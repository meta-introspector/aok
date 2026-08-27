#!/usr/bin/env python3
"""aok-jacobian — Compute Jacobian distance between projects in the aok system.

Models each project as a distribution over feature space (tags, file types,
SHA-256 byte histograms, publication time). The Jacobian matrix J maps
project parameters → feature distributions. The Jacobian distance between
two projects is the Frobenius norm of the difference of their local Jacobians,
capturing how differently they deform feature space.

Feature vectors per argument:
  - Tag histogram (normalized)
  - File extension histogram
  - SHA-256 byte histogram (256 bins, normalized)
  - Publication hour (sin/cos encoded)

The project feature vector φ(p) is the mean of its arguments' feature vectors.
The Jacobian J(p) = ∂φ/∂p is estimated via finite differences: for each project,
J(p) measures how sensitive each feature is to adding/removing arguments.

For a simpler and more robust metric, we also compute:
  - Euclidean distance in feature space
  - Symmetric KL divergence between tag distributions
  - Cosine distance between SHA-256 histograms

Output:
  - Jacobian distance matrix (projects × projects)
  - Feature distance matrix
  - Tag divergence matrix
  - ASCII heatmap
  - JSON report

Usage:
    python3 aok-jacobian.py [--manifest manifest.json] [--output jacobian-report.json]
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
from collections import Counter
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parent


def load_manifest(manifest_path: Path) -> list[dict]:
    with open(manifest_path) as f:
        data = json.load(f)
    return data.get("arguments", [])


# ── Feature extraction ──────────────────────────────────────────────

ALL_TAGS = [
    "zkpop", "zero-knowledge", "pdf", "proof", "lean4",
    "monster", "conformance", "solana",
]


def tag_histogram(tags: list[str]) -> np.ndarray:
    vec = np.zeros(len(ALL_TAGS), dtype=np.float64)
    for t in tags:
        if t in ALL_TAGS:
            vec[ALL_TAGS.index(t)] = 1.0
    norm = np.linalg.norm(vec)
    return vec / norm if norm > 0 else vec


def file_ext_histogram(files: list[str]) -> np.ndarray:
    exts = ["pdf", "md", "py", "png", "tex", "json", "txt", "lean", "rs"]
    vec = np.zeros(len(exts), dtype=np.float64)
    for f in files:
        ext = f.rsplit(".", 1)[-1].lower() if "." in f else ""
        if ext in exts:
            vec[exts.index(ext)] += 1.0
    norm = np.linalg.norm(vec)
    return vec / norm if norm > 0 else vec


def sha256_histogram(sha: str) -> np.ndarray:
    """256-bin histogram of byte values in the SHA-256 hash."""
    vec = np.zeros(256, dtype=np.float64)
    for i in range(0, len(sha), 2):
        byte_val = int(sha[i:i+2], 16)
        vec[byte_val] += 1.0
    norm = np.linalg.norm(vec)
    return vec / norm if norm > 0 else vec


def time_features(published: str) -> np.ndarray:
    """Sin/cos encoded hour of publication time."""
    try:
        hour = int(published[11:13])
        minute = int(published[14:16])
        t = hour + minute / 60.0
        return np.array([math.sin(2*math.pi*t/24), math.cos(2*math.pi*t/24)])
    except (ValueError, IndexError):
        return np.array([0.0, 0.0])


def argument_features(arg: dict) -> np.ndarray:
    """Concatenate all feature vectors for a single argument."""
    return np.concatenate([
        tag_histogram(arg.get("tags", [])),
        file_ext_histogram(arg.get("files", [])),
        sha256_histogram(arg.get("sha256", "0"*64)),
        time_features(arg.get("published", "")),
    ])


# ── Project aggregation ──────────────────────────────────────────────

def project_vectors(arguments: list[dict]) -> dict[str, np.ndarray]:
    """Compute mean feature vector for each project."""
    by_project: dict[str, list[np.ndarray]] = {}
    for arg in arguments:
        proj = arg.get("project", "general")
        by_project.setdefault(proj, []).append(argument_features(arg))

    result = {}
    for proj, vecs in by_project.items():
        result[proj] = np.mean(vecs, axis=0)
    return result


def project_tag_distributions(arguments: list[dict]) -> dict[str, np.ndarray]:
    """Compute tag distribution (probability) for each project."""
    by_project: dict[str, Counter] = {}
    for arg in arguments:
        proj = arg.get("project", "general")
        tags = arg.get("tags", ["untagged"])
        by_project.setdefault(proj, Counter()).update(tags)

    result = {}
    for proj, counter in by_project.items():
        total = sum(counter.values())
        vec = np.array([counter.get(t, 0) / total for t in ALL_TAGS], dtype=np.float64)
        # Add smoothing to avoid zeros
        vec = vec + 1e-10
        vec = vec / vec.sum()
        result[proj] = vec
    return result


# ── Jacobian estimation ──────────────────────────────────────────────

def estimate_jacobian(
    project: str,
    arguments: list[dict],
    feature_dim: int,
) -> np.ndarray:
    """Estimate the Jacobian of the feature mapping for a project.

    J(p) = ∂φ/∂p ≈ (φ(p + δ) - φ(p - δ)) / (2δ)

    Here "p + δ" means adding a small perturbation to the project's
    argument set (leave-one-out cross-validation style). The Jacobian
    captures how sensitive each feature is to changes in the project.

    For a project with n arguments, we compute n leave-one-out
    perturbations and take the average gradient magnitude.
    """
    proj_args = [a for a in arguments if a.get("project", "general") == project]
    if len(proj_args) <= 1:
        # Single argument: Jacobian is identity-scaled
        return np.eye(feature_dim, dtype=np.float64) * 0.1

    # Full project feature vector
    full_vec = np.mean([argument_features(a) for a in proj_args], axis=0)

    # Leave-one-out perturbations
    gradients = []
    for i in range(len(proj_args)):
        subset = proj_args[:i] + proj_args[i+1:]
        if not subset:
            continue
        loo_vec = np.mean([argument_features(a) for a in subset], axis=0)
        grad = full_vec - loo_vec  # Direction of change
        gradients.append(grad)

    if not gradients:
        return np.eye(feature_dim, dtype=np.float64) * 0.1

    # Jacobian = average gradient direction (as diagonal matrix)
    avg_grad = np.mean(np.abs(gradients), axis=0)
    return np.diag(avg_grad)


# ── Distance metrics ─────────────────────────────────────────────────

def jacobian_distance(J1: np.ndarray, J2: np.ndarray) -> float:
    """Frobenius norm of the difference of Jacobians."""
    return float(np.linalg.norm(J1 - J2, ord="fro"))


def euclidean_distance(v1: np.ndarray, v2: np.ndarray) -> float:
    return float(np.linalg.norm(v1 - v2))


def cosine_distance(v1: np.ndarray, v2: np.ndarray) -> float:
    norm = np.linalg.norm(v1) * np.linalg.norm(v2)
    if norm == 0:
        return 1.0
    return 1.0 - float(np.dot(v1, v2) / norm)


def symmetric_kl(p: np.ndarray, q: np.ndarray) -> float:
    """Symmetric KL divergence (Jensen-Shannon-like)."""
    p = p + 1e-10
    q = q + 1e-10
    p = p / p.sum()
    q = q / q.sum()
    kl_pq = float(np.sum(p * np.log(p / q)))
    kl_qp = float(np.sum(q * np.log(q / p)))
    return (kl_pq + kl_qp) / 2.0


# ── Output ───────────────────────────────────────────────────────────

def ascii_heatmap(matrix: np.ndarray, labels: list[str]) -> str:
    """Render an ASCII heatmap of a distance matrix."""
    n = len(labels)
    max_val = matrix.max() if matrix.max() > 0 else 1.0

    # Header
    header = "         " + " ".join(f"{l[:6]:>6s}" for l in labels)

    lines = [header, "         " + "-" * (n * 7)]

    for i in range(n):
        cells = []
        for j in range(n):
            val = matrix[i, j]
            intensity = val / max_val
            if i == j:
                cell = "   --- "
            elif intensity < 0.25:
                cell = "   .   "
            elif intensity < 0.50:
                cell = "   *   "
            elif intensity < 0.75:
                cell = "   #   "
            else:
                cell = "   @   "
            cells.append(cell)
        row = f"{labels[i][:8]:>8s} |" + "".join(cells)
        lines.append(row)

    lines.append("")
    lines.append("Legend: . < 0.25  * < 0.50  # < 0.75  @ >= 0.75  --- = diagonal")
    return "\n".join(lines)


def build_report(
    projects: list[str],
    jac_dist: np.ndarray,
    feat_dist: np.ndarray,
    tag_div: np.ndarray,
    sha_dist: np.ndarray,
) -> dict:
    """Build a JSON-serializable report."""
    report = {
        "projects": projects,
        "distances": {
            "jacobian": {},
            "euclidean": {},
            "tag_divergence": {},
            "sha256_cosine": {},
        },
        "nearest_neighbors": {},
    }

    n = len(projects)
    for i in range(n):
        for j in range(i + 1, n):
            pair = f"{projects[i]} ↔ {projects[j]}"
            report["distances"]["jacobian"][pair] = round(jac_dist[i, j], 6)
            report["distances"]["euclidean"][pair] = round(feat_dist[i, j], 6)
            report["distances"]["tag_divergence"][pair] = round(tag_div[i, j], 6)
            report["distances"]["sha256_cosine"][pair] = round(sha_dist[i, j], 6)

    # Nearest neighbor for each project by Jacobian distance
    for i in range(n):
        dists = [(jac_dist[i, j], projects[j]) for j in range(n) if j != i]
        dists.sort()
        if dists:
            report["nearest_neighbors"][projects[i]] = {
                "nearest": dists[0][1],
                "distance": round(dists[0][0], 6),
                "farthest": dists[-1][1],
                "max_distance": round(dists[-1][0], 6),
            }

    return report


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Compute Jacobian distance between aok projects"
    )
    parser.add_argument("--manifest", type=Path,
                        default=REPO_ROOT / "manifest.json",
                        help="Path to manifest.json")
    parser.add_argument("--output", type=Path,
                        default=REPO_ROOT / "jacobian-report.json",
                        help="Output JSON report path")
    parser.add_argument("--private", action="store_true",
                        help="Also load private manifest if it exists")
    args = parser.parse_args(argv[1:])

    # Load arguments
    arguments = load_manifest(args.manifest)

    # Optionally merge private manifest
    if args.private:
        private_manifest = REPO_ROOT.parent / "aok-private" / "manifest.json"
        if private_manifest.exists():
            arguments.extend(load_manifest(private_manifest))
            print(f"Loaded private manifest: {len(arguments)} total arguments")

    print(f"Loaded {len(arguments)} arguments from {args.manifest}")

    # Compute project vectors
    proj_vecs = project_vectors(arguments)
    tag_dists = project_tag_distributions(arguments)
    projects = sorted(proj_vecs.keys())
    n = len(projects)
    feature_dim = len(next(iter(proj_vecs.values())))

    print(f"Projects: {projects}")
    print(f"Feature dimension: {feature_dim}")

    # Estimate Jacobians
    jacobians = {}
    for proj in projects:
        jacobians[proj] = estimate_jacobian(proj, arguments, feature_dim)

    # Compute distance matrices
    jac_dist = np.zeros((n, n))
    feat_dist = np.zeros((n, n))
    tag_div = np.zeros((n, n))
    sha_dist = np.zeros((n, n))

    # SHA-256 feature indices: after tags (len(ALL_TAGS)) and file exts (9)
    sha_start = len(ALL_TAGS) + 9
    sha_end = sha_start + 256

    for i in range(n):
        for j in range(i + 1, n):
            jac_dist[i, j] = jac_dist[j, i] = jacobian_distance(
                jacobians[projects[i]], jacobians[projects[j]]
            )
            feat_dist[i, j] = feat_dist[j, i] = euclidean_distance(
                proj_vecs[projects[i]], proj_vecs[projects[j]]
            )
            tag_div[i, j] = tag_div[j, i] = symmetric_kl(
                tag_dists[projects[i]], tag_dists[projects[j]]
            )
            sha_i = proj_vecs[projects[i]][sha_start:sha_end]
            sha_j = proj_vecs[projects[j]][sha_start:sha_end]
            sha_dist[i, j] = sha_dist[j, i] = cosine_distance(sha_i, sha_j)

    # Output
    print("\n=== Jacobian Distance Matrix ===")
    print(ascii_heatmap(jac_dist, projects))

    print("\n=== Feature Euclidean Distance ===")
    print(ascii_heatmap(feat_dist, projects))

    print("\n=== Tag Distribution Divergence (symmetric KL) ===")
    print(ascii_heatmap(tag_div, projects))

    print("\n=== SHA-256 Cosine Distance ===")
    print(ascii_heatmap(sha_dist, projects))

    # Nearest neighbors
    print("\n=== Nearest Neighbors (by Jacobian distance) ===")
    for i, proj in enumerate(projects):
        dists = [(jac_dist[i, j], projects[j]) for j in range(n) if j != i]
        dists.sort()
        if dists:
            print(f"  {proj:12s} → nearest: {dists[0][1]:12s} ({dists[0][0]:.6f})  "
                  f"farthest: {dists[-1][1]:12s} ({dists[-1][0]:.6f})")

    # Write JSON report
    report = build_report(projects, jac_dist, feat_dist, tag_div, sha_dist)
    with open(args.output, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"\nWrote {args.output}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
