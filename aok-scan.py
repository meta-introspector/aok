#!/usr/bin/env python3
"""aok-scan — Scan existing UUID directories and build/update the manifest.

Walks all UUID directories in the aok repo, extracts metadata from PDFs
and any existing metadata.json files, and writes manifest.json.

Usage:
    python3 aok-scan.py                    # scan and update manifest
    python3 aok-scan.py --dry-run          # show what would be written
    python3 aok-scan.py --index-md         # also generate INDEX.md
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent
UUID_RE = re.compile(
    r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$",
    re.IGNORECASE,
)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def is_uuid_dir(d: Path) -> bool:
    return d.is_dir() and UUID_RE.match(d.name) is not None


def find_pdfs(d: Path) -> list[Path]:
    return sorted(d.rglob("*.pdf"))


def extract_title_from_pdf(pdf_path: Path) -> str:
    """Try to extract a title from the PDF filename."""
    return pdf_path.stem.replace("-", " ").replace("_", " ").title()


def get_git_date(d: Path) -> str:
    """Get the first commit date for a directory."""
    try:
        result = subprocess.run(
            ["git", "log", "--diff-filter=A", "--format=%aI", "--", str(d.relative_to(REPO_ROOT))],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip().split("\n")[0]
    except Exception:
        pass
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def scan_directory() -> list[dict]:
    arguments = []
    for d in sorted(REPO_ROOT.iterdir()):
        if not is_uuid_dir(d):
            continue

        # Check for existing metadata.json
        meta_path = d / "code" / "metadata.json"
        if meta_path.exists():
            with open(meta_path) as f:
                meta = json.load(f)
            arguments.append(meta)
            continue

        # Build metadata from directory contents
        pdfs = find_pdfs(d)
        if not pdfs:
            continue

        pdf = pdfs[0]  # Primary PDF
        all_files = []
        for f in sorted(d.rglob("*")):
            if f.is_file():
                all_files.append(str(f.relative_to(d)))

        arg = {
            "uuid": d.name,
            "title": extract_title_from_pdf(pdf),
            "project": classify_project(d.name, pdf.name),
            "author": "mike dupont",
            "published": get_git_date(d),
            "sha256": sha256_file(pdf),
            "tags": classify_tags(pdf.name),
            "files": all_files,
            "pdf_filename": pdf.name,
        }
        arguments.append(arg)

    arguments.sort(key=lambda x: x.get("published", ""))
    return arguments


def classify_project(uuid: str, pdf_name: str) -> str:
    n = pdf_name.lower()
    if "zkpop" in n or "zk-pop" in n or "zk" in n:
        return "zkpop"
    if "monster" in n:
        return "monster"
    if "lean" in n or "lean4" in n:
        return "lean4"
    if "solana" in n:
        return "solana"
    if "dasl" in n:
        return "dasl"
    if "aitycoon" in n:
        return "aitycoon"
    if "octra" in n:
        return "octra"
    if "mojo" in n:
        return "mojo"
    if "nodejs" in n or "node" in n:
        return "nodejs"
    if "agda" in n:
        return "agda"
    if "eliza" in n:
        return "eliza"
    if "ledger" in n:
        return "ledger"
    if "frob" in n:
        return "frob"
    if "allemanic" in n:
        return "allemanic"
    if "openpaths" in n:
        return "openpaths"
    if "piport" in n or "piagent" in n:
        return "piagent"
    if "leanmend" in n:
        return "leanmend"
    return "general"


def classify_tags(pdf_name: str) -> list[str]:
    n = pdf_name.lower()
    tags = []
    if "zkpop" in n or "zk-pop" in n:
        tags.append("zkpop")
    if "zk" in n:
        tags.append("zero-knowledge")
    if "lean" in n:
        tags.append("lean4")
    if "solana" in n:
        tags.append("solana")
    if "monster" in n:
        tags.append("monster")
    if "conformance" in n:
        tags.append("conformance")
    if "proof" in n:
        tags.append("proof")
    if "pdf" in n:
        tags.append("pdf")
    if not tags:
        tags.append("paper")
    return tags


def generate_index_md(arguments: list[dict]) -> str:
    lines = [
        "# Arguments of Knowledge — Index",
        "",
        f"Total arguments: {len(arguments)}",
        f"Last updated: {datetime.datetime.now(datetime.timezone.utc).isoformat()}",
        "",
        "## By Project",
        "",
    ]

    # Group by project
    by_project: dict[str, list[dict]] = {}
    for arg in arguments:
        proj = arg.get("project", "general")
        by_project.setdefault(proj, []).append(arg)

    for proj in sorted(by_project.keys()):
        args = by_project[proj]
        lines.append(f"### {proj} ({len(args)})")
        lines.append("")
        lines.append("| UUID | Title | Published | SHA-256 (prefix) |")
        lines.append("|------|-------|-----------|------------------|")
        for arg in args:
            uuid_short = arg["uuid"][:8]
            title = arg.get("title", "untitled")
            pub = arg.get("published", "unknown")[:10]
            sha = arg.get("sha256", "")[:12]
            lines.append(f"| `{uuid_short}` | {title} | {pub} | `{sha}` |")
        lines.append("")

    lines.extend([
        "## By Tag",
        "",
    ])
    by_tag: dict[str, list[dict]] = {}
    for arg in arguments:
        for tag in arg.get("tags", []):
            by_tag.setdefault(tag, []).append(arg)

    for tag in sorted(by_tag.keys()):
        lines.append(f"- **{tag}** ({len(by_tag[tag])})")
    lines.append("")

    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Scan aok UUID directories and build manifest"
    )
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be written")
    parser.add_argument("--index-md", action="store_true",
                        help="Also generate INDEX.md")
    args = parser.parse_args(argv[1:])

    arguments = scan_directory()

    manifest = {
        "version": 1,
        "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "total": len(arguments),
        "arguments": arguments,
    }

    if args.dry_run:
        print(json.dumps(manifest, indent=2)[:2000])
        print(f"... ({len(arguments)} arguments total)")
        return 0

    # Write manifest.json
    manifest_path = REPO_ROOT / "manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"Wrote manifest.json with {len(arguments)} arguments")

    # Generate INDEX.md
    if args.index_md:
        index_path = REPO_ROOT / "INDEX.md"
        with open(index_path, "w") as f:
            f.write(generate_index_md(arguments))
        print(f"Wrote INDEX.md")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
