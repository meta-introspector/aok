#!/usr/bin/env python3
"""aok-publish — Publish a PDF argument to the Arguments of Knowledge system.

Creates a UUID directory, places the PDF and supporting files,
updates the manifest, commits and pushes.

Usage:
    python3 aok-publish.py <pdf-path> [--title TITLE] [--project PROJECT]
                                    [--author AUTHOR] [--tags tag1,tag2]
                                    [--source-url URL] [--extra-file PATH...]
                                    [--private] [--no-push]

With --private, the argument is published to the private aok repo
(meta-introspector/aok-private) instead of the public one.

Structure created:
    <uuid>/
      code/
        paper.pdf          (or docs/ depending on --subdir)
        metadata.json       (argument metadata)
        README.md           (auto-generated from metadata)

The manifest at manifest.json is updated with the new entry.

Requires: git, python3
License: AGPL v3
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys
import uuid as uuid_module
from pathlib import Path

# Repo root is the directory containing this script
SCRIPT_DIR = Path(__file__).resolve().parent

# Private repo lives alongside the public one
PRIVATE_REPO = SCRIPT_DIR.parent / "aok-private"

# Default to public repo (this script's own directory)
REPO_ROOT = SCRIPT_DIR


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def git_cmd(*args: str, cwd: Path = REPO_ROOT) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"git error: {result.stderr}", file=sys.stderr)
        raise SystemExit(1)
    return result.stdout.strip()


def load_manifest() -> dict:
    manifest_path = REPO_ROOT / "manifest.json"
    if manifest_path.exists():
        with open(manifest_path) as f:
            return json.load(f)
    return {"version": 1, "arguments": []}


def save_manifest(manifest: dict) -> None:
    manifest_path = REPO_ROOT / "manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
        f.write("\n")


def generate_readme(meta: dict) -> str:
    lines = [
        f"# {meta['title']}",
        "",
        f"**Project:** {meta.get('project', 'general')}",
        f"**Author:** {meta.get('author', 'mike dupont')}",
        f"**Published:** {meta['published']}",
        f"**SHA-256:** `{meta['sha256']}`",
        "",
    ]
    if meta.get("tags"):
        lines.append(f"**Tags:** {', '.join(meta['tags'])}")
    if meta.get("source_url"):
        lines.append(f"**Source:** {meta['source_url']}")
    lines.extend([
        "",
        "## Files",
        "",
    ])
    for fname in meta.get("files", []):
        lines.append(f"- `{fname}`")
    lines.extend([
        "",
        "---",
        "Part of the [Arguments of Knowledge](https://github.com/meta-introspector/aok) system.",
    ])
    return "\n".join(lines) + "\n"


def publish(
    pdf_path: Path,
    title: str | None,
    project: str,
    author: str,
    tags: list[str],
    source_url: str | None,
    extra_files: list[Path],
    subdir: str,
    dry_run: bool,
    private: bool,
    no_push: bool,
) -> str:
    # Select target repo
    repo_root = PRIVATE_REPO if private else SCRIPT_DIR
    if private and not repo_root.exists():
        print(f"Error: Private repo not found at {repo_root}", file=sys.stderr)
        print("Create it with: gh repo create meta-introspector/aok-private --private", file=sys.stderr)
        raise SystemExit(1)

    repo_label = "private" if private else "public"
    print(f"Publishing to {repo_label} repo: {repo_root}")

    # Validate PDF exists
    if not pdf_path.exists():
        print(f"Error: PDF not found: {pdf_path}", file=sys.stderr)
        raise SystemExit(1)

    # Generate UUID
    arg_uuid = str(uuid_module.uuid4())
    arg_dir = repo_root / arg_uuid
    code_dir = arg_dir / "code"
    target_subdir = code_dir / subdir
    target_subdir.mkdir(parents=True, exist_ok=True)

    # Default title from filename
    if not title:
        title = pdf_path.stem.replace("-", " ").replace("_", " ").title()

    # Compute SHA-256
    sha = sha256_file(pdf_path)

    # Copy PDF
    dest_pdf = target_subdir / pdf_path.name
    if not dry_run:
        shutil.copy2(pdf_path, dest_pdf)

    # Copy extra files
    file_list = [str(dest_pdf.relative_to(arg_dir))]
    for ef in extra_files:
        if ef.exists():
            dest = target_subdir / ef.name
            if not dry_run:
                shutil.copy2(ef, dest)
            file_list.append(str(dest.relative_to(arg_dir)))

    # Create metadata
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    meta = {
        "uuid": arg_uuid,
        "title": title,
        "project": project,
        "author": author,
        "published": now,
        "sha256": sha,
        "tags": tags,
        "source_url": source_url,
        "files": file_list,
        "pdf_filename": pdf_path.name,
        "subdir": subdir,
        "private": private,
    }

    # Write metadata.json
    if not dry_run:
        with open(code_dir / "metadata.json", "w") as f:
            json.dump(meta, f, indent=2, sort_keys=True)
            f.write("\n")

        # Write README.md
        with open(arg_dir / "README.md", "w") as f:
            f.write(generate_readme(meta))

    # Update manifest
    manifest_path = repo_root / "manifest.json"
    if manifest_path.exists():
        with open(manifest_path) as f:
            manifest = json.load(f)
    else:
        manifest = {"version": 1, "arguments": []}

    manifest_entry = {
        "uuid": arg_uuid,
        "title": title,
        "project": project,
        "author": author,
        "published": now,
        "sha256": sha,
        "tags": tags,
        "files": file_list,
        "private": private,
    }
    manifest["arguments"].append(manifest_entry)
    manifest["arguments"].sort(key=lambda x: x.get("published", ""))

    if not dry_run:
        with open(manifest_path, "w") as f:
            json.dump(manifest, f, indent=2, sort_keys=True)
            f.write("\n")

    # Git operations
    if not dry_run:
        git_cmd("add", arg_uuid, cwd=repo_root)
        git_cmd("add", "manifest.json", cwd=repo_root)
        commit_msg = f"Publish: {title} ({arg_uuid[:8]})"
        git_cmd("commit", "-m", commit_msg, cwd=repo_root)

        # Push
        if not no_push:
            try:
                git_cmd("push", "origin", "main", cwd=repo_root)
                print(f"Pushed to origin/main ({repo_label})")
            except SystemExit:
                print(f"Warning: push failed, committed locally", file=sys.stderr)

    print(f"Published: {title}")
    print(f"  UUID: {arg_uuid}")
    print(f"  Repo: {repo_label}")
    print(f"  Path: {arg_dir.relative_to(repo_root)}")
    print(f"  SHA-256: {sha}")
    if dry_run:
        print("  (dry run — no files written)")

    return arg_uuid


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Publish a PDF argument to the aok system"
    )
    parser.add_argument("pdf", type=Path, help="Path to the PDF file")
    parser.add_argument("--title", type=str, default=None,
                        help="Title for the argument (default: from filename)")
    parser.add_argument("--project", type=str, default="general",
                        help="Project name (default: general)")
    parser.add_argument("--author", type=str, default="mike dupont",
                        help="Author name")
    parser.add_argument("--tags", type=str, default="",
                        help="Comma-separated tags")
    parser.add_argument("--source-url", type=str, default=None,
                        help="Source URL for the argument")
    parser.add_argument("--extra-file", action="append", type=Path,
                        dest="extra_files", default=[],
                        help="Additional files to include")
    parser.add_argument("--subdir", type=str, default="paper",
                        choices=["paper", "papers", "docs", ""],
                        help="Subdirectory under code/ (default: paper)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would happen without writing")
    parser.add_argument("--private", action="store_true",
                        help="Publish to the private aok repo instead of public")
    parser.add_argument("--no-push", action="store_true",
                        help="Commit locally without pushing to remote")

    args = parser.parse_args(argv[1:])

    tags = [t.strip() for t in args.tags.split(",") if t.strip()] if args.tags else []

    publish(
        pdf_path=args.pdf,
        title=args.title,
        project=args.project,
        author=args.author,
        tags=tags,
        source_url=args.source_url,
        extra_files=args.extra_files,
        subdir=args.subdir,
        dry_run=args.dry_run,
        private=args.private,
        no_push=args.no_push,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
