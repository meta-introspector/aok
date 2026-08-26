# aok — Project Management

This directory tracks projects that publish arguments to the aok system.

## Structure

```
projects/
  <project-name>/
    PROJECT.md       — Project description, goals, status
    arguments.json   — List of argument UUIDs for this project
    milestones/      — Milestone definitions (optional)
    tasks/           — Task tracking (optional)
```

## Active Projects

| Project | Description | Arguments | Status |
|---------|-------------|-----------|--------|
| dasl | DASL IPLD fuzz testing | — | active |
| zkpop | Zero-knowledge proofs of possession | 27 | active |
| monster | Monster group / CFT / orbifold | — | active |
| lean4 | Lean4 formalization (GOAP, 2-category) | — | active |
| dotagents | Multi-agent configuration framework | — | active |

## Publishing Workflow

1. Generate a PDF (e.g. from Lean4 proof, LaTeX, or kami skill)
2. Publish to aok:
   ```bash
   python3 aok-publish.py path/to/paper.pdf --project dasl --title "Title" --tags fuzz,cbor,proof
   ```
3. The script creates a UUID directory, copies the PDF, updates manifest.json, commits and pushes

## Scanning Existing Arguments

To rebuild the manifest from existing UUID directories:
```bash
python3 aok-scan.py --index-md
```

## Automation

The publishing pipeline can be integrated with:
- Lean4 `lake build` → PDF generation via kami
- CI/CD pipelines that produce proof artifacts
- Agent task completion (dotagents tasks → aok arguments)
