#!/usr/bin/env python3
"""Inventory the pinned Rocq artifact. Presence in this index is NOT a Lean proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PREFIXES = ("Spec", "Code", "Proof", "Link")


def inventory(source):
    lock = json.loads((ROOT / "upstream.lock.json").read_text())
    expected = lock["repositories"]["xv6iris"]["revision"]
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    if actual != expected:
        raise ValueError(f"reference is {actual}, expected {expected}")
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=source, text=True).strip():
        raise ValueError("reference checkout must be clean")
    files = []
    families = {}
    tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.v"], cwd=source)
    for relative_path in sorted(p.decode() for p in tracked.split(b"\0") if p):
        path = source / relative_path
        relative = path.relative_to(source).as_posix()
        raw = path.read_bytes()
        text = raw.decode()
        # An inventory only: this lexical scan is not a Rocq parser or proof audit.
        declarations = re.findall(r"(?m)^\s*(?:Local |Global )?(?:Definition|Fixpoint|Inductive|Record|Theorem|Lemma|Corollary)\s+(\w+)", text)
        files.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                      "lines": len(text.splitlines()), "declarations_lexical": declarations,
                      "port_status": "not_started"})
        if path.parent.name == "iris":
            for prefix in PREFIXES:
                if path.stem.startswith(prefix) and path.stem != prefix:
                    families.setdefault(path.stem[len(prefix):], {})[prefix.lower()] = relative
                    break
    return {"schema_version": 1, "upstream_revision": actual,
            "description": "Source inventory, not proof coverage. All statuses require explicit integration updates.",
            "files": files, "function_families": dict(sorted(families.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--output", type=Path, default=ROOT / "docs/upstream/inventory.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = inventory(args.source)
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if args.output.read_text() != rendered:
            raise SystemExit("upstream inventory is stale")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(f"{len(result['files'])} Rocq files; {len(result['function_families'])} function families; no Lean proof implied")


if __name__ == "__main__":
    main()
