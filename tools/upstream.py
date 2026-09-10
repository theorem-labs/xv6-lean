#!/usr/bin/env python3
"""Fetch immutable reference sources without adding them to the proof trust base."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def git(*args, cwd=None):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*")
    parser.add_argument("--directory", type=Path, default=ROOT / ".upstream")
    args = parser.parse_args()
    repos = json.loads((ROOT / "upstream.lock.json").read_text())["repositories"]
    names = args.names or list(repos)
    for name in names:
        if name not in repos:
            parser.error(f"unknown reference: {name}")
        spec = repos[name]
        target = args.directory.resolve() / name
        if target.exists():
            if git("status", "--porcelain", cwd=target):
                raise SystemExit(f"refusing to alter dirty reference checkout: {target}")
            actual = git("rev-parse", "HEAD", cwd=target)
            if actual != spec["revision"]:
                raise SystemExit(f"wrong revision at {target}: {actual}; expected {spec['revision']}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            git("init", str(target))
            git("remote", "add", "origin", spec["url"], cwd=target)
            git("fetch", "--depth=1", "origin", spec["revision"], cwd=target)
            git("checkout", "--detach", "FETCH_HEAD", cwd=target)
        actual = git("rev-parse", "HEAD", cwd=target)
        if actual != spec["revision"]:
            raise SystemExit(f"revision mismatch at {target}: {actual}")
        print(f"{name}: {actual} ({target})")


if __name__ == "__main__":
    main()
