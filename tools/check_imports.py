#!/usr/bin/env python3
"""Fail if a project Lean module is omitted from its audited umbrella import graph."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    files = {".".join(p.relative_to(ROOT).with_suffix("").parts): p
             for folder in ("MachCSL", "Xv6")
             for p in (ROOT / folder).rglob("*.lean")}
    files.update({name: ROOT / f"{name}.lean" for name in ("MachCSL", "Xv6")})
    seen = set()

    def visit(name):
        if name in seen or name not in files:
            return
        seen.add(name)
        for dependency in re.findall(r"(?m)^(?:public )?import\s+([\w.]+)", files[name].read_text()):
            visit(dependency)

    for root in ("MachCSL", "Xv6"):
        visit(root)
    missing = sorted(files.keys() - seen)
    if missing:
        raise SystemExit("project modules missing from audited imports: " + ", ".join(missing))
    print(f"All {len(files)} project modules reachable from audited umbrellas")


if __name__ == "__main__":
    main()
