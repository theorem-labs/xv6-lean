#!/usr/bin/env python3
"""Check that the compiled audit rejects unused axioms even outside project namespaces.
Run in `lake env` after building. Fixtures live in a temporary directory only.
"""
import os
from pathlib import Path
import subprocess
import shutil
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="xv6-audit-") as directory:
        tmp = Path(directory)
        built = ROOT / ".lake/build/lib/lean"
        for entry in built.iterdir():
            if entry.name == "MachCSL" or entry.name.startswith("MachCSL."):
                if entry.is_dir():
                    shutil.copytree(entry, tmp / entry.name)
                else:
                    shutil.copy2(entry, tmp / entry.name)
        fixture = tmp / "MachCSL/AuditFixture.lean"
        fixture.write_text("namespace OutsideProjectNamespace\naxiom forbidden : False\nend OutsideProjectNamespace\n")
        env = os.environ.copy()
        env["LEAN_PATH"] = str(tmp) + os.pathsep + env.get("LEAN_PATH", "")
        subprocess.run(["lean", "-j2", "-o", "MachCSL/AuditFixture.olean",
                        "MachCSL/AuditFixture.lean"], cwd=tmp, env=env, check=True)
        audit = tmp / "AuditFixtureRunner.lean"
        audit.write_text("import MachCSL.AuditFixture\n" + (ROOT / "Audit.lean").read_text())
        result = subprocess.run(["lean", "-j2", str(audit)], cwd=tmp, env=env,
                                capture_output=True, text=True)
        if result.returncode == 0 or "unapproved axiom OutsideProjectNamespace.forbidden" not in result.stdout + result.stderr:
            raise SystemExit("negative axiom audit did not reject the fixture as expected:\n" + result.stdout + result.stderr)
        print("Compiled axiom audit rejects an unused, differently-namespaced project axiom")


if __name__ == "__main__":
    main()
