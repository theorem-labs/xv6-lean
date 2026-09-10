#!/usr/bin/env python3
"""Run pinned Lake with a per-repository Lean thread limit; dependencies stay pristine."""
import fcntl
import hashlib
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    lean = shutil.which("lean")
    lake = shutil.which("lake")
    if not lean or not lake:
        raise SystemExit("Put elan's bin directory on PATH before running tools/lake.py")
    env = os.environ.copy()
    # Resolve the selected toolchain before setting the per-invocation override.
    sysroot = Path(subprocess.check_output([lean, "--print-prefix"], cwd=ROOT, text=True).strip())
    threads = int(env.get("XV6_LEAN_THREADS", "2"))
    if threads < 1:
        raise SystemExit("XV6_LEAN_THREADS must be positive")
    identity = hashlib.sha256(f"{sysroot}:threads={threads}:v2".encode()).hexdigest()[:20]
    cache = ROOT / ".cache/lean-limited"
    cache.mkdir(parents=True, exist_ok=True)
    limited = cache / identity
    # Initialize once under a lock. Running builds never see a rewritten wrapper.
    with (cache / (identity + ".lock")).open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not (limited / ".ready").exists():
            if limited.exists():
                shutil.rmtree(limited)  # only our incomplete, unpublished cache
            limited.mkdir()
            for entry in sysroot.iterdir():
                if entry.name != "bin":
                    (limited / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
            (limited / "bin").mkdir()
            for entry in (sysroot / "bin").iterdir():
                if entry.name != "lean":
                    (limited / "bin" / entry.name).symlink_to(entry)
            wrapper = limited / "bin/lean"
            wrapper.write_text("#!/bin/sh\nexec " + shlex.quote(str(sysroot / "bin/lean")) +
                               f' -j{threads} "$@"\n')
            wrapper.chmod(0o755)
            (limited / ".ready").touch()
    env["LEAN_SYSROOT"] = str(limited)
    env["LAKE_OVERRIDE_LEAN"] = "true"
    result = subprocess.run([str(sysroot / "bin/lean"), f"-j{threads}", "--run",
                             str(ROOT / "tools/LakeMain.lean"),
                             *(sys.argv[1:] or ["build"])], cwd=ROOT, env=env)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
