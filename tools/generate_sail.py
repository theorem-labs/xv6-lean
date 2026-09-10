#!/usr/bin/env python3
"""Generate the exact paper Sail model with the recorded release compiler.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PROVENANCE = ROOT / "docs/upstream/sail-generation.json"
ARCHIVE_URL = "https://github.com/rems-project/sail/releases/download/0.20.2-binary/sail-Linux-x86_64.tar.gz"
ARCHIVE_SHA = "26b59bcab2d66e9f220d317dfe45f8b09170ed70e59a824553d6f525134d1ff6"
BINARY_SHA = "6e041ffae53781ebbf85d1a6eb18ad4d7734f9eae95ace0652a36ea6e9000bb9"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def distribution_digest(root):
    entries = sorted((str(path.relative_to(root)), digest(path))
                     for path in root.rglob("*") if path.is_file())
    manifest = "".join(f"{sha}  {name}\n" for name, sha in entries)
    return hashlib.sha256(manifest.encode()).hexdigest()


def checked_checkout(path, revision):
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain"], cwd=path, text=True)
    if actual != revision or dirty:
        raise SystemExit(f"Expected a clean checkout of {revision} at {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, default=ROOT / ".cache/sail-paper")
    parser.add_argument("--xv6iris", type=Path, default=ROOT / ".upstream/xv6iris")
    parser.add_argument("--model", type=Path, default=ROOT / ".upstream/sail-riscv")
    parser.add_argument("--runtime", type=Path, default=ROOT / ".upstream/lean-sail")
    parser.add_argument("--compiler-bin", type=Path, help="Existing official extracted bin directory")
    parser.add_argument("--signature-adapter", type=Path, help="Checked prototype directory containing adapter and template")
    parser.add_argument("--dry-run", action="store_true", help="Check inputs and print argv without downloading or generating")
    args = parser.parse_args()
    for key in ("work_dir", "xv6iris", "model", "runtime"):
        setattr(args, key, getattr(args, key).resolve())
    recorded = json.loads(PROVENANCE.read_text())
    lock = json.loads((ROOT / "upstream.lock.json").read_text())["repositories"]
    for name, path in (("xv6iris", args.xv6iris), ("sail-riscv", args.model), ("lean-sail", args.runtime)):
        checked_checkout(path, lock[name]["revision"])
    config = args.xv6iris / "model-xv6iris/sail-config-rv64d.json"
    modules = args.xv6iris / "model-xv6iris/sail-modules.txt"
    extras = args.model / "handwritten_support/RiscvExtras.lean"
    for path, key in ((config, "xv6iris-arxiv-v1/model-xv6iris/sail-config-rv64d.json"),
                      (modules, "xv6iris-arxiv-v1/model-xv6iris/sail-modules.txt"),
                      (extras, "sail-riscv-paper/handwritten_support/RiscvExtras.lean")):
        if digest(path) != recorded["input_files"][key]:
            raise SystemExit(f"Input hash mismatch: {path}")
    selected = [word for line in modules.read_text().splitlines()
                for word in line.split("#", 1)[0].split()]
    compiler_bin = (args.compiler_bin or args.work_dir / "compiler/sail/bin").resolve()
    argv = [str(compiler_bin / "sail"), "--strict-var", "--strict-bitvector", "--strict-exponentials",
            "--require-version", "0.20.2", "--memo-z3-path", str(args.work_dir / "memo-z3"),
            "--lean", "--lean-output-dir", str(args.work_dir), "--lean-lib-path", str(args.runtime),
            "--lean-noncomputable", "--lean-non-beq-type", "instruction",
            "--lean-non-beq-type", "ExecutionResult", "--lean-non-beq-type", "Step",
            "--lean-import-file", str(extras), "--config", str(config), "-o", "LeanPaperStock",
            *selected, "riscv.sail_project"]
    print("cwd:", args.model / "model")
    print("PATH prefix:", compiler_bin)
    print(shlex.join(argv), flush=True)
    if args.dry_run:
        if args.compiler_bin and distribution_digest(compiler_bin.parent) != recorded["compiler_distribution_tree_sha256"]:
            raise SystemExit("Compiler distribution hash mismatch")
        return
    raw = args.work_dir / "LeanPaperStock"
    if raw.exists():
        raise SystemExit(f"Refusing to overwrite generation output: {raw}; choose a fresh work directory")
    args.work_dir.mkdir(parents=True, exist_ok=True)
    if not args.compiler_bin and not (compiler_bin / "sail").exists():
        archive = args.work_dir / "sail-Linux-x86_64.tar.gz"
        if not archive.exists():
            urllib.request.urlretrieve(ARCHIVE_URL, archive)
        if digest(archive) != ARCHIVE_SHA:
            raise SystemExit("Compiler archive hash mismatch")
        with tarfile.open(archive) as source:
            source.extractall(args.work_dir / "compiler", filter="data")
    if digest(compiler_bin / "sail") != BINARY_SHA:
        raise SystemExit("Compiler binary hash mismatch")
    if distribution_digest(compiler_bin.parent) != recorded["compiler_distribution_tree_sha256"]:
        raise SystemExit("Compiler distribution hash mismatch (including bundled libraries and Z3)")
    env = os.environ.copy()
    env["PATH"] = str(compiler_bin) + os.pathsep + env.get("PATH", "")
    metadata = {"started_utc": datetime.now(timezone.utc).isoformat(), "args": argv,
                "working_directory": str(args.model / "model"), "path_prefix": str(compiler_bin),
                "compiler_source_commit": recorded["compiler_commit"], "compiler_archive_url": ARCHIVE_URL,
                "compiler_archive_sha256": ARCHIVE_SHA, "compiler_binary_sha256": BINARY_SHA,
                "compiler_distribution_tree_sha256": recorded["compiler_distribution_tree_sha256"],
                "source_revisions": {name: lock[name]["revision"] for name in ("xv6iris", "sail-riscv", "lean-sail")},
                "input_files": {str(path): digest(path) for path in (config, modules, extras)},
                "scope": "Stock generation only; signature adaptation is separate; no correspondence claim"}
    metadata_path = args.work_dir / "generation.json"
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    with (args.work_dir / "generation.log").open("w") as log:
        result = subprocess.run(argv, cwd=args.model / "model", env=env, stdout=log, stderr=log)
    metadata.update(finished_utc=datetime.now(timezone.utc).isoformat(), exit_code=result.returncode)
    if result.returncode == 0:
        metadata["raw_output_sha256"] = {str(p.relative_to(raw)): digest(p)
                                         for p in sorted(raw.rglob("*")) if p.is_file()}
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    if result.returncode:
        raise SystemExit(f"Sail failed with exit {result.returncode}; inspect {args.work_dir / 'generation.log'}")
    if args.signature_adapter:
        prototype = args.signature_adapter.resolve()
        adapter = prototype / "adapt_paper_0202_signature.py"
        template = prototype / "SpecializationV1Free.lean.in"
        if digest(adapter) != recorded["signature_adapter_sha256"] or digest(template) != recorded["prototype_template_sha256"]:
            raise SystemExit("Signature adapter/template differs from the checked checkpoint")
        subprocess.run([sys.executable, str(adapter), str(raw), str(args.work_dir / "FreeSignature"),
                        str(args.runtime)], check=True)
    print(f"Generated {len(metadata['raw_output_sha256'])} files; provenance: {metadata_path}")


if __name__ == "__main__":
    main()
