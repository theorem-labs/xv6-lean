#!/usr/bin/env python3
"""Check the staged model's complete source inventory and immutable provenance.

Hash checks are reproducibility evidence, not semantic correspondence proofs.
"""
import hashlib
import json
from pathlib import Path
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def main():
    model = ROOT / "models/riscv"
    provenance = json.loads((model / "provenance.json").read_text())
    lock = json.loads((ROOT / "upstream.lock.json").read_text())
    expected_pins = {
        "source_commit": lock["repositories"]["sail-riscv"]["revision"],
        "paper_commit": lock["repositories"]["xv6iris"]["revision"],
        "runtime_commit": lock["repositories"]["lean-sail"]["revision"],
        "compiler_source_commit": lock["sail_compiler"]["source_commit"],
    }
    for key, expected in expected_pins.items():
        if provenance.get(key) != expected:
            raise SystemExit(f"Model provenance {key} differs from upstream.lock.json")
    paths = [model / "LeanPaperStock.lean", *(model / "LeanPaperStock").rglob("*.lean")]
    actual = {str(path.relative_to(model)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in paths}
    recorded = provenance["source_files_sha256"]
    if actual.keys() != recorded.keys():
        raise SystemExit("Model source inventory differs from the generated manifest")
    for name, digest in actual.items():
        if recorded[name] != digest:
            raise SystemExit(f"Generated model file changed: {name}; regenerate through the adapters")
    modules = [name.removesuffix(".lean").replace("/", ".") for name in actual]
    if sorted(modules) != sorted(provenance["included_modules"]):
        raise SystemExit("Model module inventory differs from its source inventory")
    config = tomllib.loads((model / "lakefile.toml").read_text())
    runtimes = [item for item in config["require"] if item["name"] == "lean-sail"]
    if len(runtimes) != 1 or runtimes[0].get("rev") != expected_pins["runtime_commit"]:
        raise SystemExit("Model Lake dependency differs from its recorded runtime")
    print(f"Verified all {len(actual)} generated model modules and source/compiler/runtime pins")


if __name__ == "__main__":
    main()
