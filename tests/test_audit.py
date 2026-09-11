#!/usr/bin/env python3
"""Compiled positive/negative audit fixtures; run in `lake env` after building.

Only temporary package overlays are changed. Each runner starts a fresh Lean
process, so no fixture declarations or attributes leak into another test.
"""
import os
from pathlib import Path
import subprocess
import shutil
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def compile_lean(path, cwd, env, output=None):
    args = ["lean", "-j2"]
    if output is not None:
        args += ["-o", str(output)]
    return subprocess.run(args + [str(path)], cwd=cwd, env=env,
                          # Full graph audits now traverse over 40,000 declarations per fixture.
                          capture_output=True, text=True, timeout=180)


def must_compile(path, cwd, env, output):
    result = compile_lean(path, cwd, env, output)
    if result.returncode:
        raise SystemExit("fixture did not compile:\n" + result.stdout + result.stderr)


def main():
    fixtures = [
        ("axiom_outside_namespace", "namespace OutsideProjectNamespace\naxiom forbidden : False\nend OutsideProjectNamespace\n",
         "unapproved axiom OutsideProjectNamespace.forbidden"),
        ("private_axiom", "private axiom privateForbidden : False\n", "unapproved axiom"),
        ("unsafe", "unsafe def unsafeData : Nat := 0\n", "unreviewed unsafe declaration"),
        ("partial", "partial def diverge (n : Nat) : Nat := diverge n\n", "unreviewed"),
        ("implemented_by", "def alternate : Nat := 1\n@[implemented_by alternate] def selected : Nat := 0\n",
         "unreviewed implemented_by declaration selected"),
        ("extern", '@[extern "xv6_audit_fixture_extern"] def externalData : Nat := 0\n',
         "unreviewed extern declaration externalData"),
        ("opaque_data", "opaque opaqueData : Nat := 0\n", "unreviewed opaque data declaration opaqueData"),
        ("positive", "opaque proofOpacity : True := True.intro\n"
         "def totalRecursion : Nat → Nat | 0 => 0 | n + 1 => totalRecursion n\n"
         "theorem ordinaryProof : (#[1, 2, 3] : Array Nat).size = 3 := rfl\n", None),
        ("external_body", "import Foreign.Hooks\ndef useForeign : Nat := Iris.unreviewedHook\n",
         "unreviewed opaque data declaration Iris.unreviewedHook"),
        ("external_statement", "import Foreign.Hooks\n"
         "theorem statementHook (h : Iris.unreviewedHook = 0) : Iris.unreviewedHook = 0 := h\n",
         "unreviewed opaque data declaration Iris.unreviewedHook"),
        ("missing_closed_root", "theorem sample : True := True.intro\n", "missing closed root Missing.finalTheorem"),
        ("runtime_initial_snapshot", "import Xv6.Fs.NativeSnapshotImage\n"
         "open Iris Iris.BI MachCSL.Logic\n"
         "theorem runtimeMint (frame : IProp FsTop.registry) :\n"
         "    iprop(frame ⊢ |==> (FsDurSnapshot.registryPdur Xv6.Fs.Image.NativeSnapshot.committed ∗ frame)) :=\n"
         "  Xv6.Fs.Image.NativeSnapshot.allocate_durable frame\n",
         "Unclassified initial snapshot allocation caller runtimeMint"),
    ]
    with tempfile.TemporaryDirectory(prefix="xv6-audit-") as directory:
        tmp = Path(directory)
        # Both imported root anchors identify this overlay as the project package.
        built = ROOT / ".lake/build/lib/lean"
        project = tmp / "project"
        project.mkdir()
        for entry in built.iterdir():
            if entry.name == "MachCSL" or entry.name.startswith("MachCSL."):
                if entry.is_dir():
                    shutil.copytree(entry, project / entry.name)
                else:
                    shutil.copy2(entry, project / entry.name)
        foreign = tmp / "foreign"
        (foreign / "Foreign").mkdir(parents=True)
        hook = foreign / "Foreign/Hooks.lean"
        # A dependency declaration cannot gain review by using Iris's namespace.
        hook.write_text("namespace Iris\nopaque unreviewedHook : Nat := 0\nend Iris\n")
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(project), str(foreign), env.get("LEAN_PATH", "")])
        must_compile(Path("Foreign/Hooks.lean"), foreign, env, Path("Foreign/Hooks.olean"))
        (project / "Unexpected").mkdir()
        for name, source, expected in fixtures:
            # This module deliberately has neither a MachCSL nor an Xv6 prefix.
            fixture = project / "Unexpected/AuditFixture.lean"
            fixture.write_text(source)
            must_compile(Path("Unexpected/AuditFixture.lean"), project, env,
                         Path("Unexpected/AuditFixture.olean"))
            body = (ROOT / "Audit.lean").read_text()
            if name == "missing_closed_root":
                marker = "def closedRoots : Array Name := #[]"
                if marker not in body:
                    raise SystemExit("update closed-root fixture for the explicit manifest declaration")
                body = body.replace(marker, "def closedRoots : Array Name := #[`Missing.finalTheorem]", 1)
            audit = project / "AuditFixtureRunner.lean"
            audit.write_text("import Unexpected.AuditFixture\n" + body)
            result = compile_lean(audit, project, env)
            output = result.stdout + result.stderr
            if expected is None:
                if result.returncode or "closed whole-system root manifest is empty" not in output:
                    raise SystemExit(f"positive fixture {name} failed:\n{output}")
            elif result.returncode == 0 or expected not in output:
                raise SystemExit(f"negative fixture {name} did not reject as expected ({expected}):\n{output}")
            print(f"audit fixture {name}: passed")
        print(f"{len(fixtures)} compiled audit fixtures passed; no closed whole-system root is claimed")


if __name__ == "__main__":
    main()
