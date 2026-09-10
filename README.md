# xv6-lean

A Lean port in progress of [MachCSL and the xv6 verification](https://arxiv.org/abs/2609.04043v1)
by M. Frans Kaashoek and Nickolai Zeldovich. The goal is the complete supporting
proof development and closed whole-system theorems over the actual xv6 kernel and
disk images.

**The full port is not complete.** Current work includes native Iris integration,
production TSO memory definitions and foundational proofs, exact paper image
imports, kernel-checked ELF structure facts, and an event-preserving Lean Sail interface. There is no Lean theorem yet
proving xv6 safety or filesystem crash consistency.

The baseline is the authors' [`arxiv-v1` snapshot](https://github.com/mit-pdos/xv6iris/tree/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476).
It is pinned in [upstream.lock.json](upstream.lock.json), alongside the matching
xv6 and Sail revisions. Newer upstream changes are tracked separately.

## Build and audit

Install [elan](https://github.com/leanprover/elan) and put its bin directory on PATH.
The repository pins Lean 4.32.2 and its Iris dependencies.

```sh
python3 tools/lake.py build
python3 tools/lake.py env lean Audit.lean
python3 tools/lake.py env python3 tests/test_audit.py
python3 tools/lake.py env lean tests/Images.lean
python3 -m unittest discover -s tests -p 'test_*.py'
```

`tools/lake.py` limits threads for Lake and Lean without editing your installed
toolchain or dependency sources. Set `XV6_LEAN_THREADS` to change its default of 2.
Ordinary `lake build` also works on hosts with sufficient thread capacity.

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound` for
logical dependencies and checks Iris's generic adequacy. It also inspects project
statement and implementation dependencies for unreviewed computational hooks,
with explicit pinned-library boundaries. Its closed-system root manifest is
currently empty. Semantic correspondence, theorem coverage and non-vacuity
remain separate integration obligations.

To reproduce the paper's reference inventory and imported images:

```sh
python3 tools/upstream.py xv6iris
python3 tools/inventory.py .upstream/xv6iris --check
python3 tools/images.py .upstream/xv6iris --check
```

These scripts reject the wrong reference commit and unexpected image hashes.
The generators are untrusted tooling: checked byte decoding, ELF loading and
filesystem initialization are required before the whole-system theorem closes.

## Project map

- [Plan](docs/PLAN.md): full scope, architecture and proof gates.
- [Status](docs/STATUS.md): completed work and remaining obligations.
- [Exact theorem targets](docs/THEOREM_TARGETS.md): source statements and completion contract.
- [Conventions](docs/CONVENTIONS.md): explicit Iris slots and specification interfaces.
- [Reviews](docs/reviews/): independent artifact, logic and design audits.
- [Source inventory](docs/upstream/inventory.json): all reference Rocq files;
  an inventory entry is not a completed Lean proof.
- `MachCSL/`: logic and machine-model foundations.
- `Xv6/`: concrete images and, eventually, kernel specifications/proofs/linking.
- [Agent instructions](AGENTS.md): shared contracts and review discipline from
  the paper's multi-agent methodology.

The imported kernel and filesystem image contain upstream xv6 software under its
[preserved MIT license](LICENSES/xv6-riscv.txt). The upstream xv6iris artifact has
no repository license file; this project does not assign it a new license.
See source references in each port and generated file.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
