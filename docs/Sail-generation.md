# Reproducing the Sail generation checkpoint

The full paper configuration generated successfully with the official Sail 0.20.2
Linux x86-64 binary in 603 seconds, producing 136 files (6.7 MB). The actual
generated model import closure now builds on Lean 4.32.2 in `models/riscv`, using
the corrected free runtime and the paper's two fixed reservation predicates. This
checkpoint establishes generation and model integration; it does not
establish correspondence with the paper's Rocq semantics or xv6 correctness.

[Machine-readable provenance](upstream/sail-generation.json) retains the exact
historical arguments and paths, compiler source commit and archive digest,
configuration and module-list hashes, runtime/template pins, all raw output file
hashes, and signature-build results. The portable recipe below replaces those
historical paths with arguments. No shared opam switch is changed.
Historical generation and signature checks used runtime `4cb7fe0`; fresh commands
use the current lock (`28c729b5`, which corrects payload-free write announcements).
The final packaged model was rebuilt and checked against that corrected runtime.

## Generate the stock paper model

```sh
python3 tools/upstream.py xv6iris sail-riscv lean-sail
python3 tools/generate_sail.py --dry-run
python3 tools/generate_sail.py
```

The generator downloads the [official compiler archive](https://github.com/rems-project/sail/releases/download/0.20.2-binary/sail-Linux-x86_64.tar.gz),
verifies archive, executable, and all 212 distribution-file digests, and runs the paper's
entire selected module list with its exact configuration. `--xv6iris`, `--model`,
`--runtime`, `--work-dir`, and `--compiler-bin` accept existing isolated paths.
Source checkouts must be clean and match the lock. The default output is
`.cache/sail-paper/LeanPaperStock`; `generation.log` and `generation.json` beside
it record the result. Existing output is never overwritten. Preserve an
interrupted output separately before retrying with a fresh work directory.

The release source commit is `3b7af38d66466ecadad563158b07ce2f82fe05da`.
The archive SHA-256 is
`26b59bcab2d66e9f220d317dfe45f8b09170ed70e59a824553d6f525134d1ff6`.
The binary requires its own `bin` directory, containing Z3, at the front of
`PATH`; the script supplies it. Generation can spend several minutes in silent
transformation passes. The measured run used about 7.2 GB resident memory.

## Check the generated free-interface signature

The released generator emits an older global namespace layout. The checked
adapter lives in [theorem-labs/lean-sail](https://github.com/theorem-labs/lean-sail/tree/62afcce/prototype)
at commit `62afcce` on `free-v1-generator-prototype`. Fetch that immutable commit
into a separate clone, then run its `prototype/adapt_paper_0202_signature.py`:

```sh
python3 PATH_TO_PROTOTYPE/prototype/adapt_paper_0202_signature.py \
  .cache/sail-paper/LeanPaperStock .cache/sail-paper/FreeSignature .upstream/lean-sail
cd .cache/sail-paper/FreeSignature
lake update
LEAN_NUM_THREADS=2 lake build LeanPaperStock.Defs LeanPaperStock.Specialization
```

Alternatively, pass `--signature-adapter PATH_TO_PROTOTYPE/prototype` during
generation; the script checks the adapter/template hashes before invoking them.
The adapter checks the actual Defs digest, imports the free V1 runtime, moves
the monad aliases after the generated Arch instance, and selects the matching
specialization. It preserves raw generation output and creates a separate copy.
The 1,785-line Defs module and specialization compiled in about 21 seconds.
Checked equalities confirm the actual 64-bit address carriers, generated barrier
and access-kind types, and free monad. Representative wrapper axiom reports
contain only `propext`.

## Reproduce the full packaged model

The full adapter pipeline is recorded at
[`68fd8c8fd5fe8e31e3b11c54a0723b12fb788817`](https://github.com/theorem-labs/lean-sail/tree/68fd8c8fd5fe8e31e3b11c54a0723b12fb788817/prototype)
on the generator-prototype branch. Fetch that immutable commit into a separate
clone and use its path for `PROTOTYPE` below.
After generating raw output, run these commands with a fresh adapted/output path:

```sh
python3 PROTOTYPE/prototype/adapt_paper_0202_signature.py RAW ADAPTED RUNTIME
python3 PROTOTYPE/prototype/parameterize_paper_0202_externs.py ADAPTED
python3 PROTOTYPE/prototype/normalize_paper_0202_rvfi.py ADAPTED
python3 PROTOTYPE/prototype/bind_paper_platform.py ADAPTED
python3 PROTOTYPE/prototype/stage_paper_model.py ADAPTED PACKAGE RISCV_SOURCE COMPILER_DISTRIBUTION
```

Here `RUNTIME` is the locked lean-sail checkout, `RISCV_SOURCE` is the locked
sail-riscv checkout, and `COMPILER_DISTRIBUTION` is the extracted `sail` directory
containing `bin` and `share`. The last step stages the 87-module import closure,
preserves compiler/model license notices, removes 28 unused FakeReal imports, and
uses package name `RiscvModel` with dependency name `lean-sail` matching the root.
The historical `LeanPaperStock` module prefix is retained to avoid renaming code.
`models/riscv/provenance.json` fixes every adapter and staged source hash.

The full package builds in 99 Lake jobs. Its entry audit traverses 8,401 combined
type/body/constructor dependencies, checking 3,077 model/runtime implementations.
No unbound hook, choice primitive, FakeReal import, custom axiom, execution override,
partial/unsafe implementation, or opaque data appears in the entry cones. Only
`execute` and `try_step` retain `[Platform]`; clock/reset/initialization functions
do not require either unbound hook class. An actual JAL fixture proves its exact
four-event register trace and final next-PC, with an enforced standard-axiom
allowlist. See `models/riscv/Tests` and `validation.json` for repeatable checks.

## Remaining integration gates

The raw handwritten `RiscvExtras.lean` contains 75 custom axiom externs. They are
excluded from the signature check. The final full-model adapter implements the
paper's reachable hooks and separates its two fixed pure reservation predicates
from unused pure/effectful extern classes. The compiled entry audit rejects the
unused classes. If a future model references an unsupported effectful hook, it
must receive an explicit Empty-result stuck event and a reachability justification,
not invented input or a new theorem assumption.

The stock `FakeReal` helper uses floating-point approximations of real arithmetic;
it is excluded from this package and the audit rejects its import. Do not treat raw generation or a parameterized build as
semantic equivalence. The choice-site certificate, optional-write-payload mapping,
cycle-counter mapping, platform correspondence, and full instruction-module audit
remain separate gates. Generated instruction semantics must not silently erase
events, choose deterministic outcomes, restrict configured instructions, or admit
new assumptions.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
