# Lean CSL foundations audit

Read the full 47-page paper before this audit. The target is the paper's actual sub-instruction, multicore, TSO, interrupt, DMA and persistent-disk power-cycle semantics, with closed adequacy. A Prop alias, WP axiom, assume-correct instruction interpreter, or reset-to-fs.img crash model does not meet that target.

## Recommendation

Use the native [leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean/tree/728a17140939e49af9236f7cb0d037da9ec52435) at exact commit **728a17140939e49af9236f7cb0d037da9ec52435**, with Lake subdirectory `Iris`, and **leanprover/lean4:v4.32.2**. Its Lean compiler commit is `f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Do not spend the initial effort reinventing Iris or creating an axiomatized interface to it.

The checked-in dependency manifest pins batteries to `023ce7d62a0531e22a5331e20b587817a80d49ff` and Qq to `38d591e778f100aec9762bb582f9c7f55f50e9dc`. The Iris package does not require Mathlib; the separate IrisMath package is optional. Its Rocq correspondence tracker is pinned at Iris-Rocq `a5375188ffce54f942a852ceee70704cb2ae8177`, so do not assume lemma identifiers exactly match xv6iris's own Iris revision.

## Implemented foundations (inspected source, not just README)

| Foundation | Concrete implementation |
| --- | --- |
| OFE/COFE, nonexpansiveness, contractiveness, guarded fixpoint | `Iris/Algebra/OFE.lean`, `COFESolver.lean` |
| Domain equation solving | `COFESolver.lean` builds the approximation tower and fold/unfold isomorphism; `IProp.lean` defines `IPre := OFunctor.Fix (UPredOF (IResF GF))` |
| CMRA/UCMRA and resource algebra laws | `Algebra/CMRA.lean`, authoritative, agreement, exclusive, fractional, discarded-fraction, sets/multisets, maps, lists, monotone-list/nat, local updates |
| Real step-indexed predicates | `Algebra/UPred.lean`: `holds : (n : Nat) → ValidAt M n → Prop` with resource monotonicity and step-index downclosure, plus COFE |
| Recursive higher-order Iris propositions | `Algebra/IProp.lean`: `IProp GF := UPred (IResUR GF)` over recursively constructed resource functors, with proved fold/unfold |
| Base BI laws, ownership, later/Löb, basic updates and soundness | `Instances/UPred/Instance.lean`, `Instances/IProp/Instance.lean`, BI modules |
| Invariants, world satisfaction, masks | `Instances/Lib/WSat.lean`, `Invariants.lean`; allocation/open/close are proved |
| Fancy updates and soundness | `Instances/Lib/FUpd.lean`: model definition, update laws, `fupd_finally_soundness`, `fupd_soundness`, `step_fupdN_soundness` |
| Cancellable invariants | `Instances/Lib/CInvariants.lean`; actual exclusive and fractional ghost resources |
| Generic operational language and threaded step relations | `ProgramLogic/Language.lean`, `ThreadPool.lean` |
| Weakest precondition | `ProgramLogic/WeakestPre.lean`: guarded fixpoint of `wp.pre` over actual primitive steps, state interpretation, fork postconditions and laters |
| Adequacy and invariance | `ProgramLogic/Adequacy.lean`: `wp_strong_adequacy_gen` (line 174), `wp_adequacy_gen` (302), `wp_invariance_gen` (341) |
| Monotone/view-indexed predicates | `BI/MonPred.lean`, `ProofMode/MonPred.lean`; useful machinery but does not supply MachCSL's specific TSO/suspended-view theory |
| Concrete concurrent examples | HeapLang semantics, primitive laws, spin/ticket/rw locks, fork/join and examples |

The generic strong adequacy theorem allocates invariants and accepts initial state interpretation and WPs, then derives a pure property from an actual finite thread-pool execution. This is precisely the correct kind of base for MachCSL. It does not already prove the new machine language is adequate: the Sail/system language instance and its state interpretation must still be ported and proved.

## Axioms/sorries audit

A source search over Iris and IrisMath found **no explicit axiom declarations and no active sorry/admit**. The apparent `sorry` in `BI/Sbi.lean:644` is inside a block-commented optional TODO theorem; three `sorry` occurrences in `Std/PartialMap.lean` are also comments. The unfinished Sbi theorem concerns a Lean-specific `sForall` helper, not the actual soundness chain. Proof-mode metaprogramming uses unsafe initialization/deserialization in `SynthInstanceAttr`; this supplies proof-producing tactics, not a logical axiom. No native_decide/ofReduceBool/skipKernelTC occurrences were found in Iris source. Ordinary Lean logical axioms (`propext`, `Classical.choice`, `Quot.sound`) must be reported honestly by a compiled axiom audit.

Build/compiled-axiom verification is in progress; append results below. Initial build failed because each Lean process defaulted to 144 threads on this host, causing `failed to create thread`. This is an environment resource issue, not a theorem error. Temporary `weakLeanArgs = ["-j2"]` in the three local package configs constrains compiler threads without changing logical source.

## Mapping xv6iris imports

I extracted all `From iris...` import families from the artifact's `iris/*.v`. Every required family has an existing native module: agree/auth/csum/dfrac/excl/frac/functions/gmap/gmultiset/gset/local_updates/numbers/ofe/ufrac/updates; dfrac_agree/excl_auth/mono_list; iprop/own; cancelable_invariants/fancy_updates/gen_heap/ghost_map/ghost_var/invariants/mono_nat/saved_prop; BI/fractional; program_logic adequacy/language/lifting/weakestpre; proofmode. `gmap` corresponds to Lean GenMap/Heap/partial map libraries and is not a textual rename; universe, OFE equality and functor plumbing require deliberate porting. Iris has `@[rocq_alias]` metadata and a porting report generator to resolve lemma correspondence.

No missing foundational feature has been identified that justifies beginning with a custom lean CSL. Missing small lemmas and proofmode conveniences can be contributed upstream or to an exact-pinned fork as encountered.

## What is genuinely still missing for this project

1. Exact artifact Sail semantics and event-level Lean interface, including all register reads/writes, exclusive memory operations, external nondeterminism and register initialization. A state monad that collapses a CPU cycle into one atomic state transition is insufficient.
2. The artifact system's TSO write-history, read visibility, exclusive RMW, MMIO, device DMA, IRQ and era/power operational rules, with persistent disk retained on reboot.
3. A real Iris `Language` instance for those events and all ghost-state/state-interpretation allocation and preservation proofs. Generic Iris adequacy is available, but MachCSL adequacy is substantial new work.
4. MachCSL-specific resource algebras, physical/register points-to, TSO stability/views/suspended views, page-table/TLB invariants, interrupt and migration capability, and their WP rules.
5. Artifact-level instruction/cycle rules, ABI continuation specifications, all xv6 Spec/Code/Proof/Link modules, boot initialization and disk-image consistency, and pure top-level safety/filesystem adequacy.
6. Semantic and trust-boundary validation: exact image bytes and Sail version/config, theorem-closure and axiom checks, source correspondence, conformance traces. Native kernel-checked proofs do not by themselves certify the faithful statement.

## Rocq import alternative

The existing `/data/jason/rocq-lean-import` is the **opposite direction**: it imports exported Lean proof objects into Rocq (`Lean Import`), translating Lean Prop to Rocq SProp. Its README labels it experimental alpha and discusses universe/conversion-checking difficulties. It is not an available route for bringing the 1.3-million-line xv6iris Rocq development into Lean. Building a trustworthy Rocq-to-Lean proof translator would itself be a large research/engineering project, with coinduction, cumulativity, dependent elimination and definitional-equality issues. Given the unusually complete native Iris foundation now available, that approach is less direct and should not be the critical path. It may be explored separately as translation tooling, but no imported theorem may become an unchecked axiom.

## Work allocation implications from paper section 7

Freeze and review the state/resource and abstraction interfaces before dispatching per-function proofs. Isolate Spec/Code/Proof/Link modules and give proof workers bounded targets without authority to weaken their contracts. Start with complete small semantic-to-Iris-to-pure-adequacy slices to detect incompatible invariant ownership before expanding. Track unclosed obligations prominently; theorem closure, live disk state across reboot, and non-vacuity are integration criteria rather than end-stage audits. Record failed abstraction designs and reset stalled agents from shared state. A single tagged dependency implementation and several independent reviewers are preferable to competing foundational CSL rewrites.

## Completed build and compiled axiom results

The exact pinned Lean 4.32.2 build of `Iris.ProgramLogic.Adequacy`, `Iris.Instances.Lib.CInvariants`, and `Iris.BI.MonPred` succeeded (211 build jobs). The only local dependency changes for this experiment were the documented thread-count build arguments, not Lean source.

Compiled `#print axioms` results:

- `Iris.ProgramLogic.wp_strong_adequacy_gen`: `[propext, Classical.choice, Quot.sound]`.
- `Iris.fupd_soundness`: `[propext, Classical.choice, Quot.sound]`.
- `Iris.IProp.fold_unfold`: `[propext, Quot.sound]`.
- `Iris.CancelableInvariant.own_valid`: `[propext, Classical.choice, Quot.sound]`.

Root integration now pins this exact dependency/toolchain and has actual compiled Iris smoke proofs in `MachCSL/Logic/Foundations.lean`. They prove resource reordering, framed resource-consuming continuation application, exclusive token nonduplication, and cancellation returning the guarded invariant body. These are integration checks, explicitly not RISC-V adequacy. They compiled against the audited dependency tree; the root full build remains to be run by the coordinator after its thread-limiting setup is finalized.


*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
