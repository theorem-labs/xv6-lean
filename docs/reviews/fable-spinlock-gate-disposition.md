# Disposition of the complete spinlock review

Fable approves the supplied safety, operational annotation, and seven-write
execution proofs, and requests actual holder inhabitation before the gate is
marked closed. This is discharged by SpinlockWitnessHolder: its actual body
boundary lies on the same composable execution to the seven-write endpoint.
It obtains the annotation through annotate_run and proves Holds with the
checked physical boundary rule. No abstract holder field is manufactured.

The coordinator independently added CertifiedRun and the combined positive
execution theorem while this review was running. The separate agent review
checks both modules and all twelve logical declarations. They already connect
the same actual execution to native safety, unique schedule annotation, holder
exclusion, and final values. The final complete_gate root additionally contains the reachable holder
checkpoint and constructs CertifiedRun from that same combined schedule.
Independent peer review and full dependency audit pass all 30 declarations
in the holder/final-gate modules. The small-program gate is now closed.

The required scope lines are accepted: physical PC exclusion is at completed
instruction boundaries only; event-defined holder exclusion is primary. The
positive witness fixes the explicit platform, chooses non-ticking cycles and
minimal permitted ordinary views, has no power cycle, and leaves six CPUs
unscheduled. Unique annotation is relative to the recorded occurrence-indexed
schedule. The whole-xv6 root manifest and cross-prover correspondence remain
open. Native kernel acquire/release are not consequences of this test gate.

The supervisor substrate and native own-author stack readback are now the
kernel critical path. The exact source definitions refine two reviewer
shorthands: mycpu's false capability still contains the canonical SIE eighth
and running-context resources, although it contains no enabled handler fixpoint
or CpuOwn bundle. Its return target is ret_pc(ra), including the architectural
low-bit clearing, not arbitrary unmasked ra. The actual source MENVCFG_S enables
ADUE and STCE, with PBMTE clear. Translation must account for the pinned A/D
update path and actual TLB behavior at each permitted kernel tier.

The readback gate now has a native physical proof for every permitted view,
preserving the entire heap/TSO and context byte resources. Context stores,
stack algebra, fractional register event folding, supervisor PMP, translation,
and fetched cycles remain the next bounded proofs. LockSet/LockRank are useful
source leaves; their allocation at eight boot-era names remains separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
