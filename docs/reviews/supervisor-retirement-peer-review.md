# Supervisor retirement and source PC ownership review

Coordinator review: pass for all six SupervisorRetirement modules. The complete
factor was compared with generated Step.lean:406–481; try_step_factor checks
exact free-tree equality by rfl for arbitrary step number and wait flag. Every
original unsuccessful, interrupt, waiting and execution arm remains present.
The successful rule reduces only Retire_Success under actual active-hart
ownership, retaining both hart reads, PC callback read and conditional modular
counter increment. Neither post-body increment flag nor counter is reset.

The register package matches pinned MinstretInv.v:349–364 and InstrBytes.v:701:
seven full mutable cells, two discarded configuration cells, and the original
reservation fragment. Packaging via a symbolic file adds no ownership of its
other fields. Source minstret_inv is emp, not a duplicated mutable invariant.
Both optional clock choices preserve all non-clock cells; native reassembly
returns the original reservation. The actual restart rule consumes it, clears
it and guards both next-clock continuations. A pure residual is a restart node,
not a terminal value.

Setup preserves Lean's actual eager configuration read even when counting is
inhibited; correspondence with Rocq's short-circuit behavior remains open.
The any-privilege plan quantifies over the actual unowned read rather than
assuming its symbolic-file value. Native rules fold established register and
restart WPs and introduce no new camera or implementation hypothesis.

A fresh independent opaque/type/constructor audit checked all 117 logical
declarations, standard three axioms only, zero exclusions or unsafe/partial
dependencies. Evidence: supervisor-retirement-peer-audit.log under
/tmp/xv6-lean-research. This does not prove fetched instruction execution or
mycpu; those still require translation, instruction bodies and composition.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
