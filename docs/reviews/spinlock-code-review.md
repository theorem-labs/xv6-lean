# Independent spinlock code-resource review

Codex independently reviewed the root-authored frozen `SpinlockCodeDefs.lean`
and `SpinlockCodeProofs.lean`, including the precise `EventWP.RamAccess`
contract, native list deletion/reassembly, existing fractional sharing and
pristine-timestamp update lemmas. No correction was required.

Each instruction resource pairs the actual four-byte image word at its
numeric instruction address with timestamp-zero pristine ownership. The source
pristine payload is exactly `RiscvPtsto.v:1505–1513`:
discarded `(0, ts_pay_none)` ownership, which is persistent. The source pin is
arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This module is concrete
integration glue over those source-backed primitives, rather than a claim to
port the complete source text/kernel-map context interface.

`codeAccess` uses the selected `Fin 17` value's actual position in
`List.finRange 17`. It extracts that indexed resource with native
`bigSepL_delete_cond`, retains every other conjunct and supplies the exact
reassembly wand demanded by `RamAccess`. Width/address/value equalities come
from `SpinlockFetch.CodeRead`; the bit-vector width conversion is checked.
No index, unselected instruction, or mutable data resource is discarded.
This adapter supplies resources for the allowed fetch result; it does not
change the actual event's metadata or the native rule's guards.

`instruction_halves` splits only physical byte fractions through native
`Fractional`, using `q.half + q.half = q`, and duplicates only the persistent
pristine component. Repeating this three times supplies eight positive
one-eighth shares of all seventeen instructions. The set conversion uses
exactly `GlobalRegisters.allCPUs = Fin 8`, with native duplicate-free list/set
separating-operation correspondence. It does not omit parked CPUs or create
additional full byte ownership.

`mint_instruction` reversibly separates a full timestamp-zero stored window,
then intentionally converts its full zero timestamps to persistent discarded
pristine fragments using the proved native ghost-map update. The byte
fraction remains full. `mint` maps the boot descriptor `List.ofFn` to the
same seventeen-index order and sequences those basic updates; `mint_shared`
then performs the exact eight-way sharing. The lock, counter and residual
heap maps are not inputs to this conversion and remain frameable. No new
authority, camera, name or invariant world is allocated. This irreversible
conversion is appropriate only for the selected immutable instruction cells;
it is not a writable-memory ownership theorem.

Independent validation: `python3 tools/lake.py build MachCSL.Logic.SpinlockCodeProofs`
passed all 472 dependency jobs. A fresh physical-origin audit checked all
13 declarations in the two modules and traversed their type, proof-body and
inductive-constructor dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` occur; no unsafe/partial logical dependency was found and zero
declarations were excluded. The only replayed warning concerned an existing
unused CPU binder in `JalBootResourcesShare`, not proof validity.
Driver/log: `/tmp/xv6-lean-research/SpinlockCodeIndependentAudit.lean` and
`/tmp/xv6-lean-research/spinlock-code-independent-audit.log`.

This reviewer authored the separately reviewed concrete boot extraction and
some imported memory primitives; the two code-sharing modules reviewed here
were root-authored. The result supplies code resources and their fetch
accessor. It does not by itself assemble per-hart loop WPs, preserve a concrete
control annotation, prove operational lock exclusion or close adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
