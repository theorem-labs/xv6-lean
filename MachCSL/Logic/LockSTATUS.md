# Native lock product camera and registry

Frozen native camera slice for `Xv6Cameras.v:101–112` and
`WpLock.v:88–110,215–243,312–331` at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`LockDefs` uses the exact product of native `ExclAuth` cameras over discrete
`Option (CPU × Bool)` and discrete `Nat`. `CPU` is the actual machine's
`Fin 8` carrier. The second component records the acquisition position.
`authAt` and `fragAt` own the product authorities and fragments at one ghost
name; `auth` and `frag` existentially hide the position exactly as in the
source. No position is dropped from the resource. `Capacity` supplies the
camera independently of runtime ghost names.

`LockProofs` proves combined validity, agreement on both fields, authority
and fragment exclusion, timelessness, and native authority/fragment
split and recombination. These two roles are exclusive `ExclAuth` halves,
not fractional `DFrac` shares. The frame-preserving native update changes
both components when matching authority and fragment are available. The
hidden-position update keeps their agreed position. Acquisition, setting
and clearing the CPU-field marker, and release are specializations of that
camera update. Fresh allocation returns both matching roles. `LockSpec`
is instantiated entirely by these proofs.

These operations are the algebra used by the holder protocol. They do not
establish an AMO step, a `ctx_floor` receipt, a word-value pin, `locked`,
`locked_pre`, or the spinlock invariant. Those source dependencies remain
to be ported before a lock instruction specification can use this camera.

`LockLink` extends the existing `FsLink.registry` with this actual product
at slot **24**. `FsTopLink` then installs the exact arbitrary-node native
map camera at slot **25**. Both links retain explicit capacities for every
existing component: ledger, heap, era, power and observations, machine
interpretation, invariants, UART ghost resources, and link tokens.
`nativeInvariant` constructs the actual `InvGS` from the preserved
invariant slots. Preservation theorems cover all earlier indices and all
indices above the newly assigned slot; concrete slot and shared-capacity
identities are checked by reflexivity. Existing registry files were not
changed.

Source `lockG` additionally contains the distinct sleeplock camera
`ExclAuth (Discrete Qp) × Auth (Option UFrac)`. It is **not implemented or
registered here**. Slot **26** is only proposed for that future camera;
there is no placeholder camera or claimed full source `lockG` instance.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsTopLink` passes
399 jobs. `LockProofs`, `LockLink`, and `FsTopLink` each elaborate in about
one second. A fresh physical-origin audit of all **194 declarations** in
`LockDefs`, `LockSpec`, `LockProofs`, `LockLink`, and `FsTopLink` checks their
full transitive types, bodies, and referenced constructor fields. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. No unsafe/partial
semantic dependency and zero excluded declarations. The audit source is
`/tmp/xv6-lean-research/LockOwnerAudit.lean` in the working environment.
No `sorry`, custom axioms, `native_decide`, or `bv_decide` are used.
Independent root and peer reviews passed; see
`docs/reviews/lock-camera-review.md` and `lock-camera-peer-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
