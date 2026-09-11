# Inode generation type one-shot and boot-regime boundary

Status: approved source and dependency contract; implemented in the isolated
`MachCSL.Logic.IcacheTypeGhost` prefix at assigned camera slot 32. See its
STATUS file for the checked implementation and remaining integration boundary.

## Exact source and available native implementation

Pinned `Xv6Cameras.v:607–613` defines `ityR` as the non-unital camera
`csumR (exclR unitO) (agreeR (leibnizO (bv 16)))`. This is distinct from
filesystem `FsLink` types, the per-inum reference ledger, and the count and
freeze-mirror cameras. Its ghost name identifies one inode generation;
the same camera at a separate name also implements the boot-shelter token.

The proposed exact Lean carrier is:

```lean
abbrev TypeRA := Iris.Csum (Iris.Excl Unit) (Iris.Agree (Iris.DiscreteO (BitVec 16)))
abbrev TypeRF := Iris.constOF TypeRA
structure Capacity (GF : BundledGFunctors) where
  type : Iris.ElemG GF TypeRF
```

The raw carrier retains both `Csum.invalid` and `Csum.inl Excl.invalid`;
there is no replacement with a two-constructor valid-state datatype.
The native `Iris/Algebra/Csum.lean` provides the OFE/COFE, CMRA, discreteness,
left exclusivity and right core-id instances. `Excl.lean` and `Agree.lean`
provide the component cameras; `CMRA.Update.exclusive` implements firing,
and `Agree.toAgree_op_valid_iff_eq` implements type agreement. Existing
`iOwn` allocation, validity, persistence and update APIs suffice. No Iris fork,
new axiom, global authority map, or ghost-variable substitute is needed.

A repository search found no existing camera with this exact schema.
Proposal: a Link module extends the current `IcacheRefLedger.registry` at 32,
proves slots 0–31 and 33 onward unchanged, and exports explicit capacities
for the existing ledger, coupling maps, inode records and other established
consumers. No registry will be changed before approval. One slot supports
arbitrarily many names; no camera per inode or per generation is proposed.

## First native API

The following definitions are direct translations of
`IcacheRef.v:1192–1233,1256–1298`, with capacity and source ghost name explicit:

```text
ity_pending capacity g := own g (Csum.inl (Excl.excl ()))
ity_shot capacity g ty := own g (Csum.inr (Agree.toAgree ⟨ty⟩))
ireg_boot capacity bootName := ity_pending capacity bootName
ireg_open capacity bootName := ∃ ty : BitVec 16, ity_shot capacity bootName ty
ireg_regime capacity bootName rg :=
  if rg then ireg_open capacity bootName else ireg_boot capacity bootName
```

Proposed exact native laws:

- Pending and shot are Timeless; shot is Persistent. Boot is Timeless;
  open is Timeless and Persistent. Every indexed regime is Timeless, with
  persistence exported only for the true/runtime branch.
- `ity_shoot g ty : ity_pending g ⊢ |==> ity_shot g ty` for every 16-bit `ty`.
- `ity_shot_agree g ty ty' : ity_shot g ty ∗ ity_shot g ty' ⊢ ⌜ty = ty'⌝`.
- `ity_pending_excl` and `ity_pending_shot_excl` derive False from the
  respective same-name combinations, through actual camera validity.
- `ireg_boot_open_excl` and `ireg_regime_boot_excl rg` preserve the source's
  distinction between the exclusive boot branch and persistent runtime branch.
- `fs_ready_seal : ireg_boot ⊢ |==> ireg_open`, firing at the exact zero
  witness used by `FsReady.v:385–391`.
- `allocate_pending frame : frame ⊢ |==> ∃ g, ity_pending g ∗ frame`, the
  isolated native allocation used by `IcacheRef.v:1151` and `2178`.
  A same-name shoot-with-frame wrapper retains the caller's arbitrary frame.
  Allocation creates a fresh name in the existing GF; it does not construct
  a new InvGS world or recycle an existing name.
- Optional local claim-guard consequence: from the actual source slot guard
  `⌜c = none⌝ ∨ ireg_open` and `ireg_boot`, derive `c = none` while returning
  the boot token. This is only the guard's native contradiction step, not
  the invariant-opening theorem `IregLinkNz.ireg_boot_no_claim`.

The type parameter is unrestricted. In particular, there is no `ty ≠ 0`
premise on `ity_shoot` or `ity_shot`: the boot seal explicitly fires at zero.
A standalone shot does not imply the inode is allocated. Nonzero record
conditions must come from the later actual loaded inode payload. Conversely,
no assumption that pending means a zero on-disk type will be introduced.
The record's arbitrary type is attached when the fill has the record; the
one-shot algebra itself only enforces same-name agreement.

Proposed files: `IcacheTypeGhost{Defs,Spec,Proofs,Link}.lean` and STATUS,
with any additional proof file split only if required by proof size.
Definitions stay in Defs. Generic laws take explicit Capacity and GName;
the concrete Link supplies the actual assigned slot only after approval.

## Exact boot-shelter boundary

The preceding regime is a real native resource. It is not a pure flag and
cannot be replaced by a Bool assertion. `IcacheBoot.v:718–726` carries the
same supplied `ireg_boot` through inode-region construction and returns it;
it does not seal it. `FsReady.fs_ready_seal` later consumes pending and
produces the persistent open resource. No whole `fs_ready`, fsinit ordering,
or machine-call theorem is included in this first camera layer.

The full current freeze shelter in `InodeRegion.v:1821–1895` contains another
native resource which this layer does not yet supply:

```text
ireg_fpin (runtime, (transaction, share)) := tx_pin log transaction share
ireg_fsh (Some (Excl Off)) := True
ireg_fsh (Some (Excl (Pre rg))) := ireg_regime rg.1 ∗ ireg_fpin rg
ireg_fsh (Some (Excl (Post rg))) := ireg_regime rg.1 ∗ ireg_fpin rg
ireg_fsh (None or Some ExclBot) := ireg_open ∨ ireg_boot
```

The false/true regime index and the exact transaction/share pair must survive
pre-to-post and be returned to the caller. The extra transaction share cannot
be discarded or replaced by an abstract asserted oracle. Its existing-source
camera is `LogDefs.ln_tx`'s native ghost map from transaction Nat to Unit;
the exact map authority, fractional entry ownership and empty-authority
refutation must be implemented and reviewed before claiming full `ireg_fsh`
or its commit-time `ireg_fsh_no_ops` theorem. No such native transaction API
was found in the current repository. This proposal therefore establishes the
actual one-shot/regime dependency first, without defining a weakened shelter.

Similarly, `IcacheRef.live_genlo_bump:2173–2187` updates a different native
liveness map while allocating the fresh pending name. The full-share liveness
premise is essential to the generation protocol; a generic pending allocation
cannot stand in for that theorem. `IcacheEscrow.ic_payload_np:1270–1276`
places shot beside loaded payload and pending beside unloaded payload; neither
payload is available from the one-shot alone. These liveness and payload
boundaries remain explicit next native dependencies.

## Validation gate

After approval and implementation: build the isolated prefix; audit every
physical-origin logical declaration and its complete type, opaque-body and
datatype-constructor dependency cone. Permit only `propext`,
`Classical.choice`, and `Quot.sound`; reject unsafe/partial logical code and
initial-snapshot allocation dependencies. Kernel-check both zero and nonzero
firing examples, duplicate pending exclusion, pending/shot exclusion, and
same-name shot agreement. Review the direct allocation callers separately
from the live-generation and whole-boot integration obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
