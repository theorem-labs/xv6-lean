# Native inode claim and freeze-shelter boundary

Status: approved exact source contract, implemented in the isolated
`MachCSL.Logic.IcacheShelter` Defs/Spec/Proofs/Link modules. See its STATUS
for validation. No additional camera or registry slot was introduced.

## Existing concrete dependencies

- `IcacheTypeGhost`: the exact non-unital type one-shot and indexed
  boot/runtime regime, slot 32.
- `LogTx`: actual native Nat-to-Unit ghost-map transaction ownership,
  positive shares, optional pin, empty-authority refutation, slot 33.
- `IcacheRefLedger`: raw ClaimCell/FreezeCell, typed claim payload,
  `FreezeIndex = Bool × (Nat × Qp)`, `frz_reg`, slot 31.
- `IcacheSlotCoupling`: the already checked source `ireg_claim_ok` and
  `ireg_frz_ok` predicates, retaining raw absent/invalid cases.

Generic definitions and laws take the actual type and transaction capacities,
plus separate explicit boot and transaction-map GNames. The concrete Link
uses the capacities already exported by `LogTx.registry`; it does not
allocate names, add slots, create a new world, or fabricate an ambient full
icfg/log_names record. This naming corresponds to the source's `icfg_boot`
and `ln_tx icfg_log` projections.

## Exact definitions

Read the complete source sections `InodeRegion.v:1780–1905,2546–2630`.
The proposed definitions preserve these exact cases:

```text
cty_pin c : Option (Nat × Qp) :=
  match c with
  | Some (Excl claim) => Some claim.transactionAndShare
  | None or Some ExclBot => None

ireg_cpin txCapacity txName c :=
  LogTx.tx_pin_o txCapacity txName (cty_pin c)

ireg_fpin txCapacity txName rg :=
  LogTx.tx_pin txCapacity txName rg.transaction rg.share

ireg_fsh typeCapacity txCapacity bootName txName f :=
  match f with
  | Some (Excl Off) => True
  | Some (Excl (Pre rg)) =>
      IcacheTypeGhost.ireg_regime typeCapacity bootName rg.runtime ∗
      ireg_fpin txCapacity txName rg
  | Some (Excl (Post rg)) =>
      IcacheTypeGhost.ireg_regime typeCapacity bootName rg.runtime ∗
      ireg_fpin txCapacity txName rg
  | None or Some ExclBot =>
      IcacheTypeGhost.ireg_open typeCapacity bootName ∨
      IcacheTypeGhost.ireg_boot typeCapacity bootName

ireg_shp typeCapacity txCapacity bootName txName c f :=
  ireg_fsh typeCapacity txCapacity bootName txName f ∗
  ireg_cpin txCapacity txName c
```

The transaction ID and positive share remain fields of the claim or freeze
index; they are never existentially forgotten inside the pin. The false
regime selects the actual exclusive boot token, and true selects the actual
persistent open token. Both phases retain the same complete index. The
claim and freeze pins may coexist and refer to the same transaction at
separate positive shares, exactly as source create/iput consumers require.

Raw invalid cases matter. A malformed claim has an empty optional pin and
must be excluded by `ireg_claim_ok`; its pin alone cannot imply `c = None`.
An absent or invalid freeze still owns the source disjunction in `ireg_fsh`,
not True or False. The pure `ireg_frz_ok` excludes those cases when the
commit-time no-ops rule requires them excluded. No raw carrier is narrowed.

## Proposed source laws

Source `ireg_fpin` and `ireg_fsh`, lines 1821–1905:

- Timeless for the pin and every shelter; no universal Persistent instance.
- `ireg_fsh_off : ⊢ ireg_fsh (freezeCell off)`.
- `ireg_fsh_pre rg : regime rg.runtime -∗ fpin rg -∗ fsh (freezeCell (pre rg))`.
- `ireg_fsh_post_acc rg : fsh (freezeCell (post rg)) ⊢ regime rg.runtime ∗ fpin rg`.
  The exact transaction/share and boot/runtime index are returned.
- `ireg_fsh_no_ops f n d : ireg_frz_ok f n d →
  LogTx.auth txName empty -∗ fsh f -∗ pure (f = freezeCell off)`.
  Actual transaction authority/fragment contradiction handles pre/post;
  the existing source pure predicate handles absent/invalid cells.
- `ireg_fsh_boot_off f : fsh f -∗ ireg_boot bootName -∗
  pure (f = freezeCell off)`, with no added pure freeze-validity premise.
  Actual native one-shot exclusions handle either indexed regime and both
  disjunctive malformed cases.
- `ireg_fsh_step ph ph' :
  (ph' = off ∨ frz_reg ph' = frz_reg ph) →
  fsh (freezeCell ph) ⊢ fsh (freezeCell ph')`.
  This is the exact source implication, including its affine off-target
  branch; it does not claim to return pins discarded by that branch.
  The same-index pre/post branches carry the supplied regime and pin.

Source claim pin and paired shelter, lines 2564–2630:

- `cty_pin` exact raw extraction equations; Timeless for cpin and shp.
- `ireg_cpin_none : ⊢ cpin None`.
- `ireg_cpin_some v : tx_pin txName v.transaction v.share ⊢ cpin (Some (Excl v))`,
  with a raw-element bridge through the existing checked `LogTx.tx_pin_elem`.
- `ireg_cpin_no_ops c f d : ireg_claim_ok c f d →
  LogTx.auth txName empty -∗ cpin c -∗ pure (c = None)`.
  Its pure claim premise is retained and discharges the invalid exclusive
  cell case after native optional-pin emptiness.
- Exact `ireg_shp_intro`, `ireg_shp_split`, and `ireg_shp_none`.

The Spec should export the two commit-time no-ops rules, the boot-off rule,
the full-index phase transport, and the paired-resource decomposition. All
laws are proved generically from actual capacities before a concrete Link.
No allocation law is needed for this resource composition layer.

## Scope and next dependencies

This closes the real native claim/freeze shelter predicate and the listed
source pure/native laws. It does not establish an inode-region invariant,
open a complete `ireg_slot`, update a physical record, mint a claim/freeze
ledger column, or implement the complete log resource. Empty transaction
authority and the source pure predicates remain explicit inputs to the
no-ops rules; they are not assumed globally. The frozen LogTx component
supplies a genuine native authority, not a pure absence assertion.

The complete slot still requires its epoch receipts, escrow registry/ticket/
corpse resources, top/record arms and their invariant protocol. Existing
reference fragments can later re-identify a claim/freeze index through their
native agreement laws, but this proposal does not replace that protocol with
a claim that a matching index is always available. Source liveness-generation
updates and full fsinit/commit theorems remain separate dependent work.

## Freeze gate

Build the isolated four-module prefix. Audit every physical-origin logical
declaration and complete type, opaque-body and datatype-constructor closure;
allow only the standard three axioms and no unsafe/partial or Initial
snapshot allocation dependencies. Include checked raw absent/invalid
extraction cases, same-index phase transport and exact post-index resource
return. Freeze all new modules and STATUS for independent source review
before whole-slot integration.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
