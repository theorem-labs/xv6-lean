# Shared kernel page-table invariant and event accessors

This is a source-checked design proposal. It introduces no Lean declarations
and establishes neither a translated `mycpu` WP nor a boot publication theorem.
The next implementation should preserve a shared, mutable table and prove its
accessors at individual machine events. The existing directly owned three-slot
walk is a useful prerequisite with a narrower contract.

Sources are `.upstream/xv6iris/iris/` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. I read the complete `KptPt.v`,
`PtTree.v`, `PtTreeAdue.v`, and `HartSKpt.v`, then the relevant definitions and
accessors in `PtreeType.v`, `KptGhost.v`, `KMap.v`, `KptTree.v`, `KptShare.v`,
`PageGeom.v`, `CtxValues.v`, and `KptPublish.v`. Generated execution references
are `models/riscv/LeanPaperStock/VmemPte.lean`, `Vmem.lean`, and the already
reviewed physical PTE read/write prefixes. These are source mappings, not a
formal equivalence theorem between the Rocq and Lean generated models.

## Source representation and invariant

The carrier is exactly the inert `PtreeType.v:20–30` tree:

```text
inductive Tree
  | node (base : BitVec 44)
         (entries : BitVec 9 → BitVec 64)
         (children : BitVec 9 → Option Tree)
```

There is no intrinsic well-formedness, fixed allocation layout, finite-map
default, or depth-three restriction on this type. Ownership recurses on a
separate natural depth. At depth zero it owns the page and stops, including
when the inert description has children below it. The shared Sv39 instance
uses depth two. The finite separating conjunction enumerates all 512 indices
once, in increasing order, corresponding to `seqZ 0 512`; it includes zero,
invalid, and otherwise unused slots.

`PtTree.v:90–139,459–509` supplies validity/invalidity predicates over arbitrary
raw words, a shallow three-level `maps`, and precisely three invalid-stop
alternatives in `blocks`. In particular, `blocks` does not mean every possible
way an architectural walk can fault: the source does not include a valid
nonleaf at level zero in that predicate. Port those alternatives exactly.
Native validity will state the corresponding actual register-only result for
every register file, with finite execution witnesses; the existing total
`registerRun` and its soundness theorem provide one implementation route.
This is a pure semantic predicate of the raw word, not an assumed memory or
translation result. Prove the needed raw pointer bit consequences and actual
register plans from it. Do not identify that predicate with the source
compiler's `exec` by an unchecked cast or declare a stronger footprint
predicate equivalent without proving the bridge.

The proposed native definition is explicit rather than a fuel bound chosen
by a caller:

```text
PteOutcome w answer := ∀ rs : RegisterFile, ∃ fuel : Nat,
  registerRun fuel (pte_is_invalid (flags w) (ext_bits_of_PTE w)) rs
    = some (answer, rs)
Valid w := PteOutcome w false
Invalid w := PteOutcome w true
```

For valid nonleaf words, the first plan theorem must derive
`RegisterPlan.Returns [] rs (pte_is_invalid (flags w) (ext_bits_of_PTE w)) false rs`
for arbitrary `rs`. Its proof derives the reserved-bit constraints from
`Valid w` and executes the generated eager reads universally. `Valid w`
alone does not license inventing a read-free Sail term.

`canonTree` preserves bases, child structure, and every upper-level raw word.
It applies `PteCanonical.canon` only at level-zero pages. It must preserve the
source's inert children there too. Canonical equality pins both upper words
exactly but permits all four A/D combinations of a leaf. `setLeaf` follows
the two actual children and updates the selected word; absent children make
it the identity. Required pure laws include path determinism, maps/blocks
exclusion, canonical transport in both directions, updates on the selected
VPN, preservation on other VPNs, and canonical invariance of A/D updates.

Reuse `KptLeaf.Permission` (`rx | rw`) as the exact source `kperm` carrier.
Let `Mapping` be a native lawful finite map from `BitVec 27` to
`BitVec 44 × Permission`. It must support arbitrary mappings, including
trampoline and kernel-stack nonidentity entries and multiple virtual aliases
to one physical data page. The native order/enumeration instance needs a
checked lookup correspondence. No claim requires normalizing the large
source static map.

The exact `KptTree.v:331–342` representation predicate is:

```text
TreeSpec root M t :=
  base t = root ∧ ∀ vpn,
    match M[vpn]? with
    | some (ppn, permission) =>
        ∃ p2 p1 a d, Maps t vpn p2 p1 (leafWord ppn permission a d)
    | none => Blocks t vpn
```

It includes the absent-entry direction. Ghost-map agreement alone does not
prove this predicate or connect a ghost map with physical page contents.

The source ownership tier is `KTier B | UTier ξ` (`PtTree.v:911–913`), distinct
from the supervisor `KT0 | KT1` translation tier. The kernel slot is:

```text
kernelSlot era B a dq w :=
  ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
  TsoPinnedReadWP.slot machineCapacity era a 8 dq (nthByte w) B
    (PteCanonical.slotSet w)
```

The existing generic slot omits alignment deliberately; this wrapper restores
the source `kpt_slot_pin` conjunct. Its eight existential floors and current
timestamps, `floor ≤ B`, and the exact zero/boot-author/boot-view anchor
disjunction are unchanged. No fractional timestamp is upgraded. `UTier ξ`
uses the existing `TsoContextWord.pointsto`, with its actual context ID and
`payNone` resources. Both arms can be defined without a current-hart parameter;
the shared invariant uses only `KTier B`.

Every node page also owns the persistent claim from `PtTree.v:1240–1264`:

```text
nodeClaim era b :=
  ⌜ramBase ≤ b.toNat*4096 ∧ b.toNat*4096+4096 ≤ ramEnd⌝ ∗
  ⌜PageValid (pageBase b)⌝ ∗ mapAt era (pageVpn b) b rw

pageOwn tier dq t := nodeClaim era (base t) ∗
  [∗ i in indices512] slotOwn tier (slotAddress (base t) i) dq (entries t i)

treeOwn tier depth dq t := pageOwn tier dq t ∗
  match depth with
  | 0 => emp
  | depth+1 => [∗ i in indices512]
      match children t i with | none => emp | some c => treeOwn tier depth dq c
```

`PageValid` must port `PageGeom.v:54–69`: 4096 alignment and membership in
`[KernelSyms.end_, 0x88000000)`. RAM membership is insufficient. The native
imported `end_` value and its checked symbol certificate can anchor the lower
bound; no kalloc ownership or kalloc function theorem is implied by this pure
geometry. All modular address formulas retain 44-bit PPNs and 64-bit physical
addresses. RAM/alignment and eight-byte no-wrap facts follow from owned nodes.

The shared body is exactly `KptShare.v:86–101`:

```text
body era root := ∃ t M B,
  treeOwn (KTier B) 2 (own 1) t ∗ snapshot era t ∗ bound era B ∗
  mapAuth era M ∗ ⌜TreeSpec root M t⌝
shared era N root := inv N (body era root)
```

It contains no CPU, running context, TLB register, or duplicated full slot.
Use an explicit namespace parameter, with the source `nroot .@ "kpt"` as a
named specialization. Accessors state `↑N ⊆ E`. Prove Timeless for the entire
body, including the recursively owned pages, before using immediate access.

## Ghost capacity, names, and publication

The missing capacities are the exact three source cameras, not a monotone
tree authority:

| Reserved slot | Camera | Existing era name |
| --- | --- | --- |
| 45 | native `GhostMapG (BitVec 27) (BitVec 44 × Permission)` | `kernelMap` |
| 46 | `Csum (Excl Unit) (Agree (DiscreteO Tree))` | `kernelPageTable` |
| 47 | `Csum (Excl Unit) (Agree (DiscreteO Nat))` | `kernelPageTableBound` |

The coordinator reserved 45–47 for this proposal. Slots 0–43 belong to the
current `FsCrash.registry`; slot 44 is reserved for the peer's supervisor bit
camera. Implementation must extend the actual frozen slot-44 family and prove
all older capacities unchanged. Generic proofs take supplied capacity
witnesses first, so the registry link can wait for that family. Reuse the
existing native invariant capacity, physical/TSO capacities, and mono-natural
capacity at slot 3. No new era-record fields or second log-length authority
are needed. `Iris.Algebra.Csum`, `Excl`, and `Agree` already exist; the
`IcacheTypeGhost` implementation is a relevant native one-shot example.

`KptGhost.v` requires two exclusive pending tokens and two one-time shots:

```text
unset era       := own era.kernelPageTable      (inl (Excl ()))
boundUnset era  := own era.kernelPageTableBound (inl (Excl ()))
snapshot era t  := own era.kernelPageTable (inr (agree (canonTree t)))
bound era B     := own era.kernelPageTableBound (inr (agree B)) ∗
                  Views.llb era.logLength B
```

Both shot resources are persistent. Snapshot agreement proves canonical
equality, not equality of current leaf words. Bound agreement proves equality
of bounds; its separate `llb` proves that the bound is a legal log position.
Required laws are allocation, exclusivity of pending ownership, shooting,
agreement, persistence, canonical rewriting, and projection of the `llb`.
Map authority is bare full authority; `mapAt` is a discarded persistent
fragment. Allocate/mint only through native ghost-map operations, with exact
fresh-key and frame laws. Do not assert that every map contains the static map
as part of the authority definition; the source carries persisted claims.

Publication has a concrete resource precondition:

```text
TreeSpec root M t →
treeOwn (KTier B) 2 (own 1) t -∗ mapAuth era M -∗
Views.llb era.logLength B -∗ unset era -∗ boundUnset era ={E}=∗
shared era N root ∗ snapshot era t ∗ bound era B
```

This allocates an invariant from an already owned, already pinned table. It
does not allocate physical pages, synthesize their contents, or establish a
kernel boot path. Current `Era.allocate` preserves the three template names;
it does not allocate these ghost resources. A fresh-name allocation wrapper
must expose the names and tokens explicitly, then prove the record update
preserves the other era fields. Installing that wrapper into actual kernel
initialization remains separate work.

The actual source boot pinning gate is `KptPublish.v:330–554`, especially
`kptree_publish_boot`. It converts context `payNone` cells to pins at each
byte's own timestamp, uses the running context's clean/dirty justification
to produce its boot-author or boot-view anchor, and chooses the global bound
`g.log.length`. It preserves the heap, TSO interpretation, and running context,
and returns `llb g.log.length`. It requires neither a draining fence nor a
boot-hart view at log top. Earlier commentary in that source file describes
superseded gates; `fence rw,w` does not drain in this model. Native pin-mint
and the recursive publication bridge are still missing. They must be proved
before claiming an actual boot allocation of `shared`.

Per-hart credentials reuse the existing exact definition:

```text
credentials era cpu := ∃ B, bound era B ∗
  (viewLB era.views era.logLength (hartAgent cpu) B ∨
   (⌜hartAgent cpu = 0⌝ ∗ llb era.logLength B))
```

The boot arm uses forwarding from actual recorded messages. A secondary
needs its own view receipt. Neither agreement token creates that receipt.

## Accessors at actual events

First prove slot and child accessors with reassembly wands, then the exact
read-only and leaf-update three-slot accessors from `PtTree.v`. A leaf-update
accessor must return the complete original remainder and rebuild
`treeOwn ... (setLeaf t vpn new)` from the two unchanged upper slots and the
new leaf. It must not require a global distinct-pages premise absent from
source. Full byte ownership rules out simultaneous overlapping owned table
pages; separate virtual mappings may still alias data pages. Prove any
needed disjointness from the resource, or avoid needing that lemma by using
the structural separating-conjunction accessor.

A snapshot/claim lookup gives the state-free path before execution:

```text
↑N ⊆ E → mapAt era vpn ppn permission -∗ snapshot era t0 -∗
shared era N root ={E}=∗ ∃ p2 p1 a d,
  ⌜base t0 = root ∧ Maps t0 vpn p2 p1 (leafWord ppn permission a d) ∧
    AddressOK (addr2 t0 vpn) ∧ AddressOK (addr1 p2 vpn) ∧ AddressOK (addr0 p1 vpn)⌝
```

`AddressOK` is RAM at the first and last byte plus actual eight-byte alignment.
This fact contains no current-read equality. The mapping claim is checked
against the invariant's actual map authority and `TreeSpec`.

For ordinary reads, an invariant opening proves an all-view fact from the
actual TSO interpretation, the persistent publication credential, and the
temporarily accessed pins. Reassemble and close the invariant before returning
the fact. The leaf existential belongs **inside** the quantified chosen view:

```text
∀ view, g.views cpu ≤ view → view ≤ g.log.length →
  ∃ w, ReadsBytes g.image g.log (hartAgent cpu) view address 8 w ∧
       canon w = canon reference
```

For upper slots strengthen the final equality to `w = reference`, using the
raw pointer's nonleaf proof. Do not return the current flat word at all views.
The concrete public event rule takes `shared`, `snapshot`, `bound`,
`bootCredential`, the generation certificate, and the reservation fragment,
and returns the same client resources, an actual chosen-view receipt, and
the canon/equality fact to a guarded continuation of
`k (.Ok (w, none))`. Its request is the complete `ReadRequest 8`, with exact
RAM/nonexclusive guards and path-address equality. Native
`MemoryReadWP.plainPremise` is an internal proof obligation discharged by this
opening; it is not an extra public hypothesis.

For exclusive reads, open at the actual unblocked read event, after the native
rule has advanced the view to the actual log top. Obtain a current physical
leaf `q` from the full heap and slot, prove its canonical relationship, and
close the invariant. Restore the **same** `readBundle` and advanced TSO
interpretation. The native rule supplies
`resvFrag (some (snapshot address 8 q))` and the actual view receipt to the
guarded continuation. No boot credential is needed for the flat read. A
different hart can already have changed A/D since the ordinary read; `q`
is existential at this opening. This discharges `exclusivePremise` using
`heap_slot_read`; the directly owned `wp_exclusive` theorem cannot be used
while retaining the invariant open through its continuation.

For conditional writes, take the actual held eight-byte snapshot, an actual
present-payload exclusive request, and a proposed new word in the same leaf
canonical class. Open **again**, at the write event. The live tree supplies
its current word `q`; the machine reservation validity/heap lookup bridge
proves `q = reserved`. The source `kpt_leaf_write_node` needs only the canonical
class and ignores this additional equality; keeping the checked equality in
the Lean proof is useful and does not assume absence of interference.

Name all eight original floors, retaining their bounds and anchors. Apply
the existing `TsoPinnedWriteWP.bundle_store` / `TsoPinnedStore.window` to
the actual bundle and log append, and restore the slot with those **same**
floors and allowed sets. `SupervisorPteAD.slot_open/slot_close` provide
the existing finite extraction machinery. Rebuild `setLeaf t vpn new`, prove
`canonTree` unchanged and `TreeSpec root M` preserved, retain mapping
authority, and close the invariant. Preserve the full heap metadata and
all other era/fixed-state resources. The native write rule then supplies
reservation `none`, an authored log-entry receipt, and the post-append view
receipt to the guarded continuation. The update is placed under the native
one-step later and exact mask restoration, following `checkedPremise`; a
fancy update is never carried across unrelated Sail events.

The final three public event contracts contain no caller-supplied read value,
successor-preservation theorem, invariant-restoration callback, or whole-walk
WP. Their callbacks are only the user's ordinary residual-program CPS
continuations. Generic internal `Spec` interfaces may separate native
implementations, but the final `Link` discharges every component contract.

## Interference, generated control flow, and composition limits

Retain the actual machine alternatives:

- Ordinary PTE reads use `Read_plain`, with arbitrary legal view advancement.
- An overlapping exclusive read stays at the same event and clears the
  current hart's old reservation. The shared invariant is restored; no
  successful snapshot or result is claimed on this arm.
- An overlapping write stays at the same event with its state and reservation
  unchanged. It does not return architectural SC failure in this model.
  Arbitrarily many such steps are permitted, using the existing guarded WP
  rules; no fairness or termination claim follows.
- A successful exclusive read takes the actual current bytes and log-top
  view. A successful conditional write appends exactly the requested bytes,
  sets the view past that append, and clears only its own reservation.
- Generation changes retain the existing dead-thread proof and exact trace
  interpretation. Device-address and malformed-wrapper alternatives remain
  in the underlying definitions; concrete geometry and prefix proofs
  discharge the relevant guards.

Compose these event rules with the frozen `SupervisorPteRead`,
`SupervisorPteWrite`, and `SupervisorPteAD` factors. The latter's public
direct-slot theorem is not itself a shared-invariant theorem. Its actual
cached-no-update, disabled-ADUE, reread-no-update, and conditional-write
branches remain distinct. An A/D value is recomputed from the exclusive
reread, not the cached PTE. The no-write refresh branch retains its actual
snapshot until a later real restart; it produces no authored-store receipt.
The actual error and `Ok false` internal-error residuals remain in the
factor equations even when the proved event contracts exclude them.

Current `Sv39Walk.Path` fixes upper words to PPN concatenated with flag 1.
The source permits arbitrary **valid** raw nonleaf words, including G and
RSW bits. A separate generalized raw-pointer plan is required, deriving
validity and exact PPN from `Maps`, retaining actual eager register reads,
and accumulating `global || G(p2) || G(p1) || G(leaf)`. Do not force G/RSW to
zero or instantiate a different pointer word. The source permission class
does fix the mapped leaf's non-A/D bits; `KptLeaf` is suitable there.

A full translated `mycpu` additionally needs the actual TLB path, not just
three reads. Port `tlb_ok_pt`, `tlb_snap_ok`, and the per-hart full SATP/TLB
residue (`KptShare.v:157–208`). TLB entries are indexed by the actual hash;
foreign entries sharing that hash are allowed and must go through actual tag
rejection. Empty, foreign-tag, hit-no-update, hit-reread-refresh, and
hit-writeback paths retain their exact TLB read/write effects and coherence.
An entry may have stale A/D bits but must retain the actual originating
`pteAddr`. The two-table `tlb_ok_pt2` SATP-switch window from `PtTree.v` remains
separate; no current-only provenance claim covers it.

The eventual virtual stack/text layer must retain each VPN's persistent
mapping claim, canonical VA and translation-tier pin, and physical byte
resource. Crossing a page boundary requires both claims and both actual
translations. The fourteen mixed-width `mycpu` fetches use their real
two-/four-byte paths, including the aligned Ziccif fast path and possible
second halfword fetch. The 34-byte physical code span and current Bare
function proof do not establish these mapping resources or a KPT boot state.

## Proposed implementation order and ownership

1. New `Xv6/Kernel/PtTree{Defs,Spec,Proofs}.lean` and narrow pure helpers:
   exact inert type, source semantic predicates, maps/blocks, depth-aware
   canonicalization, selected-leaf update, and the raw-pointer plan bridge.
   Add the small pure page-geometry definitions as a separate owned module
   if required. First contracts are `maps_across`, `canon_set_leaf`,
   `maps_set_leaf_other`, and the actual arbitrary-valid-pointer register
   plan. No cameras or shared WP claims in this checkpoint.
2. New `MachCSL/Logic/KptGhost{Defs,Spec,Proofs,Registry,Link}.lean`:
   three exact cameras, native allocation/shot/map laws, old-slot transport,
   and existing-era-name projections. No physical truth inferred from ghost
   allocation.
3. New `Xv6/Kernel/KptOwnership{Defs,Spec,Proofs,Link}.lean` and
   `KptShared{Defs,Spec,Proofs,Link}.lean`: both exact ownership tiers, all
   page/child/path accessors, publication from pinned resources, snapshot
   and claim-to-path access. No assumption that the initial machine already
   owns those resources.
4. New `Xv6/Kernel/KptEvent{Defs,Spec,Proofs,Link}.lean`, with separate pure
   helpers if needed: three concrete native event WPs, opening/reclosing at
   each actual event, followed by the shared PTE/A-D wrapper composition.
   Freeze these before generalizing the root-owned direct walk.
5. Separate approved follow-ups: context-to-pin boot publication, generalized
   shared walk and TLB hit/fill/refresh proofs, actual translation front,
   virtual resource bridges, and integration with the peer's SIE/SConf tier.

Steps 1 and 2 are now implemented in the `PtTree` and `KptGhost` prefixes;
their exact scopes, proofs and validation are recorded in
`Xv6/Kernel/PtTreeSTATUS.md` and `MachCSL/Logic/KptGhostSTATUS.md`. The later
prefixes remain proposed implementation work. The coordinator owns the direct-slot
`Sv39Walk`; the peer owns the supervisor bit/HartTp layer. No edits to those, existing pinned
modules, generated semantics, or umbrellas are required for the first slice.

Each implemented checkpoint must compile its full owned target and audit
every physical-origin declaration, including private declarations, types,
opaque bodies, and inductive constructors. Only the repository's standard
three-axiom allowance is permitted, with no unsafe/partial logical dependency.
Useful finite examples are raw pointers with G/RSW set, differing leaf A/D
values across reads, invalid absent slots, and two logical mappings to one
data PPN. They supplement the general proof; they cannot replace event
masking, native resource validity, or actual TLB branch proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
