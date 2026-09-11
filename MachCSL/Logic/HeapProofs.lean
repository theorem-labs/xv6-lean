import MachCSL.Logic.HeapSpec

namespace MachCSL.Logic.Heap
open MachCSL.Memory Tso Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
open Iris.Std.PartialMap Iris.Std.FiniteMap
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Exact identity of the value fragment; no resource transport or new byte slot. -/
theorem pointsto_eq_byteElem (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) :
    pointsto capacity names a dq byte = byteElem capacity.ledger names.bytes dq a byte := rfl

theorem physicalPointsto_eq (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) :
    physicalPointsto capacity names a dq byte =
      physBytePointsto capacity.ledger names.bytes a dq byte := rfl

instance pointsto_timeless names a dq byte : Timeless (pointsto capacity names a dq byte) := by
  unfold pointsto
  infer_instance

instance token_timeless names a mask : Timeless (token capacity names a mask) := by
  unfold token
  infer_instance

instance metadata_persistent {A : Type} [Pos.Countable A] names a ns (value : A) :
    Persistent (metadata capacity names a ns value) := by
  unfold metadata
  infer_instance

instance metadata_timeless {A : Type} [Pos.Countable A] names a ns (value : A) :
    Timeless (metadata capacity names a ns value) := by
  unfold metadata
  infer_instance

theorem valid (names : Names) (memory : AddressMap Byte) (a : PhysicalAddress)
    (dq : DFrac) (byte : Byte) :
    iprop(⊢ interp capacity names memory -∗ pointsto capacity names a dq byte -∗
      ⌜memory[a]? = some byte⌝) := by
  unfold interp genHeapInterp pointsto pointsTo
  iintro ⟨%m, _, Hbytes, _⟩ Hp
  letI := capacity.ledger.bytes
  iapply ghost_map_lookup $$ Hbytes Hp

theorem update (names : Names) (memory : AddressMap Byte) (a : PhysicalAddress) (old new : Byte) :
    iprop(interp capacity names memory ∗ pointsto capacity names a (.own 1) old ⊢ |==>
      (interp capacity names (insert memory a new) ∗ pointsto capacity names a (.own 1) new)) := by
  letI := capacity.native names
  iintro H
  iapply genHeap_update $$ H

theorem allocateCell (names : Names) (memory : AddressMap Byte) (a : PhysicalAddress)
    (byte : Byte) (absent : memory[a]? = none) :
    iprop(interp capacity names memory ⊢ |==>
      (interp capacity names (insert memory a byte) ∗
      pointsto capacity names a (.own 1) byte ∗ token capacity names a ⊤)) := by
  letI := capacity.native names
  exact genHeap_alloc absent

theorem token_union (names : Names) (a : PhysicalAddress) (left right : CoPset)
    (disjoint : left ## right) :
    iprop(token capacity names a (left ∪ right) ⊣⊢
      token capacity names a left ∗ token capacity names a right) := by
  letI := capacity.native names
  exact metaToken_union disjoint

theorem token_difference (names : Names) (a : PhysicalAddress) (small large : CoPset)
    (subset : small ⊆ large) :
    iprop(token capacity names a large ⊣⊢
      token capacity names a small ∗ token capacity names a (large \ small)) := by
  letI := capacity.native names
  exact metaToken_difference subset

theorem metadata_set {A : Type} [Pos.Countable A] (names : Names) (a : PhysicalAddress)
    (mask : CoPset) (ns : Namespace) (value : A) (within : (↑ns : CoPset) ⊆ mask) :
    iprop(⊢ token capacity names a mask ==∗ metadata capacity names a ns value) := by
  letI := capacity.native names
  exact meta_set value within

theorem metadata_agree {A : Type} [Pos.Countable A] (names : Names) (a : PhysicalAddress)
    (ns : Namespace) (left right : A) :
    iprop(⊢ metadata capacity names a ns left -∗ metadata capacity names a ns right -∗
      ⌜left = right⌝) := by
  letI := capacity.native names
  exact meta_agree

theorem allocate (memory : AddressMap Byte) :
    iprop(⊢ |==> ∃ names : Names, interp capacity names memory ∗ clients capacity names memory) := by
  letI := capacity.preS
  imod genHeap_init_names memory with ⟨%γbytes, %γmeta, Hheap, Hbytes, Htokens⟩
  imodintro
  iexists (Names.mk γbytes γmeta)
  unfold interp clients pointsto token
  iframe

/-- Allocate only the metadata cameras, one reservation token per present key.
No heap-value authority or physical address is allocated by this helper. -/
private theorem allocateMetadata (γbytes : GName) (memory : AddressMap Byte) :
    iprop(⊢ |==> ∃ (γmeta : GName) (indirection : AddressMap GName),
      ⌜∀ a, dom indirection a → dom memory a⌝ ∗
      metadataAuth capacity γmeta indirection ∗
      ([∗map] a ↦ _byte ∈ memory, token capacity ⟨γbytes, γmeta⟩ a ⊤)) := by
  letI := capacity.metadataMap
  induction memory using LawfulFiniteMap.induction_on with
  | hemp =>
    imod (ghost_map_alloc_empty (K := PhysicalAddress) (V := GName)) with ⟨%γmeta, Hmeta⟩
    imodintro
    iexists γmeta, (∅ : AddressMap GName)
    iframe Hmeta
    isplit
    · ipureintro
      exact fun _ h => h
    · iapply BigSepM.bigSepM_empty
      itrivial
  | hins a byte memory absent ih =>
    imod ih with ⟨%γmeta, %indirection, %domain, Hmeta, Htokens⟩
    have absentMeta : get? indirection a = none := by
      cases hm : get? indirection a with
      | none => rfl
      | some value =>
        have notPresent : ¬ dom memory a := by simp [dom, absent]
        exact False.elim (notPresent (domain a (by simp [dom, hm])))
    imod (iOwn_alloc (E := capacity.metadata) (ReservationMap.mkToken ⊤)
      ReservationMap.valid_token) with ⟨%γcell, Hcell⟩
    imod ghost_map_insert_persist a γcell absentMeta $$ Hmeta with ⟨Hmeta, #Hentry⟩
    imodintro
    iexists γmeta, (insert indirection a γcell)
    isplitr
    · ipureintro
      exact fun k hk => LawfulPartialMap.dom_insert_iff.mpr
        ((LawfulPartialMap.dom_insert_iff.mp hk).imp_right (domain k))
    iframe Hmeta
    iapply (BigSepM.bigSepM_insert (Φ := fun a _ => token capacity ⟨γbytes, γmeta⟩ a ⊤) absent)
    isplitl [Hcell]
    · unfold token metaToken
      iexists γcell
      iframe
      iexact Hentry
    · iexact Htokens

/-- Enrich an existing value authority at its existing name. Client value and
TSO fragments are framed by this update; no replacement value camera is minted. -/
theorem attachMetadata (γbytes : GName) (memory : AddressMap Byte) :
    iprop(⊢ byteAuth capacity.ledger γbytes (.own 1) memory ==∗ ∃ γmeta : GName,
      interp capacity ⟨γbytes, γmeta⟩ memory ∗
      ([∗map] a ↦ _byte ∈ memory, token capacity ⟨γbytes, γmeta⟩ a ⊤)) := by
  iintro Hbytes
  imod allocateMetadata capacity γbytes memory with ⟨%γmeta, %indirection, %domain, Hmeta, Htokens⟩
  imodintro
  iexists γmeta
  iframe Htokens
  unfold interp genHeapInterp
  iexists indirection
  iframe
  ipureintro
  exact domain

theorem heapSpec : HeapSpec capacity :=
  ⟨allocate capacity, attachMetadata capacity, valid capacity, update capacity, allocateCell capacity,
    token_union capacity, token_difference capacity, metadata_set capacity, metadata_agree capacity⟩

end MachCSL.Logic.Heap
