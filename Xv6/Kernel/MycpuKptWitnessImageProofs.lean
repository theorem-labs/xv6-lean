import Xv6.Kernel.MycpuKptWitnessRunProofs
namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

theorem table_words (page : Fin 3) (slot : Fin 512) :
    readBytes image (BitVec.ofNat 64 (rootBase + page.val * 4096 + slot.val * 8)) 8 =
      some (tableWord page.val slot.val) := by
  apply readBytes_of_bytes
  intro j hj
  have ha : (addressAdd (BitVec.ofNat 64 (rootBase + page.val * 4096 + slot.val * 8)) j).toNat =
      rootBase + page.val * 4096 + slot.val * 8 + j := by
    simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold rootBase
    omega
  unfold image
  rw [if_pos (by unfold tableRange; rw [ha]; unfold rootBase; omega)]
  unfold tableByte
  rw [ha]
  have sub : rootBase + page.val * 4096 + slot.val * 8 + j - rootBase =
      page.val * 4096 + slot.val * 8 + j := by omega
  rw [sub]
  have hp : (page.val * 4096 + slot.val * 8 + j) / 4096 = page.val := by omega
  have hs : ((page.val * 4096 + slot.val * 8 + j) % 4096) / 8 = slot.val := by omega
  have hb : (page.val * 4096 + slot.val * 8 + j) % 8 = j := by omega
  rw [hp, hs, hb]

theorem image_outside (a : PhysicalAddress) (outside : ¬tableRange a) :
    image a = MycpuBareWitness.image a := if_neg outside

theorem scratch_initial : readBytes initial.memory (MycpuBare.raSlot entry) 8 = some 0 ∧
    readBytes initial.memory (MycpuBare.s0Slot entry) 8 = some 0 := by
  change readBytes image _ _ = _ ∧ readBytes image _ _ = _
  rw [← cached_image]
  constructor <;> rfl

private theorem code_outside : ∀ j : Fin 34,
    ¬tableRange (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) := by decide

private theorem code_ra_disjoint : ∀ (j : Fin 34) (k : Fin 8),
    addressAdd (MycpuBare.raSlot entry) k.val ≠
      BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)) := by decide

private theorem code_s0_disjoint : ∀ (j : Fin 34) (k : Fin 8),
    addressAdd (MycpuBare.s0Slot entry) k.val ≠
      BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int)) := by decide

theorem outside_stores (a : PhysicalAddress) (ra : ¬Footprint (MycpuBare.raSlot entry) 8 a)
    (s0 : ¬Footprint (MycpuBare.s0Slot entry) 8 a) : (stateAt 14).memory a = image a := by
  change writeBytes (writeBytes image (MycpuBare.raSlot entry) 8 (entry .x1))
    (MycpuBare.s0Slot entry) 8 (entry .x8) a = _
  rw [writeBytes_outside _ _ _ _ _ s0, writeBytes_outside _ _ _ _ _ ra]

theorem code (j : Fin 34) :
    (stateAt 14).memory (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) =
      MycpuBareWitness.image (BitVec.ofInt 64 (MycpuDecode.base + (j.val : Int))) := by
  rw [outside_stores _ (by rintro ⟨k,hk,eq⟩; exact code_ra_disjoint j ⟨k,hk⟩ eq)
    (by rintro ⟨k,hk,eq⟩; exact code_s0_disjoint j ⟨k,hk⟩ eq)]
  exact image_outside _ (code_outside j)

private theorem save_below_table : ∀ k : Fin 8,
    (addressAdd (MycpuBare.raSlot entry) k.val).toNat < rootBase ∧
    (addressAdd (MycpuBare.s0Slot entry) k.val).toNat < rootBase := by decide

theorem tables_preserved (a : PhysicalAddress) (inside : tableRange a) :
    (stateAt 14).memory a = image a := by
  apply outside_stores
  · rintro ⟨k,hk,eq⟩
    have bound := (save_below_table ⟨k,hk⟩).1
    rw [eq] at bound
    exact Nat.not_lt_of_ge inside.1 bound
  · rintro ⟨k,hk,eq⟩
    have bound := (save_below_table ⟨k,hk⟩).2
    rw [eq] at bound
    exact Nat.not_lt_of_ge inside.1 bound

theorem configured_memory_ok : MemoryOK configured := by
  refine ⟨rfl, fun _ => Nat.zero_le _, ?_⟩
  intro a low high
  change Domain image a
  unfold Domain image
  split
  · exact ⟨_, rfl⟩
  · refine ⟨Xv6.Machine.bootImage.byte a.toNat, ?_⟩
    change loadedRam Xv6.Machine.bootImage a = _
    exact if_pos ⟨low, high⟩

theorem configured_reservations_ok : ReservationsOK configured := by
  intro other r impossible
  cases impossible

end Xv6.Kernel.MycpuKptWitness
