import MachCSL.Memory.Proofs

/-! Closed byte-level litmus checks for the production TSO read/fence definitions.
These are kernel-reduced proofs, without native decision or external certificates.
They check chosen legal view values, not a complete machine execution relation. -/
namespace MachCSL.Memory.Litmus

private def image : ByteMap 64 := fun _ => some 0
private def x : PhysicalAddress := 0
private def y : PhysicalAddress := 1
private def storeX : Message 64 := ⟨singleton x 1, 0⟩
private def storeY : Message 64 := ⟨singleton y 1, 1⟩
private def stores : WriteLog 64 := [storeX, storeY]

/-- Store buffering permits both harts to read the other location's old byte. -/
theorem store_buffering_allowed :
    read image stores 0 0 y = some 0 ∧ read image stores 1 0 x = some 0 := by
  decide

/-- Own writes forward even while the other hart's store remains invisible. -/
theorem own_stores_forward :
    read image stores 0 0 x = some 1 ∧ read image stores 1 0 y = some 1 := by
  decide

/-- The two draining fences pass their authors' respective last publications. -/
theorem drain_views : fencePost 0 stores true 0 = 1 ∧ fencePost 1 stores true 0 = 2 := by
  decide

/-- At these post-fence views the both-zero observation is impossible. -/
theorem drained_store_buffering_not_both_zero :
    ¬ (read image stores 0 (fencePost 0 stores true 0) y = some 0 ∧
       read image stores 1 (fencePost 1 stores true 0) x = some 0) := by
  decide

/-- At the full view, observers see both published bytes. -/
theorem full_view_published :
    read image stores 0 stores.length y = some 1 ∧
    read image stores 1 stores.length x = some 1 := by
  decide

/-- A later foreign write to an address can supersede an older forwarded write. -/
theorem foreign_write_supersedes_forwarding :
    read image [storeX, ⟨singleton x 2, 1⟩] 0 2 x = some 2 := by
  decide

/-- Undraining fences are identities in the paper's Ztso model. -/
theorem nondraining_fence : fencePost 0 stores false 0 = 0 := by decide

end MachCSL.Memory.Litmus
