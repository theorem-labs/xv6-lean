import Xv6.Kernel.MycpuBareGeometry
import Xv6.Kernel.MycpuFetchPlan

namespace Xv6.Kernel.MycpuBare
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

private theorem bare_bits : ∀ bits : BitVec 4,
    satpMode_of_bits .RV64 bits = some .Bare → bits = 0#4 := by
  intro bits h
  unfold satpMode_of_bits at h
  split at h <;> simp_all

theorem supervisor_bare {rs : RegisterFile} (config : SupervisorConfig rs) : SupervisorBare.Config rs :=
  ⟨config.privilege, config.sxl, bare_bits _ config.bare⟩

theorem supervisor_transform {rs : RegisterFile} (config : SupervisorConfig rs) :
    SupervisorAddress.Config rs .Bare := by
  refine ⟨config.privilege, config.mprv, config.mxr, ?_, config.sxl, config.bare⟩
  rw [config.environment]
  rfl

theorem supervisor_cycle {rs : RegisterFile} (config : SupervisorConfig rs) (i : Fin 14)
    (pc : rs .PC = MycpuDecode.address i) : MycpuCycle.Config rs i ramRegion := by
  have c : _get_Misa_C (rs .misa) = 1#1 := by rw [config.misa]; rfl
  have s : _get_Misa_S (rs .misa) = 1#1 := by rw [config.misa]; rfl
  have matched : matching_pma_region (rs .pma_regions) (.Physaddr (MycpuDecode.address i))
      (MycpuFetchBytes.width i) = some ramRegion := by
    rw [config.pma]
    apply pma_ram
    · have width : MycpuFetchBytes.width i = 2 ∨ MycpuFetchBytes.width i = 4 := by
        unfold MycpuFetchBytes.width
        split <;> simp
      omega
    · exact MycpuFetch.address_range i
  refine ⟨⟨⟨pc, c, supervisor_bare config, config.tor, config.htif, matched, ?_⟩,
    ⟨s, config.delegated, config.sie⟩, ?_, config.landing⟩, config.active⟩
  · rfl
  · unfold MycpuDecode.Config
    split
    · exact config.misa
    · exact ⟨config.privilege, config.environment⟩

theorem supervisor_read {rs : RegisterFile} (config : SupervisorConfig rs) (slot : MycpuMemory.Slot)
    (range : SupervisorPhysical.RamRange (MycpuMemory.address slot rs) 8) :
    MycpuMemory.ReadConfig slot rs ramRegion := by
  refine ⟨supervisor_transform config,
    ⟨supervisor_bare config, config.mprv, config.tor, range, config.htif, ?_, ?_⟩⟩
  · rw [config.pma]; exact pma_ram _ _ (by decide) range
  · rfl

theorem supervisor_write {rs : RegisterFile} (config : SupervisorConfig rs) (slot : MycpuMemory.Slot)
    (range : SupervisorPhysical.RamRange (MycpuMemory.address slot rs) 8) :
    MycpuMemory.WriteConfig slot rs ramRegion := by
  refine ⟨supervisor_transform config,
    ⟨supervisor_bare config, config.mprv, config.tor, range, config.htif, ?_, ?_⟩⟩
  · rw [config.pma]; exact pma_ram _ _ (by decide) range
  · rfl

theorem supervisor_return {rs : RegisterFile} (config : SupervisorConfig rs) : MycpuReturn.Config rs := by
  refine ⟨config.privilege, ?_, ?_⟩
  · rw [config.environment]; rfl
  · rw [config.misa]; rfl

end Xv6.Kernel.MycpuBare
