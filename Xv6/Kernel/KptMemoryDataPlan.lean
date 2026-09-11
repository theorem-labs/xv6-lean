import Xv6.Kernel.KptMemoryPlan
import Xv6.Kernel.KptHardwareProofs
import MachCSL.Logic.SupervisorWriteProofs
import MachCSL.Logic.SupervisorWriteEAPlan

namespace Xv6.Kernel.KptMemory
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

private theorem widen_read {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {program : SailM α} {value}
    (cut : SupervisorRead.OneRead small rs address program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorRead.OneRead large rs address program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  refine ⟨tail, ?_, success, error⟩
  clear success error
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

private theorem widen_write {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address word : BitVec 64} {program : SailM α} {value}
    (cut : SupervisorWrite.OneWrite small rs address word program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorWrite.OneWrite large rs address word program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  refine ⟨tail, ?_, success, error⟩
  clear success error
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (widen_plan first members) ih

theorem data_range pa (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorPhysical.RamRange pa 8 := MycpuBare.aligned_ram_range pa aligned ram

theorem data_pma rs data (ambient : Ambient rs) pa (aligned : TsoContextWord.Aligned pa)
    (ram : KernelDatum.Ram pa) :
    matching_pma_region (KptAddress.prepare rs data .pma_regions) (.Physaddr pa) 8 = some KptHardware.ramRegion := by
  rw [KptAddress.prepare_pma, ambient.address.pma]
  exact MycpuBare.pma_ram pa 8 (by decide) (data_range pa aligned ram)

theorem data_read shares rs data (ambient : Ambient rs) va pa
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorRead.OneRead (KptAddress.footprint shares) (KptAddress.prepare rs data) pa
      (readAfterAddress va (.Ok (.Physaddr pa,.PBMT_PMA,()))) (fun word => (.Ok word : Result .load)) := by
  unfold readAfterAddress
  apply SupervisorRead.OneRead.bind (value := fun word => (.Ok word : SupervisorMemOuter.ReadResult))
  · change SupervisorRead.OneRead _ _ _ (SupervisorMemOuter.readProgram .data pa) _
    rw [SupervisorMemOuter.read_factor]
    apply SupervisorRead.OneRead.prefix (effective shares rs data ambient .load)
    rw [SupervisorMemOuter.read_supervisor]
    apply SupervisorRead.OneRead.bind (value := fun word => .Ok (word,()))
    · apply widen_read (SupervisorRead.checked_boundary
        ⟨shares.pma,.own 1,.own 1,shares.htif⟩ (KptAddress.prepare rs data) .data pa tor
        (data_range pa aligned ram) (by simpa using ambient.address.htif) KptHardware.ramRegion
        (data_pma rs data ambient pa aligned ram) (by rfl) (SupervisorRead.alignment pa aligned))
      intro cell member
      simp only [SupervisorRead.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [KptAddress.footprint, KptAddress.innerShares, KptTranslate.footprint,
          KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint, SupervisorPteRead.footprint,
          SupervisorRead.footprint]
    · intro word; rfl
  · intro word; rfl

theorem data_ea shares rs data (ambient : Ambient rs) pa
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa) :
    RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (SupervisorWriteEA.program pa) (.Ok ()) (KptAddress.prepare rs data) := by
  apply widen_plan (SupervisorWriteEA.program_plan
    ⟨shares.status,shares.privilege,shares.pma,.own 1,.own 1⟩ (KptAddress.prepare rs data) pa KptHardware.ramRegion
    ⟨by simpa using ambient.address.privilege, by simpa using ambient.mprv, tor,
      data_range pa aligned ram, data_pma rs data ambient pa aligned ram, by rfl,
      SupervisorRead.alignment pa aligned⟩)
  intro cell member
  simp only [SupervisorWriteEA.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [KptAddress.footprint, KptAddress.outerShares, Sv39Address.footprint, SupervisorBare.footprint,
      KptAddress.innerShares, KptTranslate.footprint, KptMiss.footprint, KptAD.footprint,
      SupervisorPteAD.footprint, SupervisorPteRead.footprint, SupervisorRead.footprint]

theorem data_write [Platform] shares rs data (ambient : Ambient rs) va pa new
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : TsoContextWord.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorWrite.OneWrite (KptAddress.footprint shares) (KptAddress.prepare rs data) pa new
      (writeAfterAddress va new (.Ok (.Physaddr pa,.PBMT_PMA,()))) (fun value => (.Ok value : Result .store)) := by
  unfold writeAfterAddress
  apply SupervisorWrite.OneWrite.prefix (data_ea shares rs data ambient pa tor aligned ram)
  unfold writeAfterEA
  apply SupervisorWrite.OneWrite.bind (value := fun value => (.Ok value : SupervisorWrite.Result))
  · change SupervisorWrite.OneWrite _ _ _ _ (SupervisorMemOuter.writeProgram pa new) _
    rw [SupervisorMemOuter.write_factor]
    apply SupervisorWrite.OneWrite.prefix (effective shares rs data ambient .store)
    rw [SupervisorWrite.value_priv_meta_eq]
    apply widen_write (SupervisorWrite.checked_boundary
      ⟨shares.pma,.own 1,.own 1,shares.htif⟩ (KptAddress.prepare rs data) pa new tor
      (data_range pa aligned ram) (by simpa using ambient.address.htif) KptHardware.ramRegion
      (data_pma rs data ambient pa aligned ram) (by rfl) (SupervisorRead.alignment pa aligned))
    intro cell member
    simp only [SupervisorWrite.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [KptAddress.footprint, KptAddress.innerShares, KptTranslate.footprint,
        KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint, SupervisorPteRead.footprint,
        SupervisorRead.footprint]
  · intro value; rfl

end Xv6.Kernel.KptMemory
