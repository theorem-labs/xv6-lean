import Xv6.Kernel.KptMemory4Plan
import Xv6.Kernel.KptHardwareProofs
import MachCSL.Logic.SupervisorWrite4Proofs
import MachCSL.Logic.SupervisorMemOuter4Link
import MachCSL.Logic.SupervisorWriteEA4Plan

namespace Xv6.Kernel.KptMemory4
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

private theorem widen_read {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {program : SailM α} {value}
    (cut : SupervisorFetchRead.OneRead small rs address 4 program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorFetchRead.OneRead large rs address 4 program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  refine ⟨tail, ?_, success, error⟩
  clear success error
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (KptMemory.widen_plan first members) ih

private theorem widen_write {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {address : BitVec 64} {word : BitVec 32} {program : SailM α} {value}
    (cut : SupervisorWrite4.OneWrite small rs address word program value)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : SupervisorWrite4.OneWrite large rs address word program value := by
  obtain ⟨tail, cut, success, error⟩ := cut
  refine ⟨tail, ?_, success, error⟩
  clear success error
  induction cut with
  | event => exact .event
  | «prefix» first _ ih => exact .prefix (KptMemory.widen_plan first members) ih

theorem data_pma rs data (ambient : Ambient rs) pa (aligned : KernelDatumWord4.Aligned pa)
    (ram : KernelDatum.Ram pa) :
    matching_pma_region (KptAddress.prepare rs data .pma_regions) (.Physaddr pa) 4 = some KptHardware.ramRegion := by
  rw [KptAddress.prepare_pma, ambient.address.pma]
  exact MycpuBare.pma_ram pa 4 (by decide) (data_range pa aligned ram)

theorem data_read shares rs data (ambient : Ambient rs) va pa
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : KernelDatumWord4.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorFetchRead.OneRead (KptAddress.footprint shares) (KptAddress.prepare rs data) pa 4
      (readAfterAddress va (.Ok (.Physaddr pa,.PBMT_PMA,()))) (fun word => (.Ok word : Result .load)) := by
  unfold readAfterAddress
  apply SupervisorFetchRead.OneRead.bind (value := fun word => (.Ok word : SupervisorMemOuter4.ReadResult))
  · change SupervisorFetchRead.OneRead _ _ _ _ (SupervisorMemOuter4.readProgram pa) _
    rw [SupervisorMemOuter4.read_factor]
    apply SupervisorFetchRead.OneRead.prefix (effective shares rs data ambient .load)
    rw [SupervisorMemOuter4.read_supervisor]
    apply SupervisorFetchRead.OneRead.bind (value := fun word => .Ok (word,()))
    · apply widen_read (SupervisorRead4.checked_boundary
        ⟨shares.pma,.own 1,.own 1,shares.htif⟩ (KptAddress.prepare rs data) pa tor
        (data_range pa aligned ram) (by simpa using ambient.address.htif) KptHardware.ramRegion
        (data_pma rs data ambient pa aligned ram) (by rfl) (alignment pa aligned))
      intro cell member
      simp only [SupervisorFetchRead.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp [KptAddress.footprint, KptAddress.innerShares, KptTranslate.footprint,
          KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint, SupervisorPteRead.footprint,
          SupervisorRead.footprint]
    · intro word; rfl
  · intro word; rfl

theorem data_ea shares rs data (ambient : Ambient rs) pa
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : KernelDatumWord4.Aligned pa) (ram : KernelDatum.Ram pa) :
    RegisterPlan.Returns (KptAddress.footprint shares) (KptAddress.prepare rs data)
      (SupervisorWriteEA4.program pa) (.Ok ()) (KptAddress.prepare rs data) := by
  apply KptMemory.widen_plan (SupervisorWriteEA4.program_plan
    ⟨shares.status,shares.privilege,shares.pma,.own 1,.own 1⟩ (KptAddress.prepare rs data) pa KptHardware.ramRegion
    ⟨by simpa using ambient.address.privilege, by simpa using ambient.mprv, tor,
      data_range pa aligned ram, data_pma rs data ambient pa aligned ram, by rfl,
      alignment pa aligned⟩)
  intro cell member
  simp only [SupervisorWriteEA.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [KptAddress.footprint, KptAddress.outerShares, Sv39Address.footprint, SupervisorBare.footprint,
      KptAddress.innerShares, KptTranslate.footprint, KptMiss.footprint, KptAD.footprint,
      SupervisorPteAD.footprint, SupervisorPteRead.footprint, SupervisorRead.footprint]

theorem data_write [Platform] shares rs data (ambient : Ambient rs) va pa new
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (KptAddress.prepare rs data))
    (aligned : KernelDatumWord4.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorWrite4.OneWrite (KptAddress.footprint shares) (KptAddress.prepare rs data) pa new
      (writeAfterAddress va new (.Ok (.Physaddr pa,.PBMT_PMA,()))) (fun value => (.Ok value : Result .store)) := by
  unfold writeAfterAddress
  apply SupervisorWrite4.OneWrite.prefix (data_ea shares rs data ambient pa tor aligned ram)
  unfold writeAfterEA
  apply SupervisorWrite4.OneWrite.bind (value := fun value => (.Ok value : SupervisorWrite4.Result))
  · change SupervisorWrite4.OneWrite _ _ _ _ (SupervisorMemOuter4.writeProgram pa new) _
    rw [SupervisorMemOuter4.write_factor]
    apply SupervisorWrite4.OneWrite.prefix (effective shares rs data ambient .store)
    rw [SupervisorMemOuter4.write_supervisor]
    apply widen_write (SupervisorWrite4.checked_boundary
      ⟨shares.pma,.own 1,.own 1,shares.htif⟩ (KptAddress.prepare rs data) pa new tor
      (data_range pa aligned ram) (by simpa using ambient.address.htif) KptHardware.ramRegion
      (data_pma rs data ambient pa aligned ram) (by rfl) (alignment pa aligned))
    intro cell member
    simp only [SupervisorWrite4.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [KptAddress.footprint, KptAddress.innerShares, KptTranslate.footprint,
        KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint, SupervisorPteRead.footprint,
        SupervisorRead.footprint]
  · intro value; rfl

end Xv6.Kernel.KptMemory4
