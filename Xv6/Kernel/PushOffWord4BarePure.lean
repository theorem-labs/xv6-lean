import Xv6.Kernel.PushOffWord4BareSpec
import Xv6.Kernel.KptMemory4DataPlan
import MachCSL.Logic.SupervisorAddressPlan
import MachCSL.Machine.SupervisorBarePlan
namespace Xv6.Kernel.PushOffWord4Bare
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem unique (s : Shares) : RegisterFootprint.Unique (footprint s) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorBareFetch.footprint,
    SupervisorBare.footprint, SupervisorFetchRead.footprint]

theorem bare_config (rs : RegisterFile) (config : Config rs) : SupervisorBare.Config rs := by
  refine ⟨config.transform.privilege, config.transform.sxl, ?_⟩
  have h := config.transform.decoded
  simp only [satpMode_of_bits] at h
  split at h <;> simp_all

theorem transform (s : Shares) (rs : RegisterFile) (config : Config rs) va kind :
    RegisterPlan.Returns (footprint s) rs (SupervisorAddress.program va kind) (.Virtaddr va) rs := by
  apply KptMemory.widen_plan (SupervisorAddress.program_plan (transformShares s) rs .Bare config.transform va kind)
  intro cell member
  simp only [SupervisorAddress.footprint, transformShares, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [footprint, SupervisorBareFetch.footprint, SupervisorBare.footprint]

theorem pma (rs : RegisterFile) (config : Config rs) va (range : SupervisorPhysical.RamRange va 4) :
    matching_pma_region (rs .pma_regions) (.Physaddr va) 4 = some KptHardware.ramRegion := by
  rw [config.pma]
  exact MycpuBare.pma_ram va 4 (by decide) range
end Xv6.Kernel.PushOffWord4Bare
