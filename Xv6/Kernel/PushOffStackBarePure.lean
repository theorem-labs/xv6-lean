import Xv6.Kernel.PushOffStackBareDefs
import Xv6.Kernel.PushOffStackRules
import Xv6.Kernel.MycpuBareGeometry
import MachCSL.Logic.SupervisorAddressPlan

namespace Xv6.Kernel.PushOffStack.Bare
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem patched_config control satp pmp (config : Config control) : Config (patch control satp pmp) :=
  ⟨config.privilege,config.pma,config.htif,config.pmm,config.adue⟩

theorem patched_tor control satp pmp cpu values (tor : SupervisorPmp.TorRam pmp) :
    SupervisorPmp.TorRam (entry (patch control satp pmp) cpu values) :=
  ⟨tor.tor,tor.positive,tor.execute,tor.write,tor.read,tor.covers⟩

theorem transform_config control satp pmp cpu values (config : Config control)
    (facts : SupervisorBits.MsFacts (control .mstatus))
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) :
    SupervisorAddress.Config (entry (patch control satp pmp) cpu values) .Bare := by
  have a := ambient (patch control satp pmp) cpu values (patched_config control satp pmp config) facts
  refine ⟨a.address.privilege,a.mprv,a.mxr,a.pmm,a.address.sxl,?_⟩
  change satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 satp)) = some .Bare
  rw [mode]
  rfl

theorem read_config control satp pmp cpu values va (config : Config control)
    (facts : SupervisorBits.MsFacts (control .mstatus))
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp)
    (range : SupervisorPhysical.RamRange va 8) :
    SupervisorBareRead.Config (entry (patch control satp pmp) cpu values) va MycpuBare.ramRegion := by
  have a := ambient (patch control satp pmp) cpu values (patched_config control satp pmp config) facts
  refine ⟨⟨a.address.privilege,a.address.sxl,mode⟩,a.mprv,patched_tor control satp pmp cpu values tor,range,a.address.htif,?_,?_⟩
  · change matching_pma_region (control .pma_regions) (.Physaddr va) 8 = _
    rw [config.pma]
    exact MycpuBare.pma_ram va 8 (by decide) range
  · rfl

theorem write_config control satp pmp cpu values va (config : Config control)
    (facts : SupervisorBits.MsFacts (control .mstatus))
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp)
    (range : SupervisorPhysical.RamRange va 8) :
    SupervisorBareWrite.Config (entry (patch control satp pmp) cpu values) va MycpuBare.ramRegion := by
  have c := read_config control satp pmp cpu values va config facts mode tor range
  exact ⟨c.bare,c.mprv,c.tor,c.range,c.disabled,c.matched,rfl⟩

theorem transform_plan s slot rs kind va (config : SupervisorAddress.Config rs .Bare) :
    RegisterPlan.Returns (bareFootprint s slot) rs (SupervisorAddress.program va kind) (.Virtaddr va) rs := by
  apply KptMemory.widen_plan (SupervisorAddress.program_plan (transformShares s) rs .Bare config va kind)
  intro cell member
  simp only [SupervisorAddress.footprint,transformShares,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [bareFootprint,footprint,PushOffStack.memoryShares,MycpuKptMemory.memoryShares,KptAddress.auxiliaryFootprint]

theorem source_plan s control satp pmp cpu values slot :
    RegisterPlan.Returns (bareFootprint s slot) (entry (patch control satp pmp) cpu values)
      (rX_bits (regidx slot)) (sourceValue cpu values slot) (entry (patch control satp pmp) cpu values) := by
  apply KptMemory.widen_plan (PushOffStack.source_plan s (patch control satp pmp) cpu values slot)
  intro cell member
  exact List.mem_append_left _ member

theorem sp_plan s control satp pmp cpu values slot :
    RegisterPlan.Returns (bareFootprint s slot) (entry (patch control satp pmp) cpu values)
      (rX_bits (.Regidx 2#5)) (HartTp.rget cpu values 2#5) (entry (patch control satp pmp) cpu values) := by
  apply KptMemory.widen_plan (PushOffStack.sp_plan s (patch control satp pmp) cpu values slot)
  intro cell member
  exact List.mem_append_left _ member

theorem load_tail_plan s control satp pmp cpu values slot old :
    RegisterPlan.Returns (bareFootprint s slot) (entry (patch control satp pmp) cpu values)
      (loadTail slot (.Ok old)) (.Retire_Success ()) (entry (patch control satp pmp) cpu (afterMap .load slot values old)) := by
  apply KptMemory.widen_plan (PushOffStack.load_tail_plan s (patch control satp pmp) cpu values slot old)
  intro cell member
  exact List.mem_append_left _ member

end Xv6.Kernel.PushOffStack.Bare
