import Xv6.Kernel.BootPmaSpec
import MachCSL.Logic.RegisterProofs
import MachCSL.Machine.BootUniversalProofs
import Xv6.Kernel.KernelTextBootLink

namespace Xv6.Kernel.BootPma
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

set_option maxRecDepth 10000 in
theorem keys_count : remainingKeys.length = 179 := by decide
set_option maxRecDepth 10000 in
theorem keys_unique : remainingKeys.Nodup := by decide
theorem keys_mem (r : Register) : r ∈ remainingKeys ↔ r ≠ .pma_regions := by
  simp [remainingKeys, Registers.allRegisters_complete]
theorem remainder_lookup (rs : RegisterFile) (r : Register) :
    Iris.Std.PartialMap.get? (remainingMap rs) r =
    if r = .pma_regions then none else some (⟨r,rs r⟩ : Registers.Value) := by
  simp [remainingMap, Iris.Std.LawfulPartialMap.get?_delete, Registers.initialMap_lookup, eq_comm]
theorem boot_pma (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    g.registers cpu .pma_regions = pmaBoot := (BootUniversal.bootFacts_static image g facts cpu).pma
theorem pureSpec : PureSpec := ⟨keys_count, keys_unique, keys_mem, remainder_lookup, boot_pma⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance cell_persistent era cpu : Persistent (cell capacity era cpu) := by
  unfold cell
  infer_instance
instance all_persistent era : Persistent (all capacity era) := by
  unfold all
  infer_instance

theorem partition_hart name rs :
    iprop(Registers.initialCells capacity.machine.era.registers name rs ⊣⊢
      Registers.regPointsto capacity.machine.era.registers name .pma_regions (.own 1) (rs .pma_regions) ∗
      remainingHart capacity name rs) := by
  letI := capacity.machine.era.registers.registers
  unfold Registers.initialCells Registers.regPointsto remainingHart remainingMap
  exact BigSepM.bigSepM_delete (Registers.initialMap_lookup rs .pma_regions)

theorem partition_all era files :
    iprop(GlobalRegisters.allInitialCells capacity.machine.era.registers era.registers files ⊣⊢
      raw capacity era files ∗ remainingRegisters capacity era files) := by
  unfold GlobalRegisters.allInitialCells raw remainingRegisters
  exact (BigSepS.bigSepS_eqv fun {_} _ => partition_hart capacity _ _).trans BigSepS.bigSepS_sep

theorem persist_all era files (same : ∀ cpu, files cpu .pma_regions = pmaBoot) :
    iprop(raw capacity era files ⊢ |==> all capacity era) := by
  unfold raw all
  refine (BigSepS.bigSepS_mono fun {cpu} _ => ?_).trans (BigSepS.bigSepS_bupd _ _)
  unfold cell
  rw [same cpu]
  iintro H
  iapply Registers.regPointsto_persist capacity.machine.era.registers _ _ _ _ $$ H

theorem at_cpu era cpu : iprop(all capacity era ⊢ cell capacity era cpu ∗ all capacity era) := by
  unfold all
  iintro #H
  isplit
  · iapply (BigSepS.bigSepS_elem_of (GlobalRegisters.mem_allCPUs cpu))
    iexact H
  · iexact H

theorem produce image era g memory diskBytes (facts : BootFacts image g) :
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      (all capacity era ∗ retained capacity era memory g diskBytes)) := by
  unfold Era.bootClients
  iintro ⟨Hr, Ht, Hmeta, Hd, Hdisk, Hresv⟩
  ihave ⟨Hp, Hr⟩ := (partition_all capacity era g.registers).1 $$ Hr
  imod persist_all capacity era g.registers (boot_pma image g facts) $$ Hp with Hp
  imodintro
  unfold retained nonRegisterClients
  iframe

theorem produce_text_retained image era g memory diskBytes (facts : BootFacts image g) :
    iprop(KernelTextBoot.retained capacity era memory g diskBytes ⊢ |==>
      (all capacity era ∗ textRetained capacity era memory g diskBytes)) := by
  unfold KernelTextBoot.retained KernelTextBoot.otherClients MycpuBootResources.otherClients
  iintro ⟨Hrest, Hlen, Hr, Hmeta, Hd, Hdisk, Hresv⟩
  ihave ⟨Hp, Hr⟩ := (partition_all capacity era g.registers).1 $$ Hr
  imod persist_all capacity era g.registers (boot_pma image g facts) $$ Hp with Hp
  imodintro
  unfold textRetained nonRegisterClients
  iframe

theorem produce_text era g memory diskBytes (facts : BootFacts Xv6.Machine.bootImage g)
    (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      (KernelTextImage.physicalText capacity era ∗ all capacity era ∗
        textRetained capacity era memory g diskBytes)) := by
  iintro H
  imod KernelTextBoot.produce_update capacity era g memory diskBytes facts decoded $$ H with ⟨Ht, Hr⟩
  imod produce_text_retained capacity _ era g memory diskBytes facts $$ Hr with ⟨Hp, Hr⟩
  imodintro
  iframe

end Xv6.Kernel.BootPma
