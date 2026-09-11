import Xv6.Kernel.PushOffStackBarePure

namespace Xv6.Kernel.PushOffStack.Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem common_patch (era : Era.Record) (cpu : CPU) control values s slot satp pmp :
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry (patch control satp pmp) cpu values) (footprint s slot) =
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) (footprint s slot) := by
  cases slot <;> rfl

theorem packet_partition era cpu control values s slot :
    iprop(packet capacity era cpu .bare control values s ⊣⊢ ∃ satp pmp,
      ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗ ⌜SupervisorPmp.TorRam pmp⌝ ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry (patch control satp pmp) cpu values) (bareFootprint s slot) ∗
      packetFrame capacity era cpu control values s slot) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu .bare control values s).to_eq,
    (cells_partition capacity era cpu (entry control cpu values) s slot).to_eq]
  constructor
  · iintro ⟨⟨Hregs,Hrest⟩,Hbits,Hz,Htr⟩
    iunfold MycpuRegimeShell.translation at Htr
    iunfold MycpuRegimeShell.bare at Htr
    icases Htr with ⟨%satp,Hsatp,%mode,Hpmp⟩
    iunfold MachCSL.Logic.SupervisorPmp.config at Hpmp
    icases Hpmp with ⟨%pmp,%tor,Hpmp⟩
    isimp only [MachCSL.Logic.SupervisorPmp.footprint,RegisterFootprint.cells] at Hpmp
    icases Hpmp with ⟨Hcfg,Haddr,_⟩
    iexists satp,pmp
    isplitr
    · ipureintro; exact mode
    isplitr
    · ipureintro; exact tor
    isplitl [Hregs Hsatp Hcfg Haddr]
    · unfold bareFootprint
      rw [(RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu)
        (entry (patch control satp pmp) cpu values) _ _).to_eq,common_patch]
      isplitl [Hregs]
      · iexact Hregs
      · simp only [RegisterFootprint.cells,entry,MycpuRegimeShell.entry,MycpuOff.entry,patch,MycpuBareSource.patch]
        iframe
    · iunfold packetFrame
      iframe
  · iintro ⟨%satp,%pmp,%mode,%tor,Hregs,Hsaved⟩
    iunfold packetFrame at Hsaved
    icases Hsaved with ⟨Hrest,Hbits,Hz⟩
    iunfold bareFootprint at Hregs
    isimp only [(RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu)
      (entry (patch control satp pmp) cpu values) _ _).to_eq,common_patch] at Hregs
    icases Hregs with ⟨Hregs,Htr⟩
    isimp only [RegisterFootprint.cells,entry,MycpuRegimeShell.entry,MycpuOff.entry,patch,MycpuBareSource.patch] at Htr
    icases Htr with ⟨Hsatp,Hcfg,Haddr,_⟩
    iframe Hregs Hrest Hbits Hz
    iunfold MycpuRegimeShell.translation
    iunfold MycpuRegimeShell.bare
    iexists satp
    iframe Hsatp
    isplitr
    · ipureintro; exact mode
    iunfold MachCSL.Logic.SupervisorPmp.config
    iexists pmp
    isplitr
    · ipureintro; exact tor
    simp only [MachCSL.Logic.SupervisorPmp.footprint,RegisterFootprint.cells]
    iframe

theorem cells_memory era cpu rs s slot :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (bareFootprint s slot) ⊣⊢
      SupervisorBareRead.cells capacity.machine era cpu rs (memoryShares s) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (operands s slot)) := by
  simp only [bareFootprint,footprint,PushOffStack.memoryShares,MycpuKptMemory.memoryShares,
    KptAddress.auxiliaryFootprint,SupervisorBareRead.cells,SupervisorBareFetch.cells,
    SupervisorBareFetch.footprint,SupervisorBare.footprint,SupervisorFetchRead.footprint,
    memoryShares,operands,List.cons_append,List.nil_append,RegisterFootprint.cells]
  constructor
  · iintro ⟨Hms,Hpriv,Hpma,Hhtif,Henv,Hsp,Hdata,Hsatp,Hcfg,Haddr,_⟩
    iframe
  · iintro ⟨⟨Hms,Hpriv,Hsatp,Hpma,Hcfg,Haddr,Hhtif,_⟩,⟨Henv,Hsp,Hdata,_⟩⟩
    iframe

end Xv6.Kernel.PushOffStack.Bare
