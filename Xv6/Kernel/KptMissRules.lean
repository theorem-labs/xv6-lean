import Xv6.Kernel.KptMissPureProofs
import Xv6.Kernel.Sv39MissRules
import Xv6.Kernel.KptTreeWalkLink

namespace Xv6.Kernel.KptMiss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

omit [Platform] in
theorem cells_ad era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      KptAD.cells capacity era cpu rs shares ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs [(.tlb, .own 1)]) :=
  Sv39Miss.cells_ad capacity.machine era cpu rs shares

omit [Platform] in
theorem cells_walk era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      KptTreeWalk.cells capacity era cpu rs shares.memory ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
        [(.menvcfg, shares.environment), (.tlb, .own 1)]) :=
  Sv39Miss.cells_walk capacity.machine era cpu rs shares

omit [Platform] in
instance clients_persistent era cpu N root tree bound :
    Persistent (clients capacity era cpu N root tree bound) :=
  KptTreeWalk.clients_persistent capacity era cpu N root tree bound

omit [Platform] in
theorem clients_ad era cpu N root tree bound :
    iprop(clients capacity era cpu N root tree bound ⊢ KptAD.clients capacity era N root tree) := by
  iintro H
  iunfold clients at H
  iunfold KptTreeWalk.clients at H
  icases H with ⟨Hshared,Hsnapshot,_,_⟩
  iunfold KptAD.clients
  iunfold KptWriteEvent.clients
  iframe Hshared Hsnapshot

/-- Reuse only the generic full-cell fill rule; its global flag is arbitrary. -/
theorem wp_fill shares rs asid vpn ppn pte address global
    image fixed whole gen era cpu (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu (Sv39Tlb.after rs asid vpn ppn pte address global) shares -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation ())) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (add_to_TLB 39 asid vpn ppn pte address 0 global >>= continuation)) post) :=
  Sv39Miss.wp_fill capacity.machine shares rs asid vpn ppn pte address global
    image fixed whole gen era cpu continuation post

theorem wp_after_update shares rs asid vpn p2 p1 ppn permission cachedA cachedD branch
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu
          (after rs asid vpn p2 p1 ppn (KptLeaf.word ppn permission cachedA cachedD) branch) shares -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (result ppn branch))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (afterUpdate asid vpn (KptTreeWalk.output vpn p2 p1 ppn permission false cachedA cachedD)
          (KptAD.result branch) >>= continuation)) post) := by
  rw [after_update]
  cases branch <;> simp only [after, fillWord, BootPmp.sail_bind_assoc, BootPmp.sail_pure_bind]
  all_goals iintro #Hcert Hregs Hfinish
  all_goals first
  | iapply Hfinish $$ Hregs
  | iapply wp_fill capacity shares rs asid vpn ppn _ (.Physaddr (PtTree.addr0 p1 vpn))
      (PtTree.globalAfter false p2 p1 (KptLeaf.word ppn permission cachedA cachedD))
      image fixed whole gen era cpu (fun _ => continuation (result ppn _)) post $$ Hcert Hregs Hfinish

end Xv6.Kernel.KptMiss
