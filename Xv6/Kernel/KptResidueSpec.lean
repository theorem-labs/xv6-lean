import Xv6.Kernel.KptResidueDefs

namespace Xv6.Kernel.KptResidue
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Resource assembly and borrowing only. No CSR update, SATP switch,
translation success or physical table publication is assumed by these laws. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  snapshot_persistent : ∀ era tlb, Persistent (tlbSnapOK capacity era tlb)
  credentials_persistent : ∀ era cpu, Persistent (credentials capacity era cpu)
  snapshot_intro : ∀ era tree tlb, TlbCoherence.Coherent 0#16 tree tlb →
    iprop(⊢ KptShared.snapshot capacity era tree -∗ tlbSnapOK capacity era tlb)
  snapshot_coherent : ∀ era tree tlb,
    iprop(⊢ tlbSnapOK capacity era tlb -∗ KptShared.snapshot capacity era tree -∗
      ⌜TlbCoherence.Coherent 0#16 tree tlb⌝)
  snapshot_empty : ∀ era (N : Namespace) (E : CoPset) root tlb,
    (↑N : CoPset) ⊆ E → EmptyTlb tlb →
    iprop(⊢ KptShared.shared capacity era N root ={E}=∗ tlbSnapOK capacity era tlb)
  credentials_intro : ∀ era cpu B,
    iprop(⊢ KptShared.bound capacity era B -∗
      TsoPinnedReadWP.credential capacity.machine era cpu B -∗ credentials capacity era cpu)
  credentials_boot : ∀ era cpu B, hartAgent cpu = 0 →
    iprop(⊢ KptShared.bound capacity era B -∗
      Tso.Views.llb capacity.machine.era.views era.logLength B -∗ credentials capacity era cpu)
  intro_residue : ∀ era cpu (N : Namespace) root satp tlb tree B,
    SatpRooted root satp → TlbCoherence.Coherent 0#16 tree tlb →
    iprop(⊢ satpCell capacity era cpu satp -∗ tlbCell capacity era cpu tlb -∗
      KptShared.snapshot capacity era tree -∗ KptShared.bound capacity era B -∗
      TsoPinnedReadWP.credential capacity.machine era cpu B -∗ pmpConfig capacity era cpu root -∗
      KptShared.shared capacity era N root -∗ residue capacity era cpu N root)
  open_residue : ∀ era cpu (N : Namespace) root,
    iprop(residue capacity era cpu N root ⊣⊢ ∃ satp tlb, parts capacity era cpu N root satp tlb)
  shared : ∀ era cpu (N : Namespace) root,
    iprop(residue capacity era cpu N root ⊢ KptShared.shared capacity era N root)
  creds : ∀ era cpu (N : Namespace) root,
    iprop(residue capacity era cpu N root ⊢ credentials capacity era cpu)
  satp_access : ∀ era cpu (N : Namespace) root,
    iprop(residue capacity era cpu N root ⊢ ∃ satp,
      satpCell capacity era cpu satp ∗ ⌜SatpRooted root satp⌝ ∗
      (satpCell capacity era cpu satp -∗ residue capacity era cpu N root))
  grant_facts : ∀ era cpu (N : Namespace) root rs,
    iprop(⊢ Registers.regInterpAt capacity.machine.era.registers (era.registers cpu) rs -∗
      residue capacity era cpu N root -∗ ⌜MachCSL.Machine.SupervisorPmp.TorRam rs⌝)

end Xv6.Kernel.KptResidue
