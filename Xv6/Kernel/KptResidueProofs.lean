import Xv6.Kernel.KptResidueSpec
import Xv6.Kernel.KptSharedLink
import Xv6.Kernel.TlbCoherenceLink
import MachCSL.Logic.TsoPinnedReadProofs
import MachCSL.Logic.RegisterProofs

namespace Xv6.Kernel.KptResidue
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance snapshot_persistent era tlb : Persistent (tlbSnapOK capacity era tlb) := by
  unfold tlbSnapOK
  infer_instance
instance credentials_persistent era cpu : Persistent (credentials capacity era cpu) := by
  unfold credentials KptShared.credentials
  infer_instance

theorem snapshot_intro era tree tlb (coherent : TlbCoherence.Coherent 0#16 tree tlb) :
    iprop(⊢ KptShared.snapshot capacity era tree -∗ tlbSnapOK capacity era tlb) := by
  iintro Hsnapshot
  iunfold tlbSnapOK
  iexists tree
  iframe Hsnapshot
  ipureintro
  exact coherent

/-- Both snapshots are fragments of the same actual era ghost name. -/
theorem snapshot_coherent era tree tlb :
    iprop(⊢ tlbSnapOK capacity era tlb -∗ KptShared.snapshot capacity era tree -∗
      ⌜TlbCoherence.Coherent 0#16 tree tlb⌝) := by
  iintro Hsnap #Htree
  iunfold tlbSnapOK at Hsnap
  icases Hsnap with ⟨%other,%coherent,#Hother⟩
  ihave %same := KptGhost.agree capacity.ghost era.kernelPageTable other tree $$ [Hother Htree]
  · iframe Hother Htree
  ipureintro
  exact TlbCoherence.nativeSpec.coherent_canon 0#16 other tree tlb same coherent

theorem credentials_intro era cpu B :
    iprop(⊢ KptShared.bound capacity era B -∗
      TsoPinnedReadWP.credential capacity.machine era cpu B -∗ credentials capacity era cpu) := by
  iintro Hbound Hcredential
  iunfold credentials
  iunfold KptShared.credentials
  iexists B
  iframe Hbound Hcredential

theorem credentials_boot era cpu B (boot : hartAgent cpu = 0) :
    iprop(⊢ KptShared.bound capacity era B -∗
      Tso.Views.llb capacity.machine.era.views era.logLength B -∗ credentials capacity era cpu) := by
  iintro Hbound Hlog
  iapply credentials_intro capacity era cpu B $$ Hbound
  have rule := TsoPinnedRead.bootCredential_boot capacity.machine.era.tso era.tsoNames cpu B boot
  dsimp only [Era.Capacity.tso, Era.Record.tsoNames] at rule
  iunfold TsoPinnedReadWP.credential
  simp only [Era.Capacity.tso, Era.Record.tsoNames]
  iapply rule $$ Hlog

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Snapshot allocation is actual native invariant access. Full vector
emptiness proves the hash-indexed coherence with its checked bound. -/
theorem snapshot_empty era (N : Namespace) (E : CoPset) root tlb
    (mask : (↑N : CoPset) ⊆ E) (empty : EmptyTlb tlb) :
    iprop(⊢ KptShared.shared capacity era N root ={E}=∗ tlbSnapOK capacity era tlb) := by
  iintro #Hshared
  imod (KptShared.nativeSpec capacity).read_snapshot era N E root mask $$ Hshared with ⟨%tree,Hsnapshot⟩
  imodintro
  iapply snapshot_intro capacity era tree tlb _ $$ Hsnapshot
  apply TlbCoherence.nativeSpec.empty
  intro query
  exact empty ⟨TlbCoherence.index query, Sv39Tlb.index_bound query⟩

theorem intro_residue era cpu (N : Namespace) root satp tlb tree B
    (rooted : SatpRooted root satp) (coherent : TlbCoherence.Coherent 0#16 tree tlb) :
    iprop(⊢ satpCell capacity era cpu satp -∗ tlbCell capacity era cpu tlb -∗
      KptShared.snapshot capacity era tree -∗ KptShared.bound capacity era B -∗
      TsoPinnedReadWP.credential capacity.machine era cpu B -∗ pmpConfig capacity era cpu root -∗
      KptShared.shared capacity era N root -∗ residue capacity era cpu N root) := by
  iintro Hsatp Htlb Hsnapshot Hbound Hcredential Hpmp Hshared
  iunfold residue
  iexists satp, tlb
  iunfold parts
  iframe Hsatp Htlb Hpmp Hshared
  isplit
  · ipureintro; exact rooted
  · isplitl [Hsnapshot]
    · iapply snapshot_intro capacity era tree tlb coherent $$ Hsnapshot
    · iapply credentials_intro capacity era cpu B $$ Hbound Hcredential

theorem open_residue era cpu (N : Namespace) root :
    iprop(residue capacity era cpu N root ⊣⊢ ∃ satp tlb, parts capacity era cpu N root satp tlb) := .rfl

theorem shared era cpu (N : Namespace) root :
    iprop(residue capacity era cpu N root ⊢ KptShared.shared capacity era N root) := by
  unfold residue parts
  iintro ⟨%satp,%tlb,_,_,_,_,_,Hshared,_⟩
  iexact Hshared

theorem creds era cpu (N : Namespace) root :
    iprop(residue capacity era cpu N root ⊢ credentials capacity era cpu) := by
  unfold residue parts
  iintro ⟨%satp,%tlb,_,_,_,_,_,_,Hcredentials⟩
  iexact Hcredentials

/-- The wand takes exactly the borrowed full SATP cell at the same value. -/
theorem satp_access era cpu (N : Namespace) root :
    iprop(residue capacity era cpu N root ⊢ ∃ satp,
      satpCell capacity era cpu satp ∗ ⌜SatpRooted root satp⌝ ∗
      (satpCell capacity era cpu satp -∗ residue capacity era cpu N root)) := by
  unfold residue parts
  iintro ⟨%satp,%tlb,Hsatp,%rooted,Htlb,Hsnap,Hpmp,Hshared,Hcredentials⟩
  iexists satp
  iframe Hsatp
  isplit
  · ipureintro; exact rooted
  · iintro Hsatp
    iexists satp, tlb
    iframe Hsatp Htlb Hsnap Hpmp Hshared Hcredentials
    ipureintro
    exact rooted

/-- The source grant projection uses the actual authority for this CPU and
era; existential PMP vectors alone do not determine an unrelated file. -/
theorem grant_facts era cpu (N : Namespace) root rs :
    iprop(⊢ Registers.regInterpAt capacity.machine.era.registers (era.registers cpu) rs -∗
      residue capacity era cpu N root -∗ ⌜MachCSL.Machine.SupervisorPmp.TorRam rs⌝) := by
  iintro Hauth Hresidue
  iunfold residue at Hresidue
  iunfold parts at Hresidue
  icases Hresidue with ⟨%satp,%tlb,_,_,_,_,Hpmp,_,_⟩
  iunfold pmpConfig at Hpmp
  iunfold MachCSL.Logic.SupervisorPmp.config at Hpmp
  icases Hpmp with ⟨%old,%tor,Hcells⟩
  isimp only [MachCSL.Logic.SupervisorPmp.footprint, RegisterFootprint.cells] at Hcells
  icases Hcells with ⟨Hcfg,Haddr,_⟩
  ihave %cfg := Registers.reg_valid capacity.machine.era.registers (era.registers cpu) rs .pmpcfg_n
    (old .pmpcfg_n) $$ Hauth Hcfg
  ihave %addr := Registers.reg_valid capacity.machine.era.registers (era.registers cpu) rs .pmpaddr_n
    (old .pmpaddr_n) $$ Hauth Haddr
  ipureintro
  rcases tor with ⟨htor,hpositive,hx,hw,hr,hcovers⟩
  constructor <;> simp_all only [MachCSL.Machine.SupervisorPmp.entry0, MachCSL.Machine.SupervisorPmp.upper0]

theorem actual : Spec capacity :=
  ⟨snapshot_persistent capacity, credentials_persistent capacity, snapshot_intro capacity,
    snapshot_coherent capacity, snapshot_empty capacity, credentials_intro capacity,
    credentials_boot capacity, intro_residue capacity, open_residue capacity, shared capacity,
    creds capacity, satp_access capacity, grant_facts capacity⟩

end Xv6.Kernel.KptResidue
