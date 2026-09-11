import Xv6.Kernel.Sv39HitPlan

namespace Xv6.Kernel.Sv39Hit
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_head environment rs asid vpn idx p2 p1 ppn perm a d access
    (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows perm access) mxr doSum
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs environment -∗
      (cells capacity era cpu rs environment -∗
        RegisterWP.threadWP capacity image fixed whole (.hart gen cpu
          (remainder vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
            (PtTree.addr0 p1 vpn) access mxr doSum
            (headValue rs (KptLeaf.word ppn perm a d) access) >>= continuation)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu
        (program asid vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
          access mxr doSum >>= continuation)) post) := by
  rw [kernel_head asid vpn idx p2 p1 ppn perm a d access supported allowed,
    BootPmp.sail_bind_assoc]
  unfold cells
  iintro #Hcert Hcells Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity (footprint environment) (footprint_unique environment)
    image fixed whole gen era cpu rs (head (KptLeaf.word ppn perm a d) access)
    (fun value after => value = headValue rs (KptLeaf.word ppn perm a d) access ∧ after = rs)
    (fun value => remainder vpn idx (entry asid vpn p2 p1 (KptLeaf.word ppn perm a d))
      (PtTree.addr0 p1 vpn) access mxr doSum value >>= continuation) post
    (head_plan environment rs (KptLeaf.word ppn perm a d) access) $$ Hcert Hcells
  iintro %value %after %same Hcells
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hcells

theorem wp_resume environment rs vpn idx ent response (bound : idx < 64)
    (pbmt : PtTree.PbmtZero ent.pte) image fixed whole gen era cpu
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs environment -∗
      (cells capacity era cpu (updateAfter rs idx ent response) environment -∗
        RegisterWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (updateValue vpn ent response))) post) -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (afterUpdate vpn idx ent response >>= continuation)) post) := by
  unfold cells
  iintro #Hcert Hcells Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity (footprint environment) (footprint_unique environment)
    image fixed whole gen era cpu rs (afterUpdate vpn idx ent response)
    (fun value after => value = updateValue vpn ent response ∧ after = updateAfter rs idx ent response)
    continuation post (resume_plan environment rs vpn idx ent response bound pbmt) $$ Hcert Hcells
  iintro %value %after %same Hcells
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hcells

end Xv6.Kernel.Sv39Hit
