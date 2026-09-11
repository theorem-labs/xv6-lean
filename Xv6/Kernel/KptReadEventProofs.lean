import Xv6.Kernel.KptReadEventPower

namespace Xv6.Kernel.KptReadEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)
include ownership

/-- Discharge the native all-view read premise by a fresh, fully closed
invariant opening at the actual event. -/
theorem wp_read image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0 level
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (req : MemoryReadWP.ReadRequest 8)
    (location : req.pa = address tree vpn p2 p1 level)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    B rr (continuation : MemoryReadWP.ReadResult 8 → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
      KptShared.bound capacity era B -∗ TsoPinnedReadWP.credential capacity.machine era cpu B -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜ReadFact (reference p2 p1 p0 level) word⌝ -∗
        KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
        KptShared.bound capacity era B -∗ TsoPinnedReadWP.credential capacity.machine era cpu B -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (.impure (.readMem 8 req) continuation)) post) := by
  iintro #Hcert #Hshared #Hsnapshot #Hbound #Hcredential Hresv Hcontinue
  iapply MemoryReadWP.wp_ram_read_plain_ex capacity.machine image fixed whole gen era cpu 8 req continuation
    (ReadFact (reference p2 p1 p0 level)) post ram plain $$ Hcert
  iunfold MemoryReadWP.plainPremise
  iintro %g %live Hp
  imod power_reads capacity ownership fixed g gen era cpu live N root tree vpn p2 p1 p0 level mapped B
    $$ Hp Hcert Hshared Hsnapshot Hbound Hcredential with ⟨Hp,%reads⟩
  iapply fupd_mask_intro (E2 := ∅) (by intro x _; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    intro view lower _upper
    rw [location]
    exact reads view lower
  · iintro !>
    imod Hback
    imodintro
    iframe Hp
    iintro %view %word %_lower %_upper %_read %relation Hreceipt
    iapply Hcontinue $$ %view %word %relation Hshared Hsnapshot Hbound Hcredential Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_read capacity ownership⟩

end Xv6.Kernel.KptReadEvent
