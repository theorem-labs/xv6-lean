import Xv6.Kernel.BareJalSourceResources
import Xv6.Kernel.BareJalLink
namespace Xv6.Kernel.BareJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors}

theorem guard_intro (addresses : List (BitVec 64)) (done : List Nat → IProp GF) :
    iprop((∀ views, done views) ⊢ BareJalFetch.guardReads addresses done) := by
  induction addresses generalizing done with
  | nil =>
    simp only [BareJalFetch.guardReads,List.foldr_nil]
    iintro Hdone
    iapply Hdone $$ %([])
  | cons address rest ih =>
    rw [BareJalFetch.guardReads_cons]
    iintro Hdone !> %view
    iapply ih
    iintro %views
    iapply Hdone $$ %(view :: views)

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_cycle image fixed whole gen era cpu ξ file available pc imm tick extra post
    (even : KptJal.TargetEven pc imm) :
    iprop(⊢ input capacity fixed gen era cpu ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro Hinput Hfinish
  ihave ⟨%control,%rr,%config,%ambient,Hresources⟩ := open_entry capacity fixed gen era cpu ξ file available pc imm extra $$ Hinput
  ihave ⟨#Hcert,Hresources⟩ := certificate capacity fixed gen era cpu ξ file available control pc imm rr extra $$ Hresources
  iunfold resources at Hresources
  icases Hresources with ⟨Hpacket,Hcode,Hrun,Hresv,Hkept⟩
  iapply (BareJal.nativeSpec capacity).cycle control file config pc imm ambient.pc_eq even
    ξ rr tick image fixed whole gen era cpu (kept capacity fixed gen era cpu ξ file available extra) post
    $$ Hcert Hpacket Hcode Hrun Hresv Hkept
  iunfold BareJal.cycleFinish
  iunfold BareJalFetch.guards
  iapply guard_intro
  iintro %views %after %completed !> %nextTick Hresources
  iunfold BareJal.cycleResources at Hresources
  iunfold BareJal.fetchResources at Hresources
  icases Hresources with ⟨Hpacket,Hcode,Hrun,Hresv,Hreceipts,Hkept⟩
  ihave Hkept := (kept_update capacity fixed gen era cpu ξ file available pc extra).mp $$ Hkept
  ihave Hresources : resources capacity fixed gen era cpu ξ (afterFile pc file) available after pc imm none extra $$
      [Hpacket Hcode Hrun Hresv Hkept]
  · unfold resources
    iframe
  ihave Hsource := close_entry capacity fixed gen era cpu ξ (afterFile pc file) available after pc
    (KptJal.target pc imm) imm none extra (boundary pc imm control after ambient.toBoundary completed) $$ Hresources
  iunfold finish at Hfinish
  iapply Hfinish $$ Hsource %nextTick

theorem actual : Spec capacity := ⟨wp_cycle capacity⟩
end Xv6.Kernel.BareJalSource
