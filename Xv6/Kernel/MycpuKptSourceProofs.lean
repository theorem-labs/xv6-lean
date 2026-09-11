import Xv6.Kernel.MycpuKptSourceResources
import Xv6.Kernel.MycpuSconfKptPure
import Xv6.Kernel.MycpuKptSpec
import Xv6.Kernel.MycpuKptEntryLink
import Xv6.Kernel.KernelTextImageLink

namespace Xv6.Kernel.MycpuKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- The final Link supplies the actual full-function implementation and its
phase/result lemmas; this composition never supplies an instruction oracle. -/
theorem wp_function (functionSpec : MycpuKpt.Spec capacity) (phaseSpec : MycpuKpt.PureSpec)
    image fixed whole gen era cpu tier ξ original available tick (frame : IProp GF) post
    (enough : 2 ≤ available) :
    iprop(⊢ sourceInput capacity fixed gen era cpu tier ξ original available frame -∗
      finish capacity image fixed whole gen era cpu tier ξ original available frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold sourceInput
  iintro ⟨Hsource,#Htext,#Hpma,Hframe⟩ Hfinish
  ihave Hfull := (KernelTextImage.nativeSpec capacity.translation).mono era .identity tier (by cases tier <;> trivial) $$ Htext
  ihave ⟨_,Hcode⟩ := (KernelTextImage.nativeSpec capacity.translation).mycpu era tier capacity rfl $$ Hfull
  ihave Hentry : input capacity fixed gen era cpu tier ξ original available $$ [Hsource Hcode]
  · unfold input
    iframe Hsource Hpma Hcode
  ihave ⟨%root,%initial,%old,%rr,%config,%boundary,Hresources⟩ :=
    (resourceSpec capacity).open_entry fixed gen era cpu tier ξ original available enough $$ Hentry
  ihave ⟨#Hcert,Hresources⟩ := (resourceSpec capacity).certificate fixed gen era cpu tier ξ
    (sp original) available root initial original old rr $$ Hresources
  iunfold resources at Hresources
  icases Hresources with ⟨Hpacket,Hcode,Hrun,Hpair,Hresv,HentryFrame⟩
  let extra : IProp GF := iprop(MycpuKptSource.frame capacity fixed gen era cpu tier ξ
    (sp original) available ∗ frame)
  have entrySP : MycpuKpt.entrySP cpu original = sp original := rfl
  iapply functionSpec.function MycpuRegimeShell.sourceShares initial original config boundary.pc_eq
    old tier ξ rr tick image fixed whole gen era cpu KptGhost.kptN root extra post
    $$ Hcert [Hpacket Hcode Hrun Hpair Hresv HentryFrame Hframe] [Hfinish]
  · iunfold MycpuKpt.resources
    simp only [extra, entrySP]
    iframe
  · iunfold MycpuKpt.finish
    iintro %after %values %trace %good Hresources Hreceipts %nextTick
    iunfold MycpuKpt.resources at Hresources
    icases Hresources with ⟨Hpacket,Hcode,Hrun,Hpair,Hresv,Hextra⟩
    isimp only [extra] at Hextra
    icases Hextra with ⟨HentryFrame,Hframe⟩
    have sourceResult := MycpuSconfKpt.result initial original cpu after values good.1
    have restoredSP := MycpuSconfKpt.stack initial original cpu after values good.1
    have afterBoundary := phaseSpec.boundary initial original cpu after values good.1 boundary
    ihave Hentry : resources capacity fixed gen era cpu tier ξ (sp original)
        available root after values (MycpuKpt.savedWords cpu original) none $$
        [Hpacket Hcode Hrun Hpair Hresv HentryFrame]
    · unfold resources
      isimp only [entrySP] at Hpair
      iframe
    ihave Hrestored := (resourceSpec capacity).close_entry fixed gen era cpu tier ξ
      (sp original) available root after values (MycpuKpt.savedWords cpu original) none
      (returnPC cpu original) enough restoredSP afterBoundary $$ Hentry
    iunfold restored at Hrestored
    icases Hrestored with ⟨Hsource,Hpma,Hcode⟩
    iunfold finish at Hfinish
    iapply Hfinish $$ %values %sourceResult [Hsource Hpma Hframe] %nextTick
    iunfold sourceRestored
    iframe Hsource Htext Hpma Hframe

theorem actual (functionSpec : MycpuKpt.Spec capacity) (phaseSpec : MycpuKpt.PureSpec) : Spec capacity :=
  ⟨wp_function capacity functionSpec phaseSpec⟩

end Xv6.Kernel.MycpuKptSource
