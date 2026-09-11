import Xv6.Kernel.MycpuCallSconfKptSpec
import Xv6.Kernel.KptJalSconfSpec
import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.MycpuSconfKptLink

namespace Xv6.Kernel.MycpuCallSconfKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_call (jal : KptJalSconf.Spec capacity) (code : KptJal.ResourceSpec capacity)
    (pure : PureSpec) image fixed whole gen era cpu ξ original available pc imm tick (frame : IProp GF) post
    (enough : 2 ≤ available) (target : KptJal.target pc imm = MycpuSconfKpt.entryPC) :
    iprop(⊢ input capacity fixed gen era cpu ξ original available pc imm frame -∗
      finish capacity image fixed whole gen era cpu ξ original available pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨Hsource,Hcode,Htext,Hpma,Hframe⟩ Hfinish
  ihave %aligned := code.alignment era .full pc imm $$ Hcode
  let jalFrame : IProp GF := iprop(KernelTextImage.text capacity.translation era .identity ∗ frame)
  iapply jal.cycle image fixed whole gen era cpu ξ original available pc imm tick jalFrame post
    (pure.targetEven pc imm target) $$ [Hsource Hcode Htext Hpma Hframe] [Hfinish]
  · unfold KptJalSconf.input
    dsimp only [jalFrame]
    iframe
  · iunfold KptJalSconf.finish
    iintro Hreturned %bodyTick
    iunfold KptJalSconf.restored at Hreturned
    icases Hreturned with ⟨Hsource,Hcode,Hpma,Hframe⟩
    isimp only [jalFrame] at Hframe
    icases Hframe with ⟨Htext,Hframe⟩
    isimp only [target] at Hsource
    let bodyFrame : IProp GF := iprop(KptJal.code capacity era .full pc imm ∗ frame)
    iapply (MycpuSconfKpt.nativeSpec capacity).function image fixed whole gen era cpu ξ
      (KptJal.afterValues pc original) available bodyTick bodyFrame post enough
      $$ [Hsource Hcode Htext Hpma Hframe] [Hfinish]
    · unfold MycpuSconfKpt.input
      dsimp only [bodyFrame]
      iframe
    · iunfold MycpuSconfKpt.finish
      iintro %after %result Hreturned %nextTick
      iunfold MycpuSconfKpt.restored at Hreturned
      icases Hreturned with ⟨Hsource,Htext,Hpma,Hframe⟩
      isimp only [bodyFrame] at Hframe
      icases Hframe with ⟨Hcode,Hframe⟩
      isimp only [pure.returnPC cpu pc original aligned] at Hsource
      iunfold finish at Hfinish
      iapply Hfinish $$ %after %(pure.result cpu pc original after result)
        [Hsource Hcode Htext Hpma Hframe] %nextTick
      iunfold restored
      iframe

theorem actual (jal : KptJalSconf.Spec capacity) (code : KptJal.ResourceSpec capacity)
    (pure : PureSpec) : Spec capacity := ⟨wp_call capacity jal code pure⟩

end Xv6.Kernel.MycpuCallSconfKpt
