import Xv6.Kernel.MycpuCallSconfSpec
import Xv6.Kernel.MycpuCallKptSourcePure
import Xv6.Kernel.JalSconfSpec
import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.MycpuSconfLink

namespace Xv6.Kernel.MycpuCallSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- Private composition. The final Link supplies the actual JAL and code
implementations; the function body is already the closed MycpuSconf rule. -/
theorem wp_call (jal : JalSconf.Spec capacity) (code : KptJal.ResourceSpec capacity)
    image fixed whole gen era cpu tier ξ original available pc imm tick extra post
    (enough : 2 ≤ available) (target : KptJal.target pc imm = MycpuSconf.entryPC) :
    iprop(⊢ input capacity fixed gen era cpu tier ξ original available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨Hopened,Hcode,Htext,Hpma,Hextra⟩ Hfinish
  ihave %aligned := code.alignment era tier pc imm $$ Hcode
  let jalFrame : IProp GF := iprop(KernelTextImage.text capacity.translation era .identity ∗ extra)
  iapply jal.cycle image fixed whole gen era cpu tier ξ original available pc imm tick jalFrame post
    (MycpuCallKptSource.targetEven pc imm target) $$ [Hopened Hcode Htext Hpma Hextra] [Hfinish]
  · unfold JalSconf.input
    dsimp only [jalFrame]
    iframe
  · iunfold JalSconf.finish
    iintro Hreturned %bodyTick
    iunfold JalSconf.restored at Hreturned
    icases Hreturned with ⟨Hsource,Hcode,Hpma,Hframe⟩
    isimp only [jalFrame] at Hframe
    icases Hframe with ⟨Htext,Hextra⟩
    isimp only [target] at Hsource
    let bodyFrame : IProp GF := iprop(KptJal.code capacity era tier pc imm ∗ extra)
    iapply (MycpuSconf.nativeSpec capacity).function image fixed whole gen era cpu tier ξ
      (KptJal.afterValues pc original) available bodyTick bodyFrame post enough
      $$ [Hsource Hcode Htext Hpma Hextra] [Hfinish]
    · unfold MycpuSconf.input
      dsimp only [bodyFrame]
      iframe
    · iunfold MycpuSconf.finish
      iintro %after %good Hreturned %nextTick
      iunfold MycpuSconf.restored at Hreturned
      icases Hreturned with ⟨Hsource,Htext,Hpma,Hframe⟩
      isimp only [bodyFrame] at Hframe
      icases Hframe with ⟨Hcode,Hextra⟩
      isimp only [MycpuCallKptSource.returnPC cpu pc original aligned] at Hsource
      iunfold finish at Hfinish
      iapply Hfinish $$ %after %(MycpuCallKptSource.result cpu pc original after good)
        [Hsource Hcode Htext Hpma Hextra] %nextTick
      iunfold restored
      iframe

theorem actual (jal : JalSconf.Spec capacity) (code : KptJal.ResourceSpec capacity) : Spec capacity :=
  ⟨wp_call capacity jal code⟩

end Xv6.Kernel.MycpuCallSconf
