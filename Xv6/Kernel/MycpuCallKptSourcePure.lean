import Xv6.Kernel.MycpuCallKptSourceSpec
import Xv6.Kernel.MycpuCallSconfKptPure

namespace Xv6.Kernel.MycpuCallKptSource
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem targetEven pc imm (target : KptJal.target pc imm = MycpuSconf.entryPC) :
    KptJal.TargetEven pc imm := MycpuCallSconfKpt.targetEven pc imm target

theorem returnPC cpu pc original (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true) :
    MycpuSconf.returnPC cpu (KptJal.afterValues pc original) = KptJal.link pc :=
  MycpuCallSconfKpt.returnPC cpu pc original aligned

theorem result cpu pc original after (done : Result cpu (KptJal.afterValues pc original) after) :
    Result cpu original after := MycpuCallSconfKpt.result cpu pc original after done

theorem pureSpec : PureSpec := ⟨targetEven,returnPC,result⟩

end Xv6.Kernel.MycpuCallKptSource
