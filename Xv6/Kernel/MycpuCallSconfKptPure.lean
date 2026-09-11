import Xv6.Kernel.MycpuCallSconfKptSpec
import Xv6.Kernel.KptJalSconfPure
import Xv6.Kernel.KptFetchPureProofs

namespace Xv6.Kernel.MycpuCallSconfKpt
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem targetEven pc imm (target : KptJal.target pc imm = MycpuSconfKpt.entryPC) :
    KptJal.TargetEven pc imm := by
  unfold KptJal.TargetEven
  rw [target]
  rfl

theorem returnPC cpu pc original (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true) :
    MycpuSconfKpt.returnPC cpu (KptJal.afterValues pc original) = KptJal.link pc := by
  have linkAligned : is_aligned_vaddr (.Virtaddr (KptJal.link pc)) 2 = true := by
    rw [KptFetchHalf.aligned_iff] at *
    simp only [KptJal.link, Sail.BitVec.addInt, BitVec.toNat_add, BitVec.toNat_ofInt]
    have bound := pc.isLt
    omega
  have low := KptFetch.bit0 (KptJal.link pc) linkAligned
  change MycpuReturn.retPC (KptJal.link pc) = KptJal.link pc
  unfold MycpuReturn.retPC
  apply BitVec.eq_of_getLsbD_eq
  intro index
  by_cases zero : index = 0
  · subst index
    have bit : (KptJal.link pc).getLsbD 0 = false := by
      simpa [Sail.BitVec.access] using congrArg (fun value : BitVec 1 => value.getLsbD 0) low
    simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    simp
    exact bit
  · simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    simp
    intro bound _
    change (~~~ (1#64)).getLsbD index = true
    rw [BitVec.getLsbD_not, BitVec.getLsbD_one]
    simp [bound, zero]


theorem result cpu pc original after (done : Result cpu (KptJal.afterValues pc original) after) :
    Result cpu original after := by
  refine ⟨?_,done.2⟩
  intro index member
  exact (done.1 index member).trans (KptJalSconf.saved pc original index member)

theorem pureSpec : PureSpec := ⟨targetEven,returnPC,result⟩

end Xv6.Kernel.MycpuCallSconfKpt
