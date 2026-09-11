import Xv6.Kernel.PushOffCsrSpec

namespace Xv6.Kernel.PushOffCsr
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000

theorem instruction : PushOffCode.normalized index = .CSRImm (0x100#12, 2#5, .Regidx 15#5, .CSRRC) := rfl

theorem after_entry control cpu values :
    entry control cpu (afterValues control values) = after (entry control cpu values) := by
  funext r
  cases r <;> rfl

theorem other control values key (different : key ≠ 15#5) :
    afterValues control values key = values key := by
  simp [afterValues, HartTp.set, different]

theorem zero control values : afterValues control values 0#5 = values 0#5 :=
  other control values _ (by decide)

theorem pinned_tp control cpu values :
    HartTp.rget cpu (afterValues control values) HartTp.tp = HartTp.hartWord cpu := by
  simp [HartTp.rget, HartTp.pin, HartTp.set]

end Xv6.Kernel.PushOffCsr
