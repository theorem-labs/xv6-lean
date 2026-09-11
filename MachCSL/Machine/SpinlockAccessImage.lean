import MachCSL.Machine.SpinlockAccessInstructions
import MachCSL.Machine.SpinlockAccessLoadStore

namespace MachCSL.Machine.SpinlockAccess
open LeanPaperStock.Functions

/-- These equalities connect the access plans to the five actual decoded
instructions in the image. Fetch and decoder certificates remain separate. -/
theorem image_amo [Platform] : execute (SpinlockDecode.instruction ⟨7, by decide⟩) =
    execute_AMO .AMOSWAP true false (.Regidx 15#5) (.Regidx 10#5) 4 (.Regidx 15#5) := rfl

theorem image_load [Platform] : execute (SpinlockDecode.instruction ⟨10, by decide⟩) =
    execute_LOAD 4#12 (.Regidx 10#5) (.Regidx 16#5) false 4 := rfl

theorem image_store [Platform] : execute (SpinlockDecode.instruction ⟨12, by decide⟩) =
    execute_STORE 4#12 (.Regidx 16#5) (.Regidx 10#5) 4 := rfl

theorem image_fence [Platform] : execute (SpinlockDecode.instruction ⟨13, by decide⟩) =
    execute_FENCE 0#4 3#4 1#4 (.Regidx 0#5) (.Regidx 0#5) := rfl

theorem image_unlock [Platform] : execute (SpinlockDecode.instruction ⟨14, by decide⟩) =
    execute_STORE 0#12 (.Regidx 0#5) (.Regidx 10#5) 4 := rfl

end MachCSL.Machine.SpinlockAccess
