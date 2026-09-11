import MachCSL.Logic.EventPlanDefs

/-! First actual free-tree boundary of an existing plan. This is a proof
view, not an interpreter or an alternative operational semantics. -/
namespace MachCSL.Logic.EventPlanHead
open MachCSL.Memory MachCSL.Machine EventPlan

/-- Each constructor indexes the original program by its exact pure value
or first event and retains an ordinary Plan for its actual continuation.
Pin results are universal, and relation-indexed branches assert no existence
of successors. Code-read success retains the exact `none` metadata. -/
inductive Head (reads : EventWP.ReadAllowed) (rel : Relations S) :
    RegisterFile → Option Reservation → S → SailM α →
      (α → RegisterFile → Option Reservation → S → Prop) → Prop where
  | pure {rs rr s value Q} (good : Q value rs rr s) :
      Head reads rel rs rr s (.pure value) Q
  | readOwned {rs rr s r k Q} (owned : EventWP.IsOwned r)
      (rest : Plan reads rel rs rr s (k (rs r)) Q) :
      Head reads rel rs rr s (.impure (.readReg r) k) Q
  | readPin {rs rr s r k Q} (pin : EventWP.IsPin r)
      (rest : ∀ value : RegisterType r, Plan reads rel rs rr s (k value) Q) :
      Head reads rel rs rr s (.impure (.readReg r) k) Q
  | writeOwned {rs rr s r value k Q} (owned : EventWP.IsOwned r)
      (rest : Plan reads rel (Sail.Registers.write rs r value) rr s (k ()) Q) :
      Head reads rel rs rr s (.impure (.writeReg r value) k) Q
  | codeRead {rs rr s n req word k Q}
      (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
      (allowed : reads n req word)
      (rest : Plan reads rel rs rr s (k (.Ok (word, none))) Q) :
      Head reads rel rs rr s (.impure (.readMem n req) k) Q
  | plain {rs rr s n req k Q}
      (enabled : rel.plainEnabled s n req) (ram : deviceAddress req.pa = false)
      (kind : accessExclusive req.access_kind = false)
      (rest : ∀ word next, rel.plain s n req word next →
        Plan reads rel rs rr next (k (.Ok (word, none))) Q) :
      Head reads rel rs rr s (.impure (.readMem n req) k) Q
  | exclusive {rs rr s n req k Q}
      (enabled : rel.exclusiveEnabled s n req) (ram : deviceAddress req.pa = false)
      (kind : accessExclusive req.access_kind = true)
      (rest : ∀ word next, rel.exclusive s n req word next →
        Plan reads rel rs (some (snapshot req.pa n word)) next (k (.Ok (word, none))) Q) :
      Head reads rel rs rr s (.impure (.readMem n req) k) Q
  | write {rs rr s n req value k Q}
      (enabled : rel.writeEnabled s n req value) (present : req.value = some value)
      (ram : deviceAddress req.pa = false) (mode : WriteMode n req rr)
      (eligible : rel.writeModeEnabled s rr n req value mode)
      (rest : ∀ next, rel.write s n req value next →
        Plan reads rel rs none next (k (.Ok none)) Q) :
      Head reads rel rs rr s (.impure (.writeMem n req) k) Q
  | barrier {rs rr s kind k Q} (enabled : rel.barrierEnabled s kind)
      (rest : ∀ next, rel.barrier s kind next → Plan reads rel rs rr next (k ()) Q) :
      Head reads rel rs rr s (.impure (.barrier kind) k) Q

end MachCSL.Logic.EventPlanHead
