import Xv6.Kernel.CalleeSavedDefs

namespace Xv6.Kernel.CalleeSaved
open MachCSL.Machine

structure Spec : Prop where
  reflexive : ∀ rs, Preserved rs rs
  transitive : ∀ a b c, Preserved a b → Preserved b c → Preserved a c
  caller_write : ∀ a b r value, r ∉ registers → Preserved a b →
    Preserved a (MachCSL.Sail.Registers.write b r value)
  writes : ∀ rs writes, Restores rs writes → Preserved rs (applyWrites writes rs)

end Xv6.Kernel.CalleeSaved
