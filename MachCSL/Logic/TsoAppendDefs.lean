import MachCSL.Logic.TsoInterpDefs

/-! Concrete timestamp-map replacement used by the source ledger_store_ok.
Std.ExtTreeMap union is right-biased, so the replacement is the right operand. -/
namespace MachCSL.Logic.Tso
open MachCSL.Memory

def storeTimestamps (newBytes : AddressMap Byte) (time : Nat) : AddressMap TimestampElem :=
  newBytes.map (fun _ _ => (time, payNone))

def appendTimestamps (old : AddressMap TimestampElem) (newBytes : AddressMap Byte)
    (oldLength : Nat) : AddressMap TimestampElem :=
  old ∪ storeTimestamps newBytes (oldLength + 1)

end MachCSL.Logic.Tso
