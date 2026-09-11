import MachCSL.Logic.TsoReadDefs

/-! Timestamp ownership for ordinary latest-value reads. Payloads need not be
absent or discarded; the caller must separately supply a sufficient view bound. -/
namespace MachCSL.Logic.TsoReadAt
open Iris Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors}

def timestampWindow (capacity : Tso.Capacity GF) (name : GName) (a : PhysicalAddress)
    (n : Nat) (dq : DFrac) (time : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range n, ∃ pay : Tso.Payload,
    Tso.timestampElem capacity name dq (addressAdd a j) (time, pay))

end MachCSL.Logic.TsoReadAt
