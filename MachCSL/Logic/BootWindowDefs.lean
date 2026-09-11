import MachCSL.Logic.JalBootResourcesMap
import MachCSL.Logic.TsoStoreProofs

namespace MachCSL.Logic.BootWindow
open Iris Iris.Std Iris.BI MachCSL.Memory

def keys (a : PhysicalAddress) (n : Nat) : List PhysicalAddress :=
  (List.range n).map (addressAdd a)

def mapBytes {GF : BundledGFunctors} (capacity : Tso.Capacity GF) (γ : GName)
    (m : Tso.AddressMap Byte) : IProp GF :=
  bigSepM (M := Tso.AddressMap) (fun a v => Tso.byteElem capacity γ (.own 1) a v) m

def mapTimes {GF : BundledGFunctors} (capacity : Tso.Capacity GF) (γ : GName)
    (m : Tso.AddressMap Tso.TimestampElem) : IProp GF :=
  bigSepM (M := Tso.AddressMap) (fun a v => Tso.timestampElem capacity γ (.own 1) a v) m

def timeWindow {GF : BundledGFunctors} (capacity : Tso.Capacity GF) (γ : GName)
    (a : PhysicalAddress) (n t : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    Tso.timestampElem capacity γ (.own 1) (addressAdd a j) (t, Tso.payNone))

structure Word where
  address : PhysicalAddress
  size : Nat
  value : BitVec (8 * size)

def wordKeys (words : List Word) : List PhysicalAddress :=
  words.flatMap (fun w => keys w.address w.size)

end MachCSL.Logic.BootWindow
