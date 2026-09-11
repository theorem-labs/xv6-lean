import MachCSL.Logic.TsoContextBytesStoreProofs

namespace MachCSL.Logic.TsoContextBytesStore
open Iris

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

end MachCSL.Logic.TsoContextBytesStore
