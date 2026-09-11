import MachCSL.Logic.TsoContextBytesProofs
import MachCSL.Logic.TsoContextLink

namespace MachCSL.Logic.TsoContextBytes
open Iris
abbrev registry := TsoContext.registry
abbrev registryCapacity := TsoContext.registryCapacity
theorem registrySpec : Spec registryCapacity := actual registryCapacity
end MachCSL.Logic.TsoContextBytes
