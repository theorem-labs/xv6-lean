import Xv6.Kernel.HartTpDefs

namespace Xv6.Kernel.HartTp
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

/-- Exact representation and actual generated read correspondence. -/
structure PureSpec : Prop where
  zero : ∀ index, physical index = none ↔ index = 0#5
  physicalInjective : ∀ a b r s, physical a = some r → physical b = some s →
    r.val = s.val → a = b
  allIndices : ∀ index, index ∈ indices
  uniqueIndices : indices.Nodup
  uniquePhysical : physicalKeys.Nodup
  physicalCount : physicalKeys.length = 31
  readProgram : ∀ index,
    LeanPaperStock.Functions.rX_bits (.Regidx index) = readAt index
  pinnedTp : ∀ cpu values, rget cpu values tp = hartWord cpu
  readOther : ∀ cpu values index, index ≠ tp → rget cpu values index = values index
  hartIndependent : ∀ a b values index, index ≠ tp → rget a values index = rget b values index
  pinId : ∀ cpu values, values tp = hartWord cpu → pin cpu values = values
  pinSet : ∀ cpu values index value, index ≠ tp →
    set (pin cpu values) index value = pin cpu (set values index value)

/-- Source ownership accessors. No premise supplies a register or program
correctness oracle, and the remainder is the explicit other-key resource. -/
structure Spec {GF : BundledGFunctors} (capacity : Registers.Capacity GF) : Prop where
  lookupSplit : ∀ registerName values index,
    iprop(file capacity registerName values ⊣⊢
      pointsto capacity registerName index (.own 1) (values index) ∗
      remainder capacity registerName values index)
  replace : ∀ registerName values index value,
    iprop(⊢ pointsto capacity registerName index (.own 1) value -∗
      remainder capacity registerName values index -∗
      file capacity registerName (set values index value))
  lookup : ∀ registerName values index,
    iprop(⊢ file capacity registerName values -∗
      pointsto capacity registerName index (.own 1) (values index) ∗
      (pointsto capacity registerName index (.own 1) (values index) -∗
        file capacity registerName values))
  update : ∀ registerName values index,
    iprop(⊢ file capacity registerName values -∗
      pointsto capacity registerName index (.own 1) (values index) ∗
      (∀ value, pointsto capacity registerName index (.own 1) value -∗
        file capacity registerName (set values index value)))
  zeroValue : ∀ registerName values,
    iprop(⊢ file capacity registerName values -∗ ⌜values 0#5 = 0#64⌝)
  pinnedLookup : ∀ era cpu values index,
    iprop(⊢ pinnedFile capacity era cpu values -∗
      pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) ∗
      (pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) -∗
        pinnedFile capacity era cpu values))
  pinnedUpdate : ∀ era cpu values index, index ≠ tp →
    iprop(⊢ pinnedFile capacity era cpu values -∗
      pointsto capacity (era.registers cpu) index (.own 1) (rget cpu values index) ∗
      (∀ value, pointsto capacity (era.registers cpu) index (.own 1) value -∗
        pinnedFile capacity era cpu (set values index value)))
  tpAccessor : ∀ era cpu values,
    iprop(⊢ pinnedFile capacity era cpu values -∗
      Registers.regPointsto capacity (era.registers cpu) .x4 (.own 1) (hartWord cpu) ∗
      (Registers.regPointsto capacity (era.registers cpu) .x4 (.own 1) (hartWord cpu) -∗
        pinnedFile capacity era cpu values))
  actualTp : ∀ era cpu values registers,
    iprop(⊢ Registers.regInterpAt capacity (era.registers cpu) registers -∗
      pinnedFile capacity era cpu values -∗ ⌜registers .x4 = hartWord cpu⌝)

end Xv6.Kernel.HartTp
