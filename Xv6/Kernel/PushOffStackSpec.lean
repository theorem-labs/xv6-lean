import Xv6.Kernel.PushOffStackDefs

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec [Platform] : Prop where
  inventory : [instructionIndex .store .ra, instructionIndex .store .s0, instructionIndex .store .s1,
    instructionIndex .load .ra, instructionIndex .load .s0, instructionIndex .load .s1].map Fin.val = [1,2,3,14,15,16]
  storeBody : ∀ slot, body .store slot = execute_STORE (immediate slot) (regidx slot) (.Regidx 2#5) 8
  loadBody : ∀ slot, body .load slot = execute_LOAD (immediate slot) (.Regidx 2#5) (regidx slot) false 8
  storeFactor : ∀ slot, body .store slot = (do
    let value ← rX_bits (regidx slot)
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .store (sp + offset slot) value >>= storeTail)
  loadFactor : ∀ slot, body .load slot = (do
    let sp ← rX_bits (.Regidx 2#5)
    KptMemory.program .load (sp + offset slot) 0#64 >>= loadTail slot)
  storeFalse : storeTail (.Ok false) = pure (.Retire_Success ())
  storeError : ∀ error, storeTail (.Err error) = pure error
  loadError : ∀ slot error, loadTail slot (.Err error) = pure error
  entry : ∀ kind slot control cpu values word,
    PushOffStack.entry control cpu (afterMap kind slot values word) =
      physicalAfter kind slot (PushOffStack.entry control cpu values) word
  other : ∀ kind slot values word key, key ≠ index slot → afterMap kind slot values word key = values key
  sp : ∀ kind slot cpu values word,
    HartTp.rget cpu (afterMap kind slot values word) 2#5 = HartTp.rget cpu values 2#5
  address : ∀ kind slot cpu values word other,
    PushOffStack.address cpu (afterMap kind slot values word) other = PushOffStack.address cpu values other
  anchored : ∀ cpu values entrySP slot, StackReady cpu values entrySP →
    PushOffStack.address cpu values slot = KernelStack.paStk entrySP (ordinal slot)
  footprintUnique : ∀ s slot, RegisterFootprint.Unique (footprint s slot) ∧ RegisterFootprint.Unique (bareFootprint s slot)
  footprintCounts : ∀ s slot, (footprint s slot).length = 7 ∧ (bareFootprint s slot).length = 10 ∧
    (remainderFootprint s slot).length = 43
  footprintMembers : ∀ s slot cell, cell ∈ footprint s slot → cell ∈ MycpuRegimeShell.footprint s
  ambient : ∀ control cpu values, Config control → SupervisorBits.MsFacts (control .mstatus) →
    KptMemory.Ambient (PushOffStack.entry control cpu values)

/-- Actual source word/stack ownership funds both the physical access and
its value-polymorphic restoration; these are implementation obligations. -/
structure ResourceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  identityWord : ∀ era ξ va old,
    iprop(KernelDatum.word capacity.translation era .identity ξ va (.own 1) old ⊢
      ⌜TsoContextWord.Aligned va ∧ SupervisorPhysical.RamRange va 8⌝ ∗
      TsoContextReadWP.wordPointsto capacity.machine era ξ va (.own 1) old ∗ closeIdentity capacity era ξ va)
  frameFour : ∀ era tier ξ entrySP,
    iprop(KernelStack.own capacity.translation era tier ξ entrySP 4 ⊣⊢ ∃ words gap,
      savedWords capacity era tier ξ entrySP words ∗
      KernelDatum.word capacity.translation era tier ξ (KernelStack.paStk entrySP 4) (.own 1) gap)

/-- Six normalized instruction bodies over actual Bare/KPT ownership. This
is the disabled-SIE common packet boundary, not source prologue migration,
fetch/decode, a cycle, or a full push_off function. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body : ∀ s control values, Config control → ∀ regime tier,
    MycpuRegimeShell.Admits regime tier → ∀ kind slot ξ old rr,
    ∀ image fixed whole gen era cpu (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values s -∗ TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) (.own 1) old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values s kind slot tier ξ old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffStack.body kind slot >>= continuation)) post)

end Xv6.Kernel.PushOffStack
