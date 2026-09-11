import MachCSL.Logic.TsoPinnedWriteWPDefs

namespace MachCSL.Logic.TsoPinnedWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  agreement : ∀ fixed g gen era cpu a (reserved physical : BitVec 64) dq floors sets,
    ThreadLive g gen →
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot a 8 reserved)) -∗
      pinWindow capacity era a physical dq floors sets -∗ ⌜physical = reserved⌝)
  write : ∀ image fixed whole gen era cpu (req : MemoryWriteWP.WriteRequest 8)
      (reserved physical new : BitVec 64) floors sets (k : MemoryWriteWP.WriteResult → SailM Unit) post,
    req.value = some new → deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    (∀ j, j < 8 → nthByte new j ∈ sets j) →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      pinWindow capacity era req.pa physical (.own 1) floors sets -∗
      continuation capacity image fixed whole gen era cpu req.pa new floors sets (k (.Ok none)) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem 8 req) k)) post)
  writeRam : ∀ image fixed whole gen era cpu a (reserved physical new : BitVec 64) floors sets
      (k : Bool → SailM Unit) post,
    deviceAddress a = false → (∀ j, j < 8 → nthByte new j ∈ sets j) →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot a 8 reserved)) -∗
      pinWindow capacity era a physical (.own 1) floors sets -∗
      continuation capacity image fixed whole gen era cpu a new floors sets (k true) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (LeanPaperStock.Functions.write_ram .Write_RISCV_conditional
          (.Physaddr a) 8 new () >>= k)) post)

end MachCSL.Logic.TsoPinnedWriteWP
