import MachCSL.Logic.TsoPinnedWriteWPProofs

namespace MachCSL.Logic.TsoPinnedWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- All subordinate physical, timestamp, history, reservation and event
contracts are proved native laws; no caller-supplied payer is required. -/
theorem nativeSpec : Spec capacity := actual capacity

/-- General present-payload V1 builtin, retaining every request field. The
absent-payload pure path is not substituted for an actual write. -/
theorem wp_write_builtin image fixed whole gen era cpu (req : MemoryWriteWP.WriteRequest 8)
    (reserved physical new : BitVec 64) floors sets (k : MemoryWriteWP.WriteResult → SailM Unit) post
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (exclusive : accessExclusive req.access_kind = true)
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      pinWindow capacity era req.pa physical (.own 1) floors sets -∗
      continuation capacity image fixed whole gen era cpu req.pa new floors sets (k (.Ok none)) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write req >>= k)) post) := by
  have emit : (_root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write req >>= k : SailM Unit) =
      .impure (.writeMem 8 req) k := by
    unfold _root_.Sail.ConcurrencyInterfaceV1.Free.PreSail.sail_mem_write
    rw [present]
    rfl
  rw [emit]
  exact wp_write capacity image fixed whole gen era cpu req reserved physical new floors sets k post
    present ram exclusive members

end MachCSL.Logic.TsoPinnedWriteWP
