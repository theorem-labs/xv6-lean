import MachCSL.Logic.MemoryWriteWPDefs
import MachCSL.Logic.MemoryExclusiveWPSpec
import MachCSL.Logic.TsoStoreSpec
import MachCSL.Logic.ReservationSpec

namespace MachCSL.Logic.MemoryWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Contracts {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  store : TsoStore.StoreSpec (storeCapacity capacity)
  views : Tso.Views.ViewsSpec capacity.era.views
  reservations : Reservations.ReservationSpec capacity.era.reservations
  exclusive : MemoryExclusiveWP.MemoryExclusiveWPSpec capacity

structure MemoryWriteWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  write : ∀ image fixed whole gen era cpu n (req : WriteRequest n) value k rr post,
    req.value = some value → deviceAddress req.pa = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      writePremise capacity image fixed whole gen era cpu n req value k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post)
  conditional : ∀ image fixed whole gen era cpu n (req : WriteRequest n) old value k post,
    req.value = some value → deviceAddress req.pa = false → n < 2 ^ 64 →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n old)) -∗
      conditionalPremise capacity image fixed whole gen era cpu n req old value k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post)
  ledger : ∀ image fixed whole gen era cpu n (req : WriteRequest n) value k rr post,
    req.value = some value → deviceAddress req.pa = false → n ≤ 2 ^ 64 →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ledgerPremise capacity image fixed whole gen era cpu n req value k (fun _ => True) post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post)
  conditionalLedger : ∀ image fixed whole gen era cpu n (req : WriteRequest n) old value k post,
    req.value = some value → deviceAddress req.pa = false → n < 2 ^ 64 →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n old)) -∗
      ledgerPremise capacity image fixed whole gen era cpu n req value k
        (fun g => readBytes g.memory req.pa n = some old) post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.writeMem n req) k)) post)

end MachCSL.Logic.MemoryWriteWP
