import MachCSL.Logic.MemoryExclusiveWPDefs

namespace MachCSL.Logic.MemoryExclusiveWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure MemoryExclusiveWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  heldSubmap : ∀ fixed g gen era cpu r, ThreadLive g gen →
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some r) -∗
      ⌜Submap r g.memory⌝)
  heldSnapshot : ∀ fixed g gen era cpu a n word, ThreadLive g gen → n < 2 ^ 64 →
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot a n word)) -∗
      ⌜readBytes g.memory a n = some word⌝)
  exclusive : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k rr post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      exclusivePremise capacity image fixed whole gen era cpu n req k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)
  bytes : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k rr dq word post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (snapshot req.pa n word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)

end MachCSL.Logic.MemoryExclusiveWP
