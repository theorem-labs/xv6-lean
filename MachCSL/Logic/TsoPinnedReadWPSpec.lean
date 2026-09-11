import MachCSL.Logic.TsoPinnedReadWPDefs

namespace MachCSL.Logic.TsoPinnedReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  plain : ∀ image fixed whole gen era cpu n (req : MemoryReadWP.ReadRequest n) k
      dq value bound sets rr post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      credential capacity era cpu bound -∗ slot capacity era req.pa n dq value bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜Allowed n sets word⌝ -∗ credential capacity era cpu bound -∗
        slot capacity era req.pa n dq value bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)
  exclusive : ∀ image fixed whole gen era cpu (req : MemoryReadWP.ReadRequest 8) k
      dq (word : BitVec 64) bound sets rr post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = true →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      slot capacity era req.pa 8 dq (nthByte word) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, slot capacity era req.pa 8 dq (nthByte word) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem 8 req) k)) post)
  pte : ∀ image fixed whole gen era cpu (req : MemoryReadWP.ReadRequest 8) k
      dq value bound (reference : BitVec 64) rr post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      credential capacity era cpu bound -∗
      slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon reference⌝ -∗
        ⌜PteCanonical.nonleaf reference = true → word = reference⌝ -∗
        credential capacity era cpu bound -∗
        slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem 8 req) k)) post)

end MachCSL.Logic.TsoPinnedReadWP
