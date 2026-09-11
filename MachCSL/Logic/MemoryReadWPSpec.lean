import MachCSL.Logic.MemoryReadWPDefs

namespace MachCSL.Logic.MemoryReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure MemoryReadWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  plain : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k P post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      plainPremise capacity image fixed whole gen era cpu n req k P post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)
  fixedWord : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      plainWordPremise capacity image fixed whole gen era cpu n req k post -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)
  pristine : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k dq word post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)

  pristineMint : ∀ image fixed whole gen era cpu n (req : ReadRequest n) k dq word post,
    deviceAddress req.pa = false → accessExclusive req.access_kind = false →
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.initialTimestampWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, TsoRead.byteWindow capacity.era.heap.ledger era.heap req.pa n dq word -∗
        TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps req.pa n -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post)

end MachCSL.Logic.MemoryReadWP
