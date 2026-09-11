import MachCSL.Logic.TsoReadDefs

namespace MachCSL.Logic.TsoRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure TsoReadSpec {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) : Prop where
  advance : ∀ fixed g gen era cpu view, ThreadLive g gen → g.views cpu ≤ view → view ≤ g.log.length →
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era ==∗
      MachineInterp.powerInterp capacity fixed (advanceView g cpu view) ∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view)
  pristine : ∀ era g a n dq word,
    iprop(⊢ Era.interp capacity.era era g -∗
      byteWindow capacity.era.heap.ledger era.heap a n dq word -∗
      pristineWindow capacity.era.heap.ledger era.timestamps a n -∗
      ⌜∀ h view, ReadsBytes g.image g.log h view a n word⌝)
  mint : ∀ γ a n,
    iprop(initialTimestampWindow capacity.era.heap.ledger γ a n ⊢ |==>
      pristineWindow capacity.era.heap.ledger γ a n)

end MachCSL.Logic.TsoRead
