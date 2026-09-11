import MachCSL.Logic.TsoStoreDefs
import MachCSL.Logic.TsoViewsSpec
import MachCSL.Logic.TsoHistorySpec

namespace MachCSL.Logic.TsoStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Contracts {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  views : Tso.Views.ViewsSpec capacity.views
  history : Tso.History.HistorySpec capacity.history
  logGrow : ∀ γ n n', n ≤ n' →
    iprop(⊢ Tso.Views.natAuth capacity.views γ (.own 1) n ==∗
      Tso.Views.natAuth capacity.views γ (.own 1) n' ∗ Tso.Views.natLB capacity.views γ n')

structure StoreSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  update : ∀ names eraImage before after old new author,
    SameDomain old new → Transition before after new author →
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ledgerMap capacity names old ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨FiniteMap.decode new, author⟩ ∗
      storedMap capacity names new (before.log.length + 1))
  window : ∀ names eraImage before after a n {bits : Nat} (old new : BitVec bits) author,
    n ≤ 2 ^ 64 → WindowTransition before after a n new author →
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ledgerWindow capacity names a n old ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨snapshot a n new, author⟩ ∗
      storedWindow capacity names a n new (before.log.length + 1))

end MachCSL.Logic.TsoStore
