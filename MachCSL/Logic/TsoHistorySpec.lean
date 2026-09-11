import MachCSL.Logic.TsoHistoryDefs

/-! Client contract for history resources, independent of their proof implementation. -/
namespace MachCSL.Logic.Tso.History
open MachCSL.Memory Iris Iris.BI Iris.Std.PartialMap

structure HistorySpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  dirtyAlloc : iprop(⊢ |==> ∃ γ, dsetAuth capacity γ 1 ∅)
  dirtyHalves : ∀ γ set,
    iprop(dsetAuth capacity γ 1 set ⊣⊢
      dsetAuth capacity γ (Qp.half 1) set ∗ dsetAuth capacity γ (Qp.half 1) set)
  dirtyAgree : ∀ γ q1 q2 s1 s2,
    iprop(⊢ dsetAuth capacity γ q1 s1 -∗ dsetAuth capacity γ q2 s2 -∗ ⌜s1 = s2⌝)
  dirtyLookup : ∀ γ q set k,
    iprop(⊢ dsetAuth capacity γ q set -∗ dsetIn capacity γ k -∗ ⌜k ∈ set⌝)
  dirtyGet : ∀ γ q set k, k ∈ set →
    iprop(⊢ dsetAuth capacity γ q set ==∗ dsetAuth capacity γ q set ∗ dsetIn capacity γ k)
  dirtyInsert : ∀ γ set k,
    iprop(⊢ dsetAuth capacity γ 1 set ==∗
      dsetAuth capacity γ 1 (set ∪ {k}) ∗ dsetIn capacity γ k)
  dirtyMono : ∀ γ h bound bound' key, bound ≤ bound' →
    iprop(⊢ dirtyOK capacity γ h bound key -∗ dirtyOK capacity γ h bound' key)
  logAlloc : iprop(⊢ |==> ∃ γ, logAuth capacity γ (.own 1) ∅)
  logAgree : ∀ γ dq1 dq2 map1 map2,
    iprop(⊢ logAuth capacity γ dq1 map1 -∗ logAuth capacity γ dq2 map2 -∗ ⌜map1 = map2⌝)
  logLookup : ∀ γ dq entries i m,
    iprop(⊢ logAuth capacity γ dq entries -∗ logElem capacity γ i m -∗
      ⌜get? entries i = some m⌝)
  logInsert : ∀ γ entries i m, get? entries i = none →
    iprop(⊢ logAuth capacity γ (.own 1) entries ==∗
      logAuth capacity γ (.own 1) (insert entries i m) ∗ logElem capacity γ i m)
  logAppend : ∀ γ entries log m, LogRep entries log → ∀ P : IProp GF,
    iprop(⊢ logAuth capacity γ (.own 1) entries ∗ P ==∗
      logAuth capacity γ (.own 1) (insert entries log.length m) ∗
      logElem capacity γ log.length m ∗ P ∗
      ⌜LogRep (insert entries log.length m) (log ++ [m])⌝)

end MachCSL.Logic.Tso.History
