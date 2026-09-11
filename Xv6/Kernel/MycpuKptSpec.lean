import Xv6.Kernel.MycpuKptDefs

namespace Xv6.Kernel.MycpuKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  zero : ∀ initial original old cpu, Phase initial original old cpu 0 initial original old
  bound : ∀ initial original old cpu k control values words,
    Phase initial original old cpu k control values words → k ≤ 14
  config : ∀ initial original old cpu k control values words, Config initial →
    Phase initial original old cpu k control values words → Config control
  stable : ∀ initial original old cpu k control values words,
    Phase initial original old cpu k control values words → Stable initial control
  pc : ∀ initial original old cpu k control values words,
    initial .PC = MycpuDecode.address ⟨0, by decide⟩ →
    Phase initial original old cpu k control values words → ∀ bound : k < 14,
    control .PC = MycpuDecode.address ⟨k,bound⟩
  stackReady : ∀ initial original old cpu k control values words,
    Phase initial original old cpu k control values words → ∀ bound : k < 14,
    MycpuKptBody.StackReady ⟨k,bound⟩ (entrySP cpu original) cpu values
  words : ∀ initial original old cpu k control values words,
    Phase initial original old cpu k control values words → words = wordsAt cpu original old k
  finalWords : ∀ initial original old cpu control values words,
    Phase initial original old cpu 14 control values words → words = savedWords cpu original
  sequenceProjection : ∀ initial original old cpu control values words,
    initial .PC = MycpuDecode.address ⟨0, by decide⟩ →
    Phase initial original old cpu 14 control values words → ∀ r ∈ HartTp.physicalKeys,
    entry control cpu values r = MycpuRegisterSequence.returned (entry initial cpu original) r
  result : ∀ initial original old cpu control values words, Config initial →
    initial .PC = MycpuDecode.address ⟨0, by decide⟩ →
    Phase initial original old cpu 14 control values words → Result initial original cpu control values
  boundary : ∀ initial original cpu after values, Result initial original cpu after values →
    SieOffPacket.Boundary (MycpuDecode.address ⟨0, by decide⟩) initial →
    SieOffPacket.Boundary (MycpuReturn.retPC (HartTp.rget cpu original 1#5)) after
  orderedLength : ∀ trace, Ordered trace → trace.length = 14

/-- Actual full-function WP with source packet and virtual words. The input
contains no phase relation, per-step success proof or component WP. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ shares initial original, Config initial →
    initial .PC = MycpuDecode.address ⟨0, by decide⟩ →
    ∀ old tier ξ rr tick image fixed whole gen era cpu (N : Namespace) root
      (frame : IProp GF) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu shares initial original N root tier ξ (entrySP cpu original) old rr frame -∗
      finish capacity image fixed whole gen era cpu shares initial original N root tier ξ frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuKpt
