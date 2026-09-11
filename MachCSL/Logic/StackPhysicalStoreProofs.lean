import MachCSL.Logic.StackPhysicalProofs

namespace MachCSL.Logic.StackPhysical
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Resource composition for the two actual ordinary save stores. Each
premise describes one separate eight-byte authored log append. This theorem
is not an atomic instruction WP and does not hide an intervening state. -/
theorem save_two names cpu ξ eraImage before middle after sp n
    (bound : 2 ≤ n) (ra s0 : TsoContextWord.Word)
    (first : TsoContextStore.OrdinaryTransition before middle
      (TsoStore.windowMap (paStk sp 1) 8 ra) cpu)
    (second : TsoContextStore.OrdinaryTransition middle after
      (TsoStore.windowMap (paStk sp 2) 8 s0) cpu) :
    iprop(⊢ heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ own capacity names ξ sp n ==∗
      heapAt capacity names after ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 1) (.own 1) ra ∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 2) (.own 1) s0 ∗
      own capacity names ξ (paStk sp 2) (n - 2) ∗
      ⌜TsoContextWord.Readback after cpu (paStk sp 1) ra ∧
        TsoContextWord.Readback after cpu (paStk sp 2) s0⌝) := by
  rw [(frame_two capacity names ξ sp n bound).to_eq]
  iintro Hheap Htso Hrun ⟨%oldRa, %oldS0, Hra, Hs0, Hrest⟩
  imod TsoContextWord.ordinary capacity names cpu ξ eraImage before middle (paStk sp 1)
    oldRa ra first $$ Hheap Htso Hrun Hra with ⟨Hheap, Htso, Hrun, Hra, _⟩
  imod TsoContextWord.ordinary capacity names cpu ξ eraImage middle after (paStk sp 2)
    oldS0 s0 second $$ Hheap Htso Hrun Hs0 with ⟨Hheap, Htso, Hrun, Hs0, %s0read⟩
  imodintro
  ihave %raread := TsoContextWord.load_fact capacity names cpu ξ eraImage after (paStk sp 1)
    (.own 1) ra $$ Hheap Htso Hrun Hra
  iframe Hheap Htso Hrun Hra Hs0 Hrest
  ipureintro
  exact ⟨raread, s0read⟩

/-- Read the two saved words at all permitted views and rejoin the same
untouched remainder. No actual register, PC, or stack-pointer update is claimed. -/
theorem restore_two names cpu ξ eraImage g sp n
    (bound : 2 ≤ n) (ra s0 : TsoContextWord.Word) :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 1) (.own 1) ra -∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 2) (.own 1) s0 -∗
      own capacity names ξ (paStk sp 2) (n - 2) -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ own capacity names ξ sp n ∗
      ⌜TsoContextWord.Readback g cpu (paStk sp 1) ra ∧
        TsoContextWord.Readback g cpu (paStk sp 2) s0⌝) := by
  iintro Hheap Htso Hrun Hra Hs0 Hrest
  ihave %raread := TsoContextWord.load_fact capacity names cpu ξ eraImage g (paStk sp 1)
    (.own 1) ra $$ Hheap Htso Hrun Hra
  ihave %s0read := TsoContextWord.load_fact capacity names cpu ξ eraImage g (paStk sp 2)
    (.own 1) s0 $$ Hheap Htso Hrun Hs0
  iframe Hheap Htso Hrun
  isplitl [Hra Hs0 Hrest]
  · rw [(frame_two capacity names ξ sp n bound).to_eq]
    iexists ra, s0
    iframe Hra Hs0 Hrest
  · ipureintro
    exact ⟨raread, s0read⟩

end MachCSL.Logic.StackPhysical
