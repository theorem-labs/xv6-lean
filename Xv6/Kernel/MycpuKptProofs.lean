import Xv6.Kernel.MycpuKptPure
import Xv6.Kernel.MycpuKptGuards

namespace Xv6.Kernel.MycpuKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem receipts_snoc era cpu sp (trace : List Receipt) (r : Receipt) :
    iprop(⊢ receipts capacity era cpu sp trace -∗
      MycpuKptCycle.receipts capacity era cpu r.index sp r.fetchTrace r.outcome -∗
      receipts capacity era cpu sp (trace ++ [r])) := by
  induction trace with
  | nil =>
    simp only [List.nil_append, receipts]
    iintro _ Hreceipt
    iframe
  | cons first rest ih =>
    simp only [List.cons_append, receipts]
    iintro ⟨Hfirst,Hrest⟩ Hreceipt
    ihave Hrest := ih $$ Hrest Hreceipt
    iframe

theorem reservation_zero rr : reservationAt rr 0 = rr := rfl

theorem reservation_positive rr k (positive : 0 < k) : reservationAt rr k = none := by
  simp [reservationAt, Nat.ne_of_gt positive]

variable [Platform]

/-- Finite induction over the actual native cycles. Phase and event receipts
are constructed after each returned rule; neither is a public input oracle. -/
theorem chain shares initial original (config : Config initial)
    (pc : initial .PC = MycpuDecode.address ⟨0, by decide⟩)
    old tier ξ initialRR image fixed whole gen era cpu (N : Namespace) root
    (frame : IProp GF) post (fuel : Nat) :
    ∀ k, k + fuel = 14 → ∀ control values words,
      Phase initial original old cpu k control values words →
    ∀ (trace : List Receipt), trace.map (fun r => r.index.val) = List.range k → ∀ tick,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu shares control values N root tier ξ (entrySP cpu original) words
        (reservationAt initialRR k) frame -∗
      receipts capacity era cpu (entrySP cpu original) trace -∗
      finish capacity image fixed whole gen era cpu shares initial original N root tier ξ frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  induction fuel with
  | zero =>
    intro k bound control values words phase trace ordered tick
    have eq : k = 14 := by omega
    subst k
    iintro #Hcert Hresources Hreceipts Hfinish
    have result := phase_result config pc phase
    have saved := final_words phase
    isimp only [saved, reservation_positive initialRR 14 (by decide)] at Hresources
    iunfold finish at Hfinish
    iapply Hfinish $$ %control %values %trace %⟨result,ordered⟩ Hresources Hreceipts %tick
  | succ fuel ih =>
    intro k bound control values words phase trace ordered tick
    have inside : k < 14 := by omega
    let i : Fin 14 := ⟨k,inside⟩
    iintro #Hcert Hresources Hreceipts Hfinish
    iunfold resources at Hresources
    icases Hresources with ⟨Hpacket,Hcode,Hrun,Hpair,Hresv,Hframe⟩
    let extra : IProp GF := iprop(receipts capacity era cpu (entrySP cpu original) trace ∗ frame)
    iapply (MycpuKptCycle.nativeSpec capacity).cycle shares control values (phase_config config phase) i
      (phase_pc pc phase inside) (entrySP cpu original) tier ξ words (reservationAt initialRR k) tick
      image fixed whole gen era cpu N root (phase_ready phase inside) extra post
      $$ Hcert Hpacket Hcode Hrun Hpair Hresv [Hreceipts Hframe] [Hfinish]
    · isimp only [extra]; iframe
    · iunfold MycpuKptCycle.cycleFinish
      iapply guards_intro
      iintro %fetchTrace %outcome %after %done !> %nextTick Hresources
      have phase' := Phase.next inside phase done
      let receipt : Receipt := ⟨i,fetchTrace,outcome⟩
      have ordered' : (trace ++ [receipt]).map (fun r => r.index.val) = List.range (k+1) := by
        simp only [List.map_append, List.map_cons, List.map_nil, receipt, i, ordered, List.range_succ]
      iunfold MycpuKptCycle.cycleResources at Hresources
      icases Hresources with ⟨Hpacket,Hcode,Hrun,Hpair,Hresv,Hthis,Hextra⟩
      isimp only [extra] at Hextra
      icases Hextra with ⟨Hreceipts,Hframe⟩
      ihave Hreceipts := receipts_snoc capacity era cpu (entrySP cpu original) trace receipt $$ Hreceipts Hthis
      iapply ih (k+1) (by omega) after _ _ phase' (trace ++ [receipt]) ordered' nextTick
        $$ Hcert [Hpacket Hcode Hrun Hpair Hresv Hframe] Hreceipts Hfinish
      iunfold resources
      isimp only [reservation_positive initialRR (k+1) (by omega)]
      iframe

theorem wp_function shares initial original (config : Config initial)
    (pc : initial .PC = MycpuDecode.address ⟨0, by decide⟩)
    old tier ξ rr tick image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      resources capacity era cpu shares initial original N root tier ξ (entrySP cpu original) old rr frame -∗
      finish capacity image fixed whole gen era cpu shares initial original N root tier ξ frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro Hcert Hresources Hfinish
  have first := chain capacity shares initial original config pc old tier ξ rr image fixed whole gen era cpu N root
    frame post 14 0 rfl initial original old .zero [] rfl tick
  simp only [reservation_zero] at first
  iapply first $$ Hcert Hresources [] Hfinish
  simp only [receipts]
  itrivial

theorem actual : Spec capacity := ⟨wp_function capacity⟩

end Xv6.Kernel.MycpuKpt
