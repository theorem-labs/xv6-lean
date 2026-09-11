import Xv6.Kernel.KptADSpec

namespace Xv6.Kernel.KptAD
open Iris Iris.BI

/-- Extract exactly one guard for the unknown exclusive-read result. The
write alternative retains its second guard; additive branching does not
copy any client ownership. -/
theorem enabled_guards {GF : BundledGFunctors} (Φ : Branch → IProp GF) :
    iprop((∀ branch, guarded branch (Φ branch)) ⊢
      ▷ ((∀ observed, Φ (.reread observed)) ∧
          ∀ observed new, ▷ Φ (.written observed new))) := by
  iintro H
  iapply later_and.mpr
  isplit
  · iapply later_forall.mpr
    iintro %observed
    ihave Hcase := H $$ %(Branch.reread observed)
    iunfold guarded at Hcase
    iexact Hcase
  · iapply later_forall.mpr
    iintro %observed
    iapply later_forall.mpr
    iintro %new
    ihave Hcase := H $$ %(Branch.written observed new)
    iunfold guarded at Hcase
    iexact Hcase

end Xv6.Kernel.KptAD
