import MachCSL.Logic.FsViewDefs

namespace MachCSL.Logic.FsView
open Iris Iris.Std Iris.CMRA Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors}

def PhiExcl (view : View GF) : Prop :=
  ∀ (a : Int) (v w : Byte) (dq1 dq2 : DFrac),
    iprop(view.phi dq1 a v ∗ view.phi dq2 a w ⊢ ⌜✓ (dq1 • dq2)⌝)

def PhiFrac (view : View GF) : Prop :=
  ∀ (a : Int) (v : Byte) (q1 q2 : Qp),
    iprop(view.phi (.own (q1 + q2)) a v ⊣⊢
      view.phi (.own q1) a v ∗ view.phi (.own q2) a v)

class GTimeless (view : View GF) : Prop where
  timeless : ∀ (dq : DFrac) (a : Int) (v : Byte), Timeless (view.phi dq a v)

attribute [instance] GTimeless.timeless

/-- Only a full-share input and a one-way split are required by the source. -/
def ViewShed (view left right : View GF) : Prop :=
  ∀ (a : Int) (v : Byte), iprop(view.phi (.own 1) a v ⊢
    left.phi (.own 1) a v ∗ right.phi (.own 1) a v)

end MachCSL.Logic.FsView
