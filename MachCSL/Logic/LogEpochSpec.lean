import MachCSL.Logic.LogEpochDefs

namespace MachCSL.Logic.LogEpoch
open Iris Iris.BI
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  get : ∀ name epoch, iprop(⊢ epochAuth capacity name epoch -∗
    epochAuth capacity name epoch ∗ log_epoch_lb capacity name epoch)
  le : ∀ name epoch bound, iprop(⊢ epochAuth capacity name epoch -∗
    log_epoch_lb capacity name bound -∗ ⌜bound ≤ epoch⌝)
  zero : ∀ name, iprop(⊢ |==> log_epoch_lb capacity name 0)
  mint : ∀ name entries epoch block, iprop(⊢ loggedAuth capacity name entries ==∗
    loggedAuth capacity name (entries ∪ {(epoch, block)}) ∗ logged_at capacity name epoch block)
  member : ∀ name entries epoch block, iprop(⊢ loggedAuth capacity name entries -∗
    logged_at capacity name epoch block -∗ ⌜(epoch, block) ∈ entries⌝)
end MachCSL.Logic.LogEpoch
