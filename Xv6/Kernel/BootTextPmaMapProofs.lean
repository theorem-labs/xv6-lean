import Xv6.Kernel.BootTextPmaMapSpec
import Xv6.Kernel.KernelTextBootMapLink
import Xv6.Kernel.BootPmaLink

namespace Xv6.Kernel.BootTextPmaMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Keep the large static predicates opaque to proofmode. The public rule
instantiates this frame with the exact native map and text resources. -/
private theorem produce_generic (held : IProp GF) image era g memory diskBytes
    (facts : BootFacts image g) :
    iprop(held ∗ KernelTextBoot.retained capacity era memory g diskBytes ⊢ |==>
      (held ∗ BootPma.all capacity era ∗ BootPma.textRetained capacity era memory g diskBytes)) := by
  iintro ⟨Hheld, Hr⟩
  imod (BootPma.nativeSpec capacity).produce_text_retained image era g memory diskBytes facts
    $$ Hr with ⟨Hp, Hr⟩
  imodintro
  iframe

/-- Consume only the PMA register column of the actual map/text output. -/
theorem produce image era g memory diskBytes (facts : BootFacts image g) :
    iprop(KernelTextBootMap.resources capacity era memory g diskBytes ⊢ |==>
      resources capacity era memory g diskBytes) := by
  let held := iprop(Era.interp capacity.machine.era era g ∗
    KernelMapStatic.authority capacity era.kernelMap ∗ KernelMapStatic.claims capacity era.kernelMap ∗
    KernelTextImage.physicalText capacity era ∗ KernelTextImage.text capacity era .identity)
  have assoc (a b c d e f : IProp GF) :
      iprop(a ∗ b ∗ c ∗ d ∗ e ∗ f ⊣⊢ (a ∗ b ∗ c ∗ d ∗ e) ∗ f) := by
    constructor
    · iintro ⟨Ha, Hb, Hc, Hd, He, Hf⟩
      iframe
    · iintro ⟨⟨Ha, Hb, Hc, Hd, He⟩, Hf⟩
      iframe
  unfold KernelTextBootMap.resources resources
  exact (assoc _ _ _ _ _ _).1.trans ((produce_generic capacity held image era g memory diskBytes facts).trans
    (bupd_mono (assoc _ _ _ _ _ _).2))

theorem allocate_frame (before : State) (template : Era.Record) (diskBytes : Nat) (frame : IProp GF) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(frame ⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes ∗ frame) := by
  dsimp only
  iintro Hframe
  imod (KernelTextBootMap.nativeSpec capacity).allocate_frame before template diskBytes frame
    $$ Hframe with ⟨%name, %era, Hinstalled, Hresources, Hframe⟩
  imod produce capacity Xv6.Machine.bootImage era (Xv6.Machine.boot before)
    (FiniteMap.encodeAll (Xv6.Machine.boot before).memory) diskBytes
    (Xv6.Machine.boot_facts before) $$ Hresources with Hresources
  imodintro
  iexists name, era
  iframe

theorem allocate (before : State) (template : Era.Record) (diskBytes : Nat) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes) := by
  dsimp only
  ihave Hempty : emp $$ []
  · itrivial
  imod allocate_frame capacity before template diskBytes iprop(emp) $$ Hempty
    with ⟨%name, %era, Hinstalled, Hresources, _⟩
  imodintro
  iexists name, era
  iframe

end Xv6.Kernel.BootTextPmaMap
