import Xv6.Kernel.KernelTextBootMapSpec
import Xv6.Kernel.KernelTextBootLink
import Xv6.Kernel.KernelTextImageLink
import Xv6.Kernel.KernelMapStaticLink

namespace Xv6.Kernel.KernelTextBootMap
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

theorem install_name template name : (install template name).kernelMap = name := rfl

theorem install_other template name : OtherAuxiliarySame (install template name) template := by
  repeat constructor

theorem auxiliary_iff era template name :
    Era.AuxiliarySame era (install template name) ↔ era.kernelMap = name ∧ OtherAuxiliarySame era template :=
  Iff.rfl

theorem installed era template name memory (image : era.image = memory)
    (same : Era.AuxiliarySame era (install template name)) : Installed era template name memory :=
  ⟨image, (auxiliary_iff era template name).mp same⟩

theorem actualPure : PureSpec := ⟨install_name, install_other, auxiliary_iff, installed⟩

attribute [local irreducible] KernelMapStatic.claims KernelMapStatic.authority
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Generic framing prevents proofmode from expanding the finite static
map. The public theorem supplies exactly the actual native predicates and
allocators, with no caller obligations. -/
private theorem allocate_frame_generic
    (authority claims : GName → IProp GF) [∀ name, Persistent (claims name)]
    (mapAllocate : ∀ frame : IProp GF, iprop(frame ⊢ |==> ∃ name,
      authority name ∗ claims name ∗ frame))
    (attach : ∀ era, iprop(⊢ KernelTextImage.physicalText capacity era -∗
      claims era.kernelMap -∗ KernelTextImage.text capacity era .identity))
    (before : State) (template : Era.Record) (diskBytes : Nat) (frame : IProp GF) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(frame ⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      (Era.interp capacity.machine.era era g ∗ authority era.kernelMap ∗ claims era.kernelMap ∗
       KernelTextImage.physicalText capacity era ∗ KernelTextImage.text capacity era .identity ∗
       KernelTextBoot.retained capacity era memory g diskBytes) ∗ frame) := by
  dsimp only
  iintro Hframe
  imod mapAllocate frame $$ Hframe with ⟨%name, Hauth, #Hclaims, Hframe⟩
  imod (KernelTextBoot.nativeSpec capacity).allocate before (install template name) diskBytes
    with ⟨%era, %same, Hinterp, #Hphysical, Hretained⟩
  have named : era.kernelMap = name := ((auxiliary_iff era template name).mp same.2).1
  have physical := attach era
  rw [named] at physical
  ihave Htext := physical $$ Hphysical Hclaims
  imodintro
  iexists name, era
  isplitr
  · ipureintro; exact installed era template name _ same.1 same.2
  rw [named]
  iframe Hauth Hclaims Hphysical Htext Hinterp Hretained Hframe

/-- Both allocation operations are native. The installed name is derived
from the returned actual era, before attaching persistent identity claims. -/
theorem allocate_frame (before : State) (template : Era.Record) (diskBytes : Nat) (frame : IProp GF) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(frame ⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes ∗ frame) :=
  allocate_frame_generic capacity (KernelMapStatic.authority capacity) (KernelMapStatic.claims capacity)
    (KernelMapStatic.nativeSpec capacity).allocate (KernelTextImage.nativeSpec capacity).physical
    before template diskBytes frame

theorem allocate (before : State) (template : Era.Record) (diskBytes : Nat) :
    let g := Xv6.Machine.boot before
    let memory := FiniteMap.encodeAll g.memory
    iprop(⊢ |==> ∃ name era, ⌜Installed era template name memory⌝ ∗
      resources capacity era memory g diskBytes) := by
  dsimp only
  ihave Hempty : emp $$ []
  · itrivial
  imod allocate_frame capacity before template diskBytes iprop(emp) $$ Hempty with ⟨%name, %era, Hfacts, Hresources, _⟩
  imodintro
  iexists name, era
  iframe

end Xv6.Kernel.KernelTextBootMap
