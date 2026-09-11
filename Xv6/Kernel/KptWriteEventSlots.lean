import Xv6.Kernel.KptWriteEventSpec
import MachCSL.Logic.SupervisorPteADSlots
import MachCSL.Machine.PteCanonicalLink

namespace Xv6.Kernel.KptWriteEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The written bytes keep the original per-address allowed sets. The
leaf-family equality re-expresses them as the new slot's own sets. -/
theorem slot_family era address dq bound word a d (leaf : PteCanonical.Leaf word) :
    iprop(TsoPinnedReadWP.slot capacity.machine era address 8 dq
      (nthByte (PteCanonical.setAD word a d)) bound (PteCanonical.slotSet word) ⊢
      TsoPinnedReadWP.slot capacity.machine era address 8 dq
        (nthByte (PteCanonical.setAD word a d)) bound
        (PteCanonical.slotSet (PteCanonical.setAD word a d))) := by
  unfold TsoPinnedReadWP.slot TsoPinnedRead.slotBytes
  apply BigSepL.bigSepL_mono
  intro i j found
  have inside : j < 8 := List.mem_range.mp (List.mem_iff_getElem?.mpr ⟨i,found⟩)
  rw [PteCanonical.family_variant word a d j leaf inside]

end Xv6.Kernel.KptWriteEvent
