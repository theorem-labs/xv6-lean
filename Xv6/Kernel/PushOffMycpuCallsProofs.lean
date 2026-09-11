import Xv6.Kernel.PushOffMycpuCallsPureProofs
import Xv6.Kernel.KernelTextImageLink
import Xv6.Kernel.KptJalResources

namespace Xv6.Kernel.PushOffMycpuCalls
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem code era tier site :
    iprop(KernelTextImage.text capacity.translation era .identity ⊢
      KernelTextImage.text capacity.translation era .identity ∗
      KptJal.code capacity era tier (pc site) (immediate site)) := by
  iintro #Htext
  ihave Htier := (KernelTextImage.nativeSpec capacity.translation).mono era .identity tier
    (by cases tier <;> trivial) $$ Htext
  ihave Hwindow := (KernelTextImage.nativeSpec capacity.translation).window era tier
    (address site) 4 (encoding site) (bytes site) $$ Htier
  isimp only [← encoding_eq site] at Hwindow
  iframe Htext
  iapply (KptJal.nativeResourceSpec capacity).window era tier (pc site) (immediate site) (aligned site)
  ieval (change _ ⊢ KernelTextDatum.window capacity.translation era tier (KernelTextImage.address (address site)) 4 .discard (KptJal.encoding (immediate site)))
  iexact Hwindow

theorem actual : Spec capacity := ⟨code capacity⟩

end Xv6.Kernel.PushOffMycpuCalls
