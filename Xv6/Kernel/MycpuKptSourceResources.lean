import Xv6.Kernel.MycpuKptSourceSpec
import Xv6.Kernel.MycpuKptEntryPure
import Xv6.Kernel.SieOffPacketLink
import Xv6.Kernel.KernelStackLink

namespace Xv6.Kernel.MycpuKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem save_area era tier ξ entrySP available (enough : 2 ≤ available) :
    iprop(KernelStack.own capacity.translation era tier ξ entrySP available ⊣⊢
      ∃ saved : Words, MycpuKptBody.pair capacity era tier ξ entrySP saved ∗
        tail capacity era tier ξ entrySP available) := by
  rw [((KernelStack.nativeSpec capacity.translation).frame_two era tier ξ entrySP available enough).to_eq]
  unfold MycpuKptBody.pair tail
  rw [MycpuKptEntry.slot_ra, MycpuKptEntry.slot_s0]
  constructor
  · iintro ⟨%first, %second, Hfirst, Hsecond, Htail⟩
    iexists words first second
    simp only [words]
    iframe
  · iintro ⟨%saved, ⟨Hfirst, Hsecond⟩, Htail⟩
    iexists saved .ra, saved .s0
    iframe

theorem open_entry fixed gen era cpu tier ξ file available (enough : 2 ≤ available) :
    iprop(input capacity fixed gen era cpu tier ξ file available ⊢ ∃ root control saved rr,
      ⌜MycpuKptCycle.Config control⌝ ∗ ⌜SieOffPacket.Boundary entryPC control⌝ ∗
      resources capacity fixed gen era cpu tier ξ (sp file) available root control file saved rr) := by
  unfold input
  iintro ⟨⟨%root,%control,%ambient,Hopened⟩, #Hpma, Hcode⟩
  ihave ⟨%pma, Hopened⟩ := (SieOffPacket.nativeSpec capacity).boot_pma_from_cell
    fixed gen era cpu tier ξ file available (.kpt root) control $$ Hopened Hpma
  isimp [SieOffPacket.opened, SieOffPacket.frame, SieOffPacket.Regime.shell,
    SieOffPacket.slotToken] at Hopened
  icases Hopened with ⟨Hpacket, ⟨Hstack, Hrun, Htimer, Hwit, Hhw, Hshot⟩, Hresv⟩
  ihave ⟨%saved, Hpair, Htail⟩ := (save_area capacity era tier ξ (sp file) available enough).mp $$ Hstack
  isimp [Reservations.resvAny] at Hresv
  icases Hresv with ⟨%rr, Hresv⟩
  iexists root, control, saved, rr
  isplitr
  · ipureintro; exact MycpuKptEntry.config entryPC control ambient pma
  isplitr
  · ipureintro; exact ambient.toBoundary
  unfold resources frame
  iframe
  iexact Hpma

theorem close_entry fixed gen era cpu tier ξ entrySP available root control file saved rr returnPC
    (enough : 2 ≤ available) (restoredSP : sp file = entrySP)
    (boundary : SieOffPacket.Boundary returnPC control) :
    iprop(resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr ⊢
      restored capacity fixed gen era cpu tier ξ file available returnPC) := by
  unfold resources frame
  iintro ⟨Hpacket, Hcode, Hrun, Hpair, Hresv, ⟨Htail, Htimer, Hwit, Hhw, Hshot, Hpma⟩⟩
  ihave Hstack : KernelStack.own capacity.translation era tier ξ entrySP available $$ [Hpair Htail]
  · iapply (save_area capacity era tier ξ entrySP available enough).mpr
    iexists saved
    iframe
  ihave Hopened : SieOffPacket.opened capacity fixed gen era cpu tier ξ file available
      (.kpt root) control $$ [Hpacket Hrun Hresv Hstack Htimer Hwit Hhw Hshot]
  · unfold SieOffPacket.opened SieOffPacket.frame
    simp only [SieOffPacket.Regime.shell, SieOffPacket.slotToken, restoredSP]
    iframe Hpacket Hrun Hstack Htimer Hwit Hhw Hshot
    unfold Reservations.resvAny
    iexists rr
    iexact Hresv
  ihave Hsource := (SieOffPacket.nativeSpec capacity).close_packet fixed gen era cpu tier ξ
    file available returnPC (.kpt root) control boundary $$ Hopened
  unfold restored
  iframe

theorem certificate fixed gen era cpu tier ξ entrySP available root control file saved rr :
    iprop(resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr) := by
  unfold resources frame
  iintro ⟨Hpacket, Hcode, Hrun, Hpair, Hresv, ⟨Htail, Htimer, Hwit, Hhw, Hshot, Hpma⟩⟩
  ihave ⟨%hw, Hcells, Hfacts, Hcert, Hhw⟩ := SieOffPacket.hardware_access capacity fixed gen era cpu $$ Hhw
  iframe

theorem resourceSpec : ResourceSpec capacity :=
  ⟨fun _ _ _ _ _ => save_area capacity _ _ _ _ _, open_entry capacity, close_entry capacity, certificate capacity⟩

end Xv6.Kernel.MycpuKptSource
