import Xv6.Kernel.BareJalSourcePure
import Xv6.Kernel.SieOffPacketLink
namespace Xv6.Kernel.BareJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem open_entry fixed gen era cpu ξ file available pc imm extra :
    iprop(input capacity fixed gen era cpu ξ file available pc imm extra ⊢ ∃ control rr,
      ⌜BareJal.Config control⌝ ∗ ⌜SieOffPacket.Ambient pc control⌝ ∗
      resources capacity fixed gen era cpu ξ file available control pc imm rr extra) := by
  unfold input
  iintro ⟨⟨%control,%facts,Hopened⟩,Hcode,#Hpma,Hextra⟩
  ihave ⟨%pma,Hopened⟩ := (SieOffPacket.nativeSpec capacity).boot_pma_from_cell
    fixed gen era cpu .identity ξ file available .bare control $$ Hopened Hpma
  isimp only [SieOffPacket.opened,SieOffPacket.frame,SieOffPacket.Regime.shell,Reservations.resvAny] at Hopened
  icases Hopened with ⟨Hpacket,⟨Hstack,Hrun,Htimer,Hwit,Hhw,Hslot⟩,%rr,Hresv⟩
  iexists control,rr
  isplitr
  · ipureintro; exact config pc control facts pma
  isplitr
  · ipureintro; exact facts
  unfold resources kept BareJal.packet
  iframe Hpacket Hcode Hrun Hresv Hstack Htimer Hwit Hhw Hslot Hpma Hextra

theorem close_entry fixed gen era cpu ξ file available control codePC currentPC imm rr extra
    (atBoundary : SieOffPacket.Boundary currentPC control) :
    iprop(resources capacity fixed gen era cpu ξ file available control codePC imm rr extra ⊢
      restored capacity fixed gen era cpu ξ file available codePC currentPC imm extra) := by
  unfold resources kept BareJal.packet
  iintro ⟨Hpacket,Hcode,Hrun,Hresv,Hstack,Htimer,Hwit,Hhw,Hslot,Hpma,Hextra⟩
  ihave Hopened : SieOffPacket.opened capacity fixed gen era cpu .identity ξ file available .bare control $$
      [Hpacket Hrun Hresv Hstack Htimer Hwit Hhw Hslot]
  · unfold SieOffPacket.opened SieOffPacket.frame
    simp only [SieOffPacket.Regime.shell]
    iframe Hpacket Hrun Hstack Htimer Hwit Hhw Hslot
    unfold Reservations.resvAny
    iexists rr
    iexact Hresv
  ihave Hsource := (SieOffPacket.nativeSpec capacity).close_packet fixed gen era cpu .identity ξ
    file available currentPC .bare control atBoundary $$ Hopened
  unfold restored
  iframe

theorem kept_update fixed gen era cpu ξ file available pc extra :
    iprop(kept capacity fixed gen era cpu ξ file available extra ⊣⊢
      kept capacity fixed gen era cpu ξ (afterFile pc file) available extra) := by
  simp only [kept,stack]
  exact .rfl

theorem certificate fixed gen era cpu ξ file available control pc imm rr extra :
    iprop(resources capacity fixed gen era cpu ξ file available control pc imm rr extra ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu ξ file available control pc imm rr extra) := by
  unfold resources kept
  iintro ⟨Hpacket,Hcode,Hrun,Hresv,Hstack,Htimer,Hwit,Hhw,Hslot,Hpma,Hextra⟩
  ihave ⟨%hw,Hcells,Hfacts,Hcert,Hhw⟩ := SieOffPacket.hardware_access capacity fixed gen era cpu $$ Hhw
  iframe

theorem nativeResourceSpec : ResourceSpec capacity :=
  ⟨open_entry capacity,close_entry capacity,kept_update capacity,certificate capacity⟩
end Xv6.Kernel.BareJalSource
