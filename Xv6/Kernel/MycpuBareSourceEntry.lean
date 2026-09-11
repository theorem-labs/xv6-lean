import Xv6.Kernel.MycpuBareSourceResources
import Xv6.Kernel.SieOffPacketLink
import Xv6.Kernel.KernelStackLink

namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem open_entry fixed gen era cpu ξ file available extra (enough : 2 ≤ available) :
    iprop(input capacity fixed gen era cpu ξ file available extra ⊢ ∃ control raWord s0Word rr,
      ⌜MycpuOff.EntryConfig control⌝ ∗ ⌜SieOffPacket.Ambient entryPC control⌝ ∗
      resources capacity fixed gen era cpu ξ (sp file) available control file raWord s0Word rr extra) := by
  unfold input
  iintro ⟨⟨%control,%facts,Hopened⟩,#Htext,#Hpma,Hextra⟩
  ihave ⟨%pma,Hopened⟩ := (SieOffPacket.nativeSpec capacity).boot_pma_from_cell
    fixed gen era cpu .identity ξ file available .bare control $$ Hopened Hpma
  isimp only [SieOffPacket.opened, SieOffPacket.frame, SieOffPacket.Regime.shell] at Hopened
  icases Hopened with ⟨Hpacket,⟨Hstack,Hrun,Htimer,Hwit,Hhw,Hslot⟩,Hresv⟩
  ihave ⟨%satp,%pmp,%mode,%tor,Hpacket⟩ := (packet capacity era cpu control file).mp $$ Hpacket
  ihave ⟨%raWord,%s0Word,Hra,Hs0,Htail⟩ :=
    ((KernelStack.nativeSpec capacity.translation).frame_two era .identity ξ (sp file) available enough).mp $$ Hstack
  ihave ⟨Hra,HcloseRA⟩ := identity_word capacity era ξ (KernelStack.paStk (sp file) 1) raWord $$ Hra
  ihave ⟨Hs0,HcloseS0⟩ := identity_word capacity era ξ (KernelStack.paStk (sp file) 2) s0Word $$ Hs0
  ihave ⟨_,Hcode⟩ := text_resources capacity era $$ Htext
  isimp only [Reservations.resvAny] at Hresv
  icases Hresv with ⟨%rr,Hresv⟩
  iexists patch control satp pmp,raWord,s0Word,rr
  isplitr
  · ipureintro; exact config control satp pmp facts pma mode tor
  isplitr
  · ipureintro; exact ambient entryPC control satp pmp facts
  unfold resources frame physicalPair
  iframe Hpacket Hrun Hcode Hra Hs0 Hresv Htail HcloseRA HcloseS0 Htimer Hwit Hhw Hslot Htext Hpma Hextra

theorem patch_self (control : RegisterFile) : patch control (control .satp) control = control := by
  funext r
  cases r <;> rfl

theorem bare_mode (value : BitVec 4)
    (mode : satpMode_of_bits .RV64 value = some .Bare) : value = 0#4 := by
  unfold satpMode_of_bits at mode
  split at mode <;> simp_all

theorem close_entry fixed gen era cpu ξ entrySP available control file raWord s0Word rr pc extra
    (enough : 2 ≤ available) (restoredSP : sp file = entrySP)
    (boundary : SieOffPacket.Boundary pc control)
    (mode : satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (control .satp))) = some .Bare)
    (tor : SupervisorPmp.TorRam control) :
    iprop(resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra ⊢
      restored capacity fixed gen era cpu ξ file available pc extra) := by
  unfold resources frame physicalPair
  iintro ⟨Hpacket,Hrun,Hcode,⟨Hra,Hs0⟩,Hresv,
    ⟨Htail,HcloseRA,HcloseS0,Htimer,Hwit,Hhw,Hslot,Htext,Hpma,Hextra⟩⟩
  iunfold closeWord at HcloseRA HcloseS0
  ihave Hra := HcloseRA $$ %raWord Hra
  ihave Hs0 := HcloseS0 $$ %s0Word Hs0
  ihave Hstack : KernelStack.own capacity.translation era .identity ξ entrySP available $$ [Hra Hs0 Htail]
  · iapply ((KernelStack.nativeSpec capacity.translation).frame_two era .identity ξ entrySP available enough).mpr
    iexists raWord,s0Word
    iframe
  ihave Hpacket : MycpuRegimeShell.resources capacity era cpu .bare control file
      MycpuRegimeShell.sourceShares $$ [Hpacket]
  · iapply (packet capacity era cpu control file).mpr
    iexists control .satp,control
    simp only [patch_self]
    iframe Hpacket
    isplitr
    · ipureintro; exact bare_mode _ mode
    ipureintro; exact tor
  ihave Hopened : SieOffPacket.opened capacity fixed gen era cpu .identity ξ file available .bare control $$
      [Hpacket Hrun Hresv Hstack Htimer Hwit Hhw Hslot]
  · unfold SieOffPacket.opened SieOffPacket.frame
    simp only [SieOffPacket.Regime.shell, restoredSP]
    iframe Hpacket Hrun Hstack Htimer Hwit Hhw Hslot
    unfold Reservations.resvAny
    iexists rr
    iexact Hresv
  ihave Hsource := (SieOffPacket.nativeSpec capacity).close_packet fixed gen era cpu .identity ξ
    file available pc .bare control boundary $$ Hopened
  unfold restored
  iframe

theorem certificate fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra :
    iprop(resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra) := by
  unfold resources frame
  iintro ⟨Hpacket,Hrun,Hcode,Hpair,Hresv,
    ⟨Htail,HcloseRA,HcloseS0,Htimer,Hwit,Hhw,Hslot,Htext,Hpma,Hextra⟩⟩
  ihave ⟨%hw,Hcells,Hfacts,Hcert,Hhw⟩ := SieOffPacket.hardware_access capacity fixed gen era cpu $$ Hhw
  iframe

theorem resourceSpec : ResourceSpec capacity :=
  ⟨identity_word capacity,text_resources capacity,packet capacity,open_entry capacity,
    close_entry capacity,certificate capacity⟩

end Xv6.Kernel.MycpuBareSource
