import Xv6.Kernel.KptJalSconfPure
import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.MycpuKptEntryLink
import Xv6.Kernel.MycpuKptGuards

namespace Xv6.Kernel.KptJalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_cycle (jal : KptJal.Spec capacity)
    image fixed whole gen era cpu ξ file available pc imm tick (frame : IProp GF) post
    (even : KptJal.TargetEven pc imm) :
    iprop(⊢ input capacity fixed gen era cpu ξ file available pc imm frame -∗
      finish capacity image fixed whole gen era cpu ξ file available pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨Hsource,Hcode,#Hpma,Hframe⟩ Hfinish
  ihave ⟨%regime,%control,%ambient,%admits,Hopened⟩ :=
    (SieOffPacket.nativeSpec capacity).open_packet fixed gen era cpu .full ξ file available pc $$ Hsource
  obtain ⟨root,rfl⟩ := MycpuKptEntry.full_regime regime admits
  ihave ⟨%pma,Hopened⟩ := (SieOffPacket.nativeSpec capacity).boot_pma_from_cell
    fixed gen era cpu .full ξ file available (.kpt root) control $$ Hopened Hpma
  ihave ⟨#Hcert,Hopened⟩ := (SieOffPacket.nativeSpec capacity).certificate
    fixed gen era cpu .full ξ file available (.kpt root) control $$ Hopened
  isimp [SieOffPacket.opened,SieOffPacket.frame,SieOffPacket.Regime.shell,
    SieOffPacket.slotToken,Reservations.resvAny] at Hopened
  icases Hopened with ⟨Hpacket,⟨Hstack,Hrun,Htimer,Hwit,Hhw,Hshot⟩,⟨%rr,Hresv⟩⟩
  let extra : IProp GF := iprop(
    KernelStack.own capacity.translation era .full ξ (SieOffCapability.sp file) available ∗
    SieOffCapability.timer capacity era cpu ∗ SieOffCapability.tierWitness capacity era cpu .full ∗
    Sconf.hardware capacity fixed gen era cpu ∗ SupervisorTranslation.shot capacity.translation era cpu ∗ frame)
  iapply jal.cycle MycpuRegimeShell.sourceShares control file
    (MycpuKptEntry.config pc control ambient pma) pc imm ambient.pc_eq even
    .full ξ rr tick image fixed whole gen era cpu KptGhost.kptN root extra post
    $$ Hcert Hpacket Hcode Hrun Hresv [Hstack Htimer Hwit Hhw Hshot Hframe] [Hfinish]
  · dsimp only [extra]
    iframe
  · iunfold KptJal.cycleFinish
    iunfold KptJal.guards
    iapply MycpuKpt.fetch_guards_intro
    iintro %trace %after %completed !> %nextTick Hresources
    iunfold KptJal.cycleResources at Hresources
    icases Hresources with ⟨Hpacket,Hcode,Hrun,Hresv,Hreceipts,Hextra⟩
    isimp only [extra] at Hextra
    icases Hextra with ⟨Hstack,Htimer,Hwit,Hhw,Hshot,Hframe⟩
    ihave Hopened : SieOffPacket.opened capacity fixed gen era cpu .full ξ (afterFile pc file)
        available (.kpt root) after $$ [Hpacket Hrun Hresv Hstack Htimer Hwit Hhw Hshot]
    · unfold SieOffPacket.opened SieOffPacket.frame
      simp only [SieOffPacket.Regime.shell,SieOffPacket.slotToken,stack]
      iframe Hpacket Hstack Hrun Htimer Hwit Hhw Hshot
      unfold Reservations.resvAny
      iexists none
      iexact Hresv
    ihave Hsource := (SieOffPacket.nativeSpec capacity).close_packet fixed gen era cpu .full ξ
      (afterFile pc file) available (KptJal.target pc imm) (.kpt root) after
      (boundary pc imm control after ambient.toBoundary completed) $$ Hopened
    iunfold finish at Hfinish
    iapply Hfinish $$ [Hsource Hcode Hframe] %nextTick
    iunfold restored
    iframe Hsource Hcode Hpma Hframe

theorem actual (jal : KptJal.Spec capacity) : Spec capacity := ⟨wp_cycle capacity jal⟩

end Xv6.Kernel.KptJalSconf
