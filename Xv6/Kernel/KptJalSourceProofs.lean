import Xv6.Kernel.KptJalSourcePure
import Xv6.Kernel.KptJalSpec
import Xv6.Kernel.MycpuKptEntryLink
import Xv6.Kernel.MycpuKptGuards

namespace Xv6.Kernel.KptJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- Conditional composition of the actual cycle interface. The final Link
must supply its native implementation before exporting a closed rule. -/
theorem wp_cycle (jal : KptJal.Spec capacity)
    image fixed whole gen era cpu tier ξ file available pc imm tick extra post
    (even : KptJal.TargetEven pc imm) :
    iprop(⊢ input capacity fixed gen era cpu tier ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨⟨%root,%control,%ambient,Hopened⟩,Hcode,#Hpma,Hextra⟩ Hfinish
  ihave ⟨%pma,Hopened⟩ := (SieOffPacket.nativeSpec capacity).boot_pma_from_cell
    fixed gen era cpu tier ξ file available (.kpt root) control $$ Hopened Hpma
  ihave ⟨#Hcert,Hopened⟩ := (SieOffPacket.nativeSpec capacity).certificate
    fixed gen era cpu tier ξ file available (.kpt root) control $$ Hopened
  isimp only [SieOffPacket.opened,SieOffPacket.frame,SieOffPacket.Regime.shell,
    SieOffPacket.slotToken,Reservations.resvAny] at Hopened
  icases Hopened with ⟨Hpacket,⟨Hstack,Hrun,Htimer,Hwit,Hhw,Hshot⟩,⟨%rr,Hresv⟩⟩
  iapply jal.cycle MycpuRegimeShell.sourceShares control file
    (MycpuKptEntry.config pc control ambient pma) pc imm ambient.pc_eq even
    tier ξ rr tick image fixed whole gen era cpu KptGhost.kptN root
    (sourceFrame capacity fixed gen era cpu tier ξ file available extra) post
    $$ Hcert Hpacket Hcode Hrun Hresv [Hstack Htimer Hwit Hhw Hshot Hextra] [Hfinish]
  · unfold sourceFrame
    iframe
  · iunfold KptJal.cycleFinish
    iunfold KptJal.guards
    iapply MycpuKpt.fetch_guards_intro
    iintro %trace %after %completed !> %nextTick Hresources
    iunfold KptJal.cycleResources at Hresources
    icases Hresources with ⟨Hpacket,Hcode,Hrun,Hresv,Hreceipts,Hframe⟩
    iunfold sourceFrame at Hframe
    icases Hframe with ⟨Hstack,Htimer,Hwit,Hhw,Hshot,Hextra⟩
    ihave Hopened : SieOffPacket.opened capacity fixed gen era cpu tier ξ (afterFile pc file)
        available (.kpt root) after $$ [Hpacket Hrun Hresv Hstack Htimer Hwit Hhw Hshot]
    · unfold SieOffPacket.opened SieOffPacket.frame
      simp only [SieOffPacket.Regime.shell,SieOffPacket.slotToken,stack]
      iframe Hpacket Hstack Hrun Htimer Hwit Hhw Hshot
      unfold Reservations.resvAny
      iexists none
      iexact Hresv
    ihave Hsource := (SieOffPacket.nativeSpec capacity).close_packet fixed gen era cpu tier ξ
      (afterFile pc file) available (KptJal.target pc imm) (.kpt root) after
      (boundary pc imm control after ambient.toBoundary completed) $$ Hopened
    iunfold finish at Hfinish
    iapply Hfinish $$ [Hsource Hcode Hextra] %nextTick
    iunfold restored
    iframe Hsource Hcode Hpma Hextra

theorem actual (jal : KptJal.Spec capacity) : Spec capacity := ⟨wp_cycle capacity jal⟩

end Xv6.Kernel.KptJalSource
