import Xv6.Kernel.JalSconfSpec
import Xv6.Kernel.BareJalSourceSpec
import Xv6.Kernel.KptJalSourceSpec
import Xv6.Kernel.MycpuSconfPure
import Xv6.Kernel.SieOffPacketLink

namespace Xv6.Kernel.JalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- Open the actual source slot once and dispatch to its native branch.
The final Link must supply both branch implementations. -/
theorem wp_cycle (bare : BareJalSource.Spec capacity) (kpt : KptJalSource.Spec capacity)
    image fixed whole gen era cpu tier ξ file available pc imm tick extra post
    (even : KptJal.TargetEven pc imm) :
    iprop(⊢ input capacity fixed gen era cpu tier ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨Hsource,Hcode,Hpma,Hextra⟩ Hfinish
  ihave ⟨%regime,%control,%ambient,%admitted,Hopened⟩ :=
    (SieOffPacket.nativeSpec capacity).open_packet fixed gen era cpu tier ξ file available pc $$ Hsource
  cases regime with
  | bare =>
    have ident := MycpuSconf.bare_tier tier admitted
    subst tier
    iapply bare.cycle image fixed whole gen era cpu ξ file available pc imm tick extra post even $$
      [Hopened Hcode Hpma Hextra] [Hfinish]
    · unfold BareJalSource.input BareJal.code
      iframe Hcode Hpma Hextra
      iexists control
      iframe Hopened
      ipureintro; exact ambient
    · iunfold BareJalSource.finish
      iintro Hrestored %nextTick
      iunfold finish at Hfinish
      iapply Hfinish $$ [Hrestored] %nextTick
      iunfold restored
      iunfold BareJalSource.restored at Hrestored
      isimp only [BareJal.code] at Hrestored
      iexact Hrestored
  | kpt root =>
    iapply kpt.cycle image fixed whole gen era cpu tier ξ file available pc imm tick extra post even $$
      [Hopened Hcode Hpma Hextra] [Hfinish]
    · unfold KptJalSource.input
      iframe Hcode Hpma Hextra
      iexists root,control
      iframe Hopened
      ipureintro; exact ambient
    · iunfold KptJalSource.finish
      iintro Hrestored %nextTick
      iunfold finish at Hfinish
      iapply Hfinish $$ [Hrestored] %nextTick
      ieval (change _ ⊢ KptJalSource.restored capacity fixed gen era cpu tier ξ file available pc imm extra)
      iexact Hrestored

theorem actual (bare : BareJalSource.Spec capacity) (kpt : KptJalSource.Spec capacity) : Spec capacity :=
  ⟨wp_cycle capacity bare kpt⟩

end Xv6.Kernel.JalSconf
