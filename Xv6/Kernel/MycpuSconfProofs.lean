import Xv6.Kernel.MycpuSconfPure
import Xv6.Kernel.MycpuBareSourceSpec
import Xv6.Kernel.MycpuKptSourceSpec
import Xv6.Kernel.SieOffPacketLink

namespace Xv6.Kernel.MycpuSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- The actual packet is opened exactly once. The native Link supplies
both existing branch implementations, including their complete cycles. -/
theorem wp_function (bare : MycpuBareSource.Spec capacity) (kpt : MycpuKptSource.Spec capacity)
    image fixed whole gen era cpu tier ξ original available tick extra post (enough : 2 ≤ available) :
    iprop(⊢ input capacity fixed gen era cpu tier ξ original available extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  unfold input
  iintro ⟨Hsource,Htext,Hpma,Hextra⟩ Hfinish
  ihave ⟨%regime,%control,%ambient,%admitted,Hopened⟩ :=
    (SieOffPacket.nativeSpec capacity).open_packet fixed gen era cpu tier ξ original available entryPC $$ Hsource
  cases regime with
  | bare =>
    have ident := bare_tier tier admitted
    subst tier
    iapply bare.function image fixed whole gen era cpu ξ original available tick extra post enough $$
      [Hopened Htext Hpma Hextra] [Hfinish]
    · unfold MycpuBareSource.input
      iframe Htext Hpma Hextra
      iexists control
      iframe Hopened
      ipureintro; exact ambient
    · iunfold MycpuBareSource.finish
      iintro %after %good Hrestored %nextTick
      iunfold finish at Hfinish
      iapply Hfinish $$ %after %(bare_result cpu original after good) [Hrestored] %nextTick
      ieval (change _ ⊢ MycpuBareSource.restored capacity fixed gen era cpu ξ after available (MycpuBareSource.returnPC cpu original) extra)
      iexact Hrestored
  | kpt root =>
    iapply kpt.function image fixed whole gen era cpu tier ξ original available tick extra post enough $$
      [Hopened Htext Hpma Hextra] [Hfinish]
    · unfold MycpuKptSource.sourceInput
      iframe Htext Hpma Hextra
      iexists root,control
      iframe Hopened
      ipureintro; exact ambient
    · iunfold MycpuKptSource.finish
      iintro %after %good Hrestored %nextTick
      iunfold finish at Hfinish
      iapply Hfinish $$ %after %(kpt_result cpu original after good) [Hrestored] %nextTick
      ieval (change _ ⊢ MycpuKptSource.sourceRestored capacity fixed gen era cpu tier ξ original after available extra)
      iexact Hrestored

theorem actual (bare : MycpuBareSource.Spec capacity) (kpt : MycpuKptSource.Spec capacity) : Spec capacity :=
  ⟨wp_function capacity bare kpt⟩

end Xv6.Kernel.MycpuSconf
