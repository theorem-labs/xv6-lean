import Xv6.Kernel.MycpuBareSourceEntry
import Xv6.Kernel.MycpuOffSpec

namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_function (functionSpec : MycpuOff.Spec (bareCapacity capacity))
    image fixed whole gen era cpu ξ original available tick extra post (enough : 2 ≤ available) :
    iprop(⊢ input capacity fixed gen era cpu ξ original available extra -∗
      finish capacity image fixed whole gen era cpu ξ original available extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro Hinput Hfinish
  ihave ⟨%initial,%oldRA,%oldS0,%rr,%config,%ambient,Hresources⟩ :=
    open_entry capacity fixed gen era cpu ξ original available extra enough $$ Hinput
  ihave ⟨#Hcert,Hresources⟩ := certificate capacity fixed gen era cpu ξ (sp original) available
    initial original oldRA oldS0 rr extra $$ Hresources
  iunfold resources at Hresources
  icases Hresources with ⟨Hpacket,Hrun,Hcode,Hpair,Hresv,Hframe⟩
  ihave Hwords : MycpuOff.stackWords (bareCapacity capacity) era ξ initial cpu original oldRA oldS0 $$ [Hpair]
  · ieval (change _ ⊢ physicalPair capacity era ξ (sp original) oldRA oldS0)
    iexact Hpair
  have checked := functionSpec.function shares initial original config image fixed whole gen era cpu ξ
    oldRA oldS0 rr tick post
  simp only [bareCapacity] at checked
  isimp only [bareCapacity] at Hpacket Hwords
  iapply checked $$ Hcert Hpacket Hrun Hcode Hwords Hresv [Hfinish Hframe]
  iintro %after %good Hpacket Hrun Hcode Hwords Hresv %nextTick
  have sourceResult := result initial cpu original after good
  have sourceSP := stack initial cpu original after good
  have sourceBoundary := boundary initial cpu original after ambient.toBoundary good
  ihave Hresources : resources capacity fixed gen era cpu ξ (sp original) available
      after (MycpuOff.returnedMap original after) (original 1#5) (original 8#5) none extra $$
      [Hpacket Hrun Hcode Hwords Hresv Hframe]
  · unfold resources
    simp only [bareCapacity]
    iframe Hpacket Hrun Hcode Hresv Hframe
    ieval (change _ ⊢ MycpuOff.stackWords (bareCapacity capacity) era ξ initial cpu original (original 1#5) (original 8#5))
    isimp only [bareCapacity]
    iexact Hwords
  ihave Hrestored := close_entry capacity fixed gen era cpu ξ (sp original) available
    after (MycpuOff.returnedMap original after) (original 1#5) (original 8#5) none
    (returnPC cpu original) extra enough sourceSP sourceBoundary good.body.config.bare good.body.config.tor $$ Hresources
  iunfold finish at Hfinish
  iapply Hfinish $$ %(MycpuOff.returnedMap original after) %sourceResult Hrestored %nextTick

theorem actual (functionSpec : MycpuOff.Spec (bareCapacity capacity)) : Spec capacity :=
  ⟨wp_function capacity functionSpec⟩

end Xv6.Kernel.MycpuBareSource
