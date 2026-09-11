import MachCSL.Logic.SupervisorBareReadSpec
import MachCSL.Logic.SupervisorBareReadPlan
import MachCSL.Logic.SupervisorBareFetchProofs

namespace MachCSL.Logic.SupervisorBareRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
open SupervisorRead

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) :=
  SupervisorBareFetch.footprint_unique shares

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

theorem wp_read (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  ihave %aligned := TsoContextWord.aligned (TsoContextReadWP.contextCapacity capacity)
    (TsoContextReadWP.contextNames era) ξ address dq word $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := program_boundary shares rs address region config aligned
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs (request address)
    (program address) tail cut (SupervisorPhysical.device_ram address 8 config.range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (request address).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

theorem actual : Spec capacity := ⟨wp_read capacity⟩

end MachCSL.Logic.SupervisorBareRead
