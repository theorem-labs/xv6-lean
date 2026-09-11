import MachCSL.Logic.SupervisorBareWriteSpec
import MachCSL.Logic.SupervisorBareWritePlan
import MachCSL.Logic.SupervisorWriteProofs

namespace MachCSL.Logic.SupervisorBareWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions TsoContextReadWP

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorBareFetch.footprint,
    SupervisorBare.footprint, SupervisorFetchRead.footprint]

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Actual Bare virtual store with alignment derived from the owned word.
The complete permission/translation prefix is constructed, not assumed. -/
theorem wp_write (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    image fixed whole gen era cpu ξ (old new : BitVec 64) rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address new >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ address (.own 1) old $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := virtual_boundary shares rs address new region config aligned
  have gate := SupervisorWrite.Boundary.fold capacity (footprint shares) (footprint_unique shares)
    rs (SupervisorWrite.request address new) (program address new) tail cut old new rfl
    (SupervisorWrite.request_ram address new config.range) (by rfl)
    image fixed whole gen era cpu ξ rr continuation post
  rw [show (SupervisorWrite.request address new).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword Hresv
  iintro !> %view Hregs Hrun Hword Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_write capacity⟩

end MachCSL.Logic.SupervisorBareWrite
