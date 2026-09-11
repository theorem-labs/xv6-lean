import MachCSL.Logic.SupervisorMemOuterDefs

namespace MachCSL.Logic.SupervisorMemOuter
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (physical : SupervisorRead.Shares) (rs : RegisterFile)
    (_priv : rs .cur_privilege = .Supervisor) (_clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (kind : SupervisorRead.Kind) (address : BitVec 64) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 8) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (_grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (SupervisorRead.access kind))
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : ReadResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorRead.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorRead.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (readProgram kind address >>= continuation)) post)
  write : ∀ (shares : Shares) (physical : SupervisorWrite.Shares) (rs : RegisterFile)
    (_priv : rs .cur_privilege = .Supervisor) (_clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 8) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (_grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    image fixed whole gen era cpu ξ (old new : BitVec 64) rr
    (continuation : SupervisorWrite.Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorWrite.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorWrite.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (writeProgram address new >>= continuation)) post)

end MachCSL.Logic.SupervisorMemOuter
