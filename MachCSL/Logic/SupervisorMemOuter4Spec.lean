import MachCSL.Logic.SupervisorMemOuter4Defs

namespace MachCSL.Logic.SupervisorMemOuter4
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

/-- Exact raw factors, retaining both successful and error responses. -/
structure PureSpec : Prop where
  read_factor : ∀ address, readProgram address = (effective (.Load .Data) >>= fun priv =>
    mem_read_priv (.Load .Data) .PBMT_PMA priv (.Physaddr address) 4 false false false)
  read_supervisor : ∀ address,
    mem_read_priv (.Load .Data) .PBMT_PMA .Supervisor (.Physaddr address) 4 false false false =
      (SupervisorRead4.program address >>= fun response => pure (MemoryOpResult_drop_meta response))
  write_factor : ∀ address word, writeProgram address word = (effective (.Store .Data) >>= fun priv =>
    mem_write_value_priv_meta (.Physaddr address) 4 word (.Store .Data) .PBMT_PMA priv () false false false)
  write_supervisor : ∀ address word,
    mem_write_value_priv_meta (.Physaddr address) 4 word (.Store .Data) .PBMT_PMA .Supervisor () false false false =
      SupervisorWrite4.program address word

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  read : ∀ (shares : Shares) (physical : SupervisorRead4.Shares) (rs : RegisterFile)
    (_priv : rs .cur_privilege = .Supervisor) (_clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (_aligned : is_aligned_paddr (.Physaddr address) 4 = true) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 4) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (_grant : (override_PMA region.attributes .PBMT_PMA).readable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec 32)
    (continuation : ReadResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorRead4.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorRead4.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 4 dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (readProgram address >>= continuation)) post)
  write : ∀ (shares : Shares) (physical : SupervisorWrite4.Shares) (rs : RegisterFile)
    (_priv : rs .cur_privilege = .Supervisor) (_clear : _get_Mstatus_MPRV (rs .mstatus) = 0#1)
    (address : BitVec 64) (_aligned : is_aligned_paddr (.Physaddr address) 4 = true) (_config : Machine.SupervisorPmp.TorRam rs)
    (_range : SupervisorPhysical.RamRange address 4) (_disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (_matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 4 = some region)
    (_grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    image fixed whole gen era cpu ξ (old new : BitVec 32) rr
    (continuation : SupervisorWrite4.Result → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ SupervisorWrite4.cells capacity era cpu rs physical -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address 4 (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ SupervisorWrite4.cells capacity era cpu rs physical -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address 4 (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (writeProgram address new >>= continuation)) post)

end MachCSL.Logic.SupervisorMemOuter4
