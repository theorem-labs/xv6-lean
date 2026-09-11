import MachCSL.Logic.SupervisorBareFetchDefs
import Xv6.Kernel.MycpuBootResourcesDefs

namespace Xv6.Kernel.MycpuFetch
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Shares where
  pc : DFrac
  misa : DFrac
  bare : SupervisorBareFetch.Shares

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.PC, shares.pc), (.misa, shares.misa)] ++ SupervisorBareFetch.footprint shares.bare

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

def result (i : Fin 14) : FetchResult :=
  if MycpuDecode.compressed i then .F_RVC (BitVec.ofNat 16 (MycpuDecode.encoding i))
  else .F_Base (BitVec.ofNat 32 (MycpuDecode.encoding i))

structure Config (rs : RegisterFile) (i : Fin 14) (region : PMA_Region) : Prop where
  pc : rs .PC = MycpuDecode.address i
  compressed : _get_Misa_C (rs .misa) = 1#1
  bare : SupervisorBare.Config rs
  pmp : SupervisorPmp.TorRam rs
  htif : rs .htif_tohost_base = none
  matched : matching_pma_region (rs .pma_regions) (.Physaddr (MycpuDecode.address i))
    (MycpuFetchBytes.width i) = some region
  executable : (override_PMA region.attributes .PBMT_PMA).executable = true

/-- The full original tail remains for all responses. Only the specified owned
word is proved to return immediately; other words may cause another fetch. -/
def FixedRead (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (address : BitVec 64) (n : Nat) (word : BitVec (8 * n))
    (program : SailM α) (value : α) : Prop :=
  ∃ tail, SupervisorFetchRead.Boundary fp rs (SupervisorFetchRead.request address n) program tail ∧
    (∀ tag, tail (.Ok (word, tag)) = pure value) ∧
    tail (.Err ()) = _root_.Sail.ConcurrencyInterfaceV1.Free.fail .Exit

abbrev window {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (ξ : TsoContext.CtxId) (dq : DFrac) (i : Fin 14) : IProp GF :=
  TsoContextBytesReadWP.window capacity era ξ (MycpuDecode.address i)
    (MycpuFetchBytes.width i) dq (MycpuFetchBytes.word i)

abbrev shared {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) : IProp GF :=
  MycpuBootResources.physicalSpan (MycpuBootResources.storeCapacity capacity.era)
    (MycpuBootResources.storeNames era) .discard

end Xv6.Kernel.MycpuFetch
