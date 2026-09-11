import Xv6.Kernel.MycpuBareSourceDefs

namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  config : ∀ control satp pmp, SieOffPacket.Ambient entryPC control →
    control .pma_regions = pmaBoot → _get_Satp64_Mode (Mk_Satp64 satp) = 0#4 →
    SupervisorPmp.TorRam pmp → MycpuOff.EntryConfig (patch control satp pmp)
  ambient : ∀ pc control satp pmp, SieOffPacket.Ambient pc control →
    SieOffPacket.Ambient pc (patch control satp pmp)
  result : ∀ control cpu original after, MycpuOff.Result control cpu original after →
    Result cpu original (MycpuOff.returnedMap original after)
  stack : ∀ control cpu original after, MycpuOff.Result control cpu original after →
    sp (MycpuOff.returnedMap original after) = sp original
  boundary : ∀ control cpu original after, SieOffPacket.Boundary entryPC control →
    MycpuOff.Result control cpu original after →
    SieOffPacket.Boundary (returnPC cpu original) after
  text : ∀ j : Nat, j < 34 → ∃ b,
    KernelTextImage.sourceMap (MycpuDecode.base + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte MycpuBootResources.spanWord j

/-- Resource transformations are actual native ownership laws. In
particular the caller supplies neither physical stack words nor a restoration
callback, and the Bare slot is opened to obtain its real three register cells. -/
structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  identity_word : ∀ era ξ address word,
    iprop(KernelDatum.word capacity.translation era .identity ξ address (.own 1) word ⊢
      TsoContextReadWP.wordPointsto capacity.machine era ξ address (.own 1) word ∗
      closeWord capacity era ξ address)
  text : ∀ era, iprop(KernelTextImage.text capacity.translation era .identity ⊢
    KernelTextImage.text capacity.translation era .identity ∗ MycpuBare.shared capacity.machine era)
  packet : ∀ era cpu control file,
    iprop(MycpuRegimeShell.resources capacity era cpu .bare control file MycpuRegimeShell.sourceShares ⊣⊢
      ∃ satp pmp, ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗ ⌜SupervisorPmp.TorRam pmp⌝ ∗
        MycpuOff.resources (bareCapacity capacity) era cpu (patch control satp pmp) file shares)
  open_entry : ∀ fixed gen era cpu ξ file available extra, 2 ≤ available →
    iprop(input capacity fixed gen era cpu ξ file available extra ⊢ ∃ control raWord s0Word rr,
      ⌜MycpuOff.EntryConfig control⌝ ∗ ⌜SieOffPacket.Ambient entryPC control⌝ ∗
      resources capacity fixed gen era cpu ξ (sp file) available control file raWord s0Word rr extra)
  close_entry : ∀ fixed gen era cpu ξ entrySP available control file raWord s0Word rr pc extra,
    2 ≤ available → sp file = entrySP → SieOffPacket.Boundary pc control →
    satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 (control .satp))) = some .Bare →
    SupervisorPmp.TorRam control →
    iprop(resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra ⊢
      restored capacity fixed gen era cpu ξ file available pc extra)
  certificate : ∀ fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra,
    iprop(resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu ξ entrySP available control file raWord s0Word rr extra)

/-- A real branch function rule. The only WP input is the caller's actual
returned-cycle continuation. It does not assert that identity tier forces Bare. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ image fixed whole gen era cpu ξ original available tick extra post,
    2 ≤ available →
    iprop(⊢ input capacity fixed gen era cpu ξ original available extra -∗
      finish capacity image fixed whole gen era cpu ξ original available extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuBareSource
