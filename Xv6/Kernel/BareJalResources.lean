import Xv6.Kernel.BareJalSpec
import Xv6.Kernel.BareJalFetchLink
import Xv6.Kernel.KptJalResources
import Xv6.Kernel.MycpuBareSourceResources
namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem remainder : restFootprint = [(.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.mie, .own 1), (.mideleg, .own 1), (.menvcfg, .own 1), (.elp, .discard), (.hart_state, .own 1), (.x1, .own 1), (.x2, .own 1), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x8, .own 1), (.x9, .own 1), (.x10, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x15, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)
instance code_persistent era pc imm : Persistent (code capacity era pc imm) := by
  unfold code; infer_instance

theorem partition era cpu control values :
    iprop(packet capacity era cpu control values ⊣⊢ ∃ satp pmp,
      ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗ ⌜SupervisorPmp.TorRam pmp⌝ ∗
      BareJalFetch.cells capacity.translation era cpu (entry (patch control satp pmp) cpu values) fetchShares ∗
      fetchFrame capacity era cpu (patch control satp pmp) values) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu .bare control values shares).to_eq]
  simp only [MycpuRegimeShell.translation,MycpuRegimeShell.bare,fetchFrame,BareJalFetch.cells,
    remainder,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint,SupervisorRetirement.retirementFootprint,SupervisorClock.clockFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list,
    shares,MycpuRegimeShell.sourceShares,fetchShares,BareJalFetch.footprint,
    SupervisorBareFetch.footprint,SupervisorBare.footprint,SupervisorFetchRead.footprint,
    SupervisorPmp.config,SupervisorPmp.footprint,List.cons_append,List.nil_append,RegisterFootprint.cells,entry,MycpuRegimeShell.entry,MycpuOff.entry,patch,MycpuBareSource.patch]
  constructor
  · iintro ⟨⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hcur_privilege,Hmisa,Hmie,Hmideleg,Hmenvcfg,Help,Hpma_regions,Hhtif_tohost_base,Hhart_state,Hmstatus,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩,Hbits,Hz,%satp,Hsatp,%mode,%pmp,%tor,Hpmp⟩
    icases Hpmp with ⟨Hpmpcfg_n,Hpmpaddr_n,_⟩
    iexists satp,pmp
    iframe
    isplitr
    · ipureintro; exact mode
    ipureintro; exact tor
  · iintro ⟨%satp,%pmp,%mode,%tor,⟨HPC,Hmisa,Hmstatus,Hcur_privilege,Hsatp,Hpma_regions,Hpmpcfg_n,Hpmpaddr_n,Hhtif_tohost_base,_⟩,⟨HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hmie,Hmideleg,Hmenvcfg,Help,Hhart_state,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩,Hbits,Hz⟩
    iframe HPC HnextPC Hminstret Hminstret_increment Hmcountinhibit Hminstretcfg Hmcycle Hmtime Hmip Hcur_privilege Hmisa Hmie Hmideleg Hmenvcfg Help Hpma_regions Hhtif_tohost_base Hhart_state Hmstatus Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17 Hx18 Hx19 Hx20 Hx21 Hx22 Hx23 Hx24 Hx25 Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hbits Hz
    iexists satp
    iframe Hsatp
    isplitr
    · ipureintro; exact mode
    iexists pmp
    iframe
    ipureintro; exact tor

theorem nativeResourceSpec : ResourceSpec capacity := ⟨partition capacity⟩
end Xv6.Kernel.BareJal
