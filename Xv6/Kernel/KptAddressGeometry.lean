import Xv6.Kernel.KptAddressSpec

namespace Xv6.Kernel.KptAddress
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

@[simp] theorem prepare_satp rs data : prepare rs data .satp = data.satp := by
  simp [prepare, MachCSL.Sail.Registers.write]
@[simp] theorem prepare_tlb rs data : prepare rs data .tlb = data.tlb := by
  simp [prepare, MachCSL.Sail.Registers.write]
@[simp] theorem prepare_cfg rs data : prepare rs data .pmpcfg_n = data.cfg := by
  simp [prepare, MachCSL.Sail.Registers.write]
@[simp] theorem prepare_addr rs data : prepare rs data .pmpaddr_n = data.addr := by
  simp [prepare, MachCSL.Sail.Registers.write]

theorem prepare_other rs data r (satp : r ≠ .satp) (tlb : r ≠ .tlb)
    (cfg : r ≠ .pmpcfg_n) (addr : r ≠ .pmpaddr_n) : prepare rs data r = rs r := by
  simp [prepare, MachCSL.Sail.Registers.write, Ne.symm satp, Ne.symm tlb, Ne.symm cfg, Ne.symm addr]

@[simp] theorem prepare_status rs data : prepare rs data .mstatus = rs .mstatus :=
  prepare_other rs data .mstatus (by decide) (by decide) (by decide) (by decide)
@[simp] theorem prepare_privilege rs data : prepare rs data .cur_privilege = rs .cur_privilege :=
  prepare_other rs data .cur_privilege (by decide) (by decide) (by decide) (by decide)
@[simp] theorem prepare_pma rs data : prepare rs data .pma_regions = rs .pma_regions :=
  prepare_other rs data .pma_regions (by decide) (by decide) (by decide) (by decide)
@[simp] theorem prepare_htif rs data : prepare rs data .htif_tohost_base = rs .htif_tohost_base :=
  prepare_other rs data .htif_tohost_base (by decide) (by decide) (by decide) (by decide)
@[simp] theorem prepare_environment rs data : prepare rs data .menvcfg = rs .menvcfg :=
  prepare_other rs data .menvcfg (by decide) (by decide) (by decide) (by decide)

theorem unique shares : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, Sv39Address.footprint, SupervisorBare.footprint,
    KptTranslate.footprint, KptMiss.footprint, KptAD.footprint, SupervisorPteAD.footprint,
    SupervisorPteRead.footprint, SupervisorRead.footprint]

theorem outer rs data root (ambient : Ambient rs) (rooted : KptResidue.SatpRooted root data.satp) :
    Sv39Address.Config (prepare rs data) root where
  privilege := by simpa using ambient.privilege
  sxl := by simpa using ambient.sxl
  rooted := by simpa using rooted

theorem controls rs data (ambient : Ambient rs)
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data)) :
    KptHardware.Controls (prepare rs data) where
  tor := tor
  htif := by simpa using ambient.htif
  pma := by simpa using ambient.pma

theorem effective rs data access (given : Sv39Address.Effective rs access) :
    Sv39Address.Effective (prepare rs data) access := by
  simpa [Sv39Address.Effective, SupervisorBare.Effective] using given

/-- A TLB replacement commutes with the other three disjoint components of
this proof-side description. This is not an equality with an unowned file. -/
theorem prepare_write_tlb rs data tlb :
    MachCSL.Sail.Registers.write (prepare rs data) .tlb tlb = prepare rs { data with tlb := tlb } := by
  funext r
  by_cases hs : r = .satp
  · subst r; simp [MachCSL.Sail.Registers.write]
  by_cases ht : r = .tlb
  · subst r; simp
  by_cases hc : r = .pmpcfg_n
  · subst r; simp [MachCSL.Sail.Registers.write]
  by_cases ha : r = .pmpaddr_n
  · subst r; simp [MachCSL.Sail.Registers.write]
  simp [MachCSL.Sail.Registers.write, Ne.symm ht, prepare_other rs data r hs ht hc ha,
    prepare_other rs { data with tlb := tlb } r hs ht hc ha]

theorem translate_after_only_tlb rs asid vpn p2 p1 ppn permission branch :
    KptTranslate.after rs asid vpn p2 p1 ppn permission branch =
      MachCSL.Sail.Registers.write rs .tlb
        (KptTranslate.after rs asid vpn p2 p1 ppn permission branch .tlb) := by
  cases branch with
  | hit a d update =>
    cases update <;> simp [KptTranslate.after, KptHit.after, Sv39Hit.updateAfter, KptAD.result,
      TlbCoherence.refreshAfter, MachCSL.Sail.Registers.write_current]
  | miss a d view2 view1 view0 update =>
    cases update <;> simp [KptTranslate.after, KptMiss.after, Sv39Tlb.after,
      MachCSL.Sail.Registers.write_current]

theorem after rs data address ppn permission tree p2 p1 a d branch :
    KptTranslate.after (prepare rs data) 0#16 (Sv39Address.vpn address) p2 p1 ppn permission branch =
      prepare rs (afterData rs data address ppn permission (.translated tree p2 p1 a d branch)) := by
  rw [translate_after_only_tlb, prepare_write_tlb]
  rfl

theorem preserved rs data address ppn permission outcome :
    let next := afterData rs data address ppn permission outcome
    next.satp = data.satp ∧ next.cfg = data.cfg ∧ next.addr = data.addr := by
  cases outcome <;> exact ⟨rfl,rfl,rfl⟩

theorem tor_of_vectors (old rs : RegisterFile) (data : Data)
    (cfg : data.cfg = old .pmpcfg_n) (addr : data.addr = old .pmpaddr_n)
    (tor : MachCSL.Machine.SupervisorPmp.TorRam old) :
    MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data) := by
  rcases tor with ⟨htor,hpositive,hx,hw,hr,hcovers⟩
  constructor <;> simpa only [MachCSL.Machine.SupervisorPmp.entry0,
    MachCSL.Machine.SupervisorPmp.upper0, prepare_cfg, prepare_addr, cfg, addr] using
    (by assumption)

theorem tor_after rs data address ppn permission outcome
    (tor : MachCSL.Machine.SupervisorPmp.TorRam (prepare rs data)) :
    MachCSL.Machine.SupervisorPmp.TorRam (prepare rs (afterData rs data address ppn permission outcome)) :=
  tor_of_vectors (prepare rs data) rs _ (by simp [(preserved rs data address ppn permission outcome).2.1])
    (by simp [(preserved rs data address ppn permission outcome).2.2]) tor

theorem pureSpec : PureSpec := ⟨unique, outer, controls, effective, after, preserved⟩

end Xv6.Kernel.KptAddress
