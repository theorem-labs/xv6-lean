import Xv6.Kernel.MycpuKptFetchPureProofs
import Xv6.Kernel.MycpuRegimeShellResources
import Xv6.Kernel.KptFetchLink

namespace Xv6.Kernel.MycpuKptFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem remainder (s : Shares) : remainderFootprint s =
    [(.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.mie, s.enable), (.mideleg, s.delegation), (.elp, s.landing), (.hart_state, s.hart), (.x1, .own 1), (.x2, .own 1), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x8, .own 1), (.x9, .own 1), (.x10, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x15, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem cells_partition era cpu rs shares :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
      (MycpuRegimeShell.footprint shares) ⊣⊢
      KptFetch.cells capacity.translation era cpu rs (fetchShares shares) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (remainderFootprint shares)) := by
  simp only [KptFetch.cells,remainder,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint,SupervisorRetirement.retirementFootprint,SupervisorClock.clockFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list,
    fetchShares,KptFetch.footprint,KptFetchHalf.footprint,KptAddress.auxiliaryFootprint,
    List.cons_append,List.nil_append,RegisterFootprint.cells]
  constructor
  · iintro ⟨HPC, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hcur_privilege, Hmisa, Hmie, Hmideleg, Hmenvcfg, Help, Hpma_regions, Hhtif_tohost_base, Hhart_state, Hmstatus, Hx1, Hx2, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩
    iframe
  · iintro ⟨⟨HPC, Hmisa, Hmstatus, Hcur_privilege, Hpma_regions, Hhtif_tohost_base, Hmenvcfg, _⟩,⟨HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hmie, Hmideleg, Help, Hhart_state, Hx1, Hx2, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩⟩
    iframe

theorem packet_partition era cpu control values shares N root :
    iprop(packet capacity era cpu (.kpt N root) control values shares ⊣⊢
      KptFetch.cells capacity.translation era cpu (entry control cpu values) (fetchShares shares) ∗
      packetFrame capacity era cpu control values shares ∗ KptResidue.residue capacity.translation era cpu N root) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu (.kpt N root) control values shares).to_eq,
    (cells_partition capacity era cpu (entry control cpu values) shares).to_eq]
  unfold packetFrame MycpuRegimeShell.translation
  constructor
  · iintro ⟨⟨Hcells,Hrest⟩,Hbits,Hz,Hresidue⟩; iframe
  · iintro ⟨Hcells,⟨Hrest,Hbits,Hz⟩,Hresidue⟩; iframe

instance window_persistent era tier i : Persistent (window capacity era tier i) := by
  unfold window; infer_instance
instance code_persistent era tier : Persistent (code capacity era tier) := by
  unfold code; infer_instance
instance code_timeless era tier : Timeless (code capacity era tier) := by
  unfold code window; infer_instance

theorem code_window era tier i : iprop(code capacity era tier ⊢ window capacity era tier i) :=
  BigSepL.bigSepL_mem (by simp : i ∈ List.finRange 14)

theorem window_width era tier i n (width : MycpuFetchBytes.width i = n) :
    window capacity era tier i = KernelTextDatum.window capacity.translation era tier
      (MycpuDecode.address i) n .discard (BitVec.ofNat (8*n) (MycpuFetchBytes.encoding i)) := by
  subst n
  rfl

/-- Each concrete source window supplies the exact InstrBytes shape. -/
theorem window_instruction era tier (i : Fin 14) : iprop(window capacity era tier i ⊢
    KptFetch.instrBytes capacity.translation era tier (MycpuDecode.address i) (result i)) := by
  obtain ⟨i,bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have width : MycpuFetchBytes.width ⟨0,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (0 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨0,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (0 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨0,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨0,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨0,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨0,bound⟩ = MycpuDecode.encoding ⟨0,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨1,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (1 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨1,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (1 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨1,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨1,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨1,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨1,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨1,bound⟩
        · iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨2,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (2 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨2,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (2 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨2,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨2,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨2,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨2,bound⟩ = MycpuDecode.encoding ⟨2,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨3,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (3 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨3,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (3 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨3,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨3,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨3,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨3,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨3,bound⟩
        · iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨4,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (4 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨4,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (4 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨4,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨4,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨4,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨4,bound⟩ = MycpuDecode.encoding ⟨4,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨5,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (5 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨5,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (5 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨5,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨5,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨5,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨5,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨5,bound⟩
        · iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨6,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (6 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨6,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (6 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨6,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨6,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨6,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨6,bound⟩ = MycpuDecode.encoding ⟨6,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨7,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (7 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨7,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (7 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨7,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨7,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨7,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨7,bound⟩ = MycpuDecode.encoding ⟨7,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨8,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (8 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨8,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (8 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨8,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨8,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨8,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨8,bound⟩ = MycpuDecode.encoding ⟨8,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨9,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (9 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨9,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (9 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨9,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨9,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨9,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨9,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨9,bound⟩
        · iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨10,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (10 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨10,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (10 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨10,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨10,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨10,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨10,bound⟩ = MycpuDecode.encoding ⟨10,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨11,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (11 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨11,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (11 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨11,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨11,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨11,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨11,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨11,bound⟩
        · iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨12,bound⟩ = 2 :=
      (show MycpuFetchBytes.width (12 : Fin 14) = 2 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨12,bound⟩)) 4 = false :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (12 : Fin 14))) 4 = false from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨12,bound⟩ 2 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨12,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨12,bound⟩
      · have same : MycpuFetchBytes.encoding ⟨12,bound⟩ = MycpuDecode.encoding ⟨12,bound⟩ := rfl
        isimp only [same] at Hwindow
        iexact Hwindow
  · have width : MycpuFetchBytes.width ⟨13,bound⟩ = 4 :=
      (show MycpuFetchBytes.width (13 : Fin 14) = 4 from by decide)
    have four : is_aligned_vaddr (.Virtaddr (MycpuDecode.address ⟨13,bound⟩)) 4 = true :=
      (show is_aligned_vaddr (.Virtaddr (MycpuDecode.address (13 : Fin 14))) 4 = true from by decide)
    iintro Hwindow
    ieval (rewrite [window_width capacity era tier ⟨13,bound⟩ 4 width]) at Hwindow
    iunfold KptFetch.instrBytes
    isimp only [result,MycpuFetch.result,MycpuDecode.compressed,MycpuDecode.width,Nat.reduceBEq,
      Bool.false_eq_true,↓reduceIte,four]
    isplit
    · ipureintro; exact aligned_two ⟨13,bound⟩
    · isplit
      · ipureintro; exact MycpuDecode.compressed_tag ⟨13,bound⟩
      · iexists (BitVec.ofNat 32 (MycpuFetchBytes.encoding ⟨13,bound⟩))
        isplit
        · ipureintro; exact fetched_low ⟨13,bound⟩
        · iexact Hwindow

theorem code_instruction era tier i : iprop(code capacity era tier ⊢
    KptFetch.instrBytes capacity.translation era tier (MycpuDecode.address i) (result i)) := by
  iintro Hcode
  ihave Hwindow := code_window capacity era tier i $$ Hcode
  iapply window_instruction capacity era tier i $$ Hwindow

theorem nativeResourceSpec : ResourceSpec capacity :=
  ⟨code_persistent capacity,code_timeless capacity,code_window capacity,code_instruction capacity,
    packet_partition capacity⟩

end Xv6.Kernel.MycpuKptFetch
