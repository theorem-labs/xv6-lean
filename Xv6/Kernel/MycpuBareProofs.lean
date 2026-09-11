import Xv6.Kernel.MycpuBareSpec
import Xv6.Kernel.MycpuBareReference
import Xv6.Kernel.MycpuBareConfig
import Xv6.Kernel.MycpuCycleLink

namespace Xv6.Kernel.MycpuBare
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open TsoContextReadWP

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

private def finish (shares : Shares) (frameShares : FrameShares) (entry : RegisterFile)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result entry after⌝ -∗
    cells capacity era cpu after shares -∗ calleeFrame capacity era cpu after frameShares -∗
    running capacity era cpu ξ -∗ shared capacity era -∗
    stackWords capacity era ξ entry (entry .x1) (entry .x8) -∗
    Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
    ∀ nextTick, RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post)

private abbrev raAt (entry : RegisterFile) (old : BitVec 64) (k : Nat) : BitVec 64 :=
  if k ≤ 1 then old else entry .x1
private abbrev s0At (entry : RegisterFile) (old : BitVec 64) (k : Nat) : BitVec 64 :=
  if k ≤ 2 then old else entry .x8
private abbrev reservationAt (initial : Option Reservation) (k : Nat) : Option Reservation :=
  if k = 0 then initial else none

omit [Platform] in
theorem calleeFrame_result era cpu entry after shares (saved : CalleeSaved.Preserved entry after) :
    calleeFrame capacity era cpu after shares = calleeFrame capacity era cpu entry shares := by
  have h (r : Register) (member : r ∈ CalleeSaved.registers) := saved r member
  simp only [calleeFrame, frameFootprint, remainingSaved, List.map_cons, List.map_nil,
    RegisterFootprint.cells, h .x9 (by decide), h .x18 (by decide), h .x19 (by decide),
    h .x20 (by decide), h .x21 (by decide), h .x22 (by decide), h .x23 (by decide),
    h .x24 (by decide), h .x25 (by decide), h .x26 (by decide), h .x27 (by decide)]

set_option maxHeartbeats 2000000 in
private theorem chain shares frameShares entry (config : EntryConfig entry)
    image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) initial post
    (raRange : SupervisorPhysical.RamRange (raSlot entry) 8)
    (s0Range : SupervisorPhysical.RamRange (s0Slot entry) 8) (fuel : Nat) :
    ∀ k, k + fuel = 14 → ∀ rs, Phase entry k rs → ∀ tick,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ calleeFrame capacity era cpu entry frameShares -∗
      running capacity era cpu ξ -∗ shared capacity era -∗
      wordPointsto capacity era ξ (raSlot entry) (.own 1) (raAt entry oldRA k) -∗
      wordPointsto capacity era ξ (s0Slot entry) (.own 1) (s0At entry oldS0 k) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu (reservationAt initial k) -∗
      finish capacity shares frameShares entry image fixed whole gen era cpu ξ post -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle tick)) post) := by
  induction fuel with
  | zero =>
    intro k bound rs phase tick
    have eq : k = 14 := by omega
    subst k
    iintro #Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    isimp [raAt] at Hra
    isimp [s0At] at Hs0
    isimp [reservationAt] at Hresv
    have result := phase_result config phase
    have frameEq := calleeFrame_result capacity era cpu entry rs frameShares result.saved
    isimp only [← frameEq] at Hframe
    ihave Hwords : stackWords capacity era ξ entry (entry .x1) (entry .x8) $$ [Hra Hs0]
    ·
      unfold stackWords
      iframe Hra Hs0
    isimp only [finish] at Hfinish
    iapply Hfinish $$ %rs %result Hregs Hframe Hrun Hspan Hwords Hresv %tick
  | succ fuel ih =>
    intro k bound rs phase tick
    iintro #Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    have lt : k < 14 := by omega
    have supervisor := stable_config config.toSupervisorConfig (phase_stable entry k rs phase)
    have pc := phase_address config.pc phase lt
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨0, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨0, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨0, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ initial tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 1 after := phase_next entry 0 rs after phase completed
      have next := ih 1 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨1, by decide⟩ pc
      have address := phase_stack_address phase (by decide) (by decide) .ra
      have dataRange : SupervisorPhysical.RamRange (MycpuMemory.address .ra rs) 8 := by
        rw [address]
        exact raRange
      have memoryConfig := supervisor_write supervisor .ra dataRange
      isimp only [← address] at Hra
      iapply MycpuCycle.wp_store capacity .ra shares rs ramRegion ramRegion cycleConfig memoryConfig
        image fixed whole gen era cpu ξ oldRA
        none tick post $$ Hcert Hregs Hrun Hspan Hra Hresv
      iintro !> !> !> %fetchView %dataView %after %completed %nextTick Hregs Hrun Hspan Hra Hresv Hfetch Hdata
      isimp only [address, phase_store_ra phase] at Hra
      have phase' : Phase entry 2 after := phase_next entry 1 rs after phase completed
      have next := ih 2 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨2, by decide⟩ pc
      have address := phase_stack_address phase (by decide) (by decide) .s0
      have dataRange : SupervisorPhysical.RamRange (MycpuMemory.address .s0 rs) 8 := by
        rw [address]
        exact s0Range
      have memoryConfig := supervisor_write supervisor .s0 dataRange
      isimp only [← address] at Hs0
      iapply MycpuCycle.wp_store capacity .s0 shares rs ramRegion ramRegion cycleConfig memoryConfig
        image fixed whole gen era cpu ξ oldS0
        none tick post $$ Hcert Hregs Hrun Hspan Hs0 Hresv
      iintro !> !> !> %fetchView %dataView %after %completed %nextTick Hregs Hrun Hspan Hs0 Hresv Hfetch Hdata
      isimp only [address, phase_store_s0 phase] at Hs0
      have phase' : Phase entry 3 after := phase_next entry 2 rs after phase completed
      have next := ih 3 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨3, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨1, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨1, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 4 after := phase_next entry 3 rs after phase completed
      have next := ih 4 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨4, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨2, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨2, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 5 after := phase_next entry 4 rs after phase completed
      have next := ih 5 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨5, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨3, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨3, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 6 after := phase_next entry 5 rs after phase completed
      have next := ih 6 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨6, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨4, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨4, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 7 after := phase_next entry 6 rs after phase completed
      have next := ih 7 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨7, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨5, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨5, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 8 after := phase_next entry 7 rs after phase completed
      have next := ih 8 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨8, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨6, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨6, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 9 after := phase_next entry 8 rs after phase completed
      have next := ih 9 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨9, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨7, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨7, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 10 after := phase_next entry 9 rs after phase completed
      have next := ih 10 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨10, by decide⟩ pc
      have address := phase_stack_address phase (by decide) (by decide) .ra
      have dataRange : SupervisorPhysical.RamRange (MycpuMemory.address .ra rs) 8 := by
        rw [address]
        exact raRange
      have memoryConfig := supervisor_read supervisor .ra dataRange
      isimp only [← address] at Hra
      iapply MycpuCycle.wp_load capacity .ra shares rs ramRegion ramRegion cycleConfig memoryConfig
        image fixed whole gen era cpu ξ (.own 1) (entry .x1)
        none tick post $$ Hcert Hregs Hrun Hspan Hra Hresv
      iintro !> !> !> %fetchView %dataView %after %completed %nextTick Hregs Hrun Hspan Hra Hresv Hfetch Hdata
      isimp only [address] at Hra
      have phase' : Phase entry 11 after := phase_next entry 10 rs after phase completed
      have next := ih 11 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨11, by decide⟩ pc
      have address := phase_stack_address phase (by decide) (by decide) .s0
      have dataRange : SupervisorPhysical.RamRange (MycpuMemory.address .s0 rs) 8 := by
        rw [address]
        exact s0Range
      have memoryConfig := supervisor_read supervisor .s0 dataRange
      isimp only [← address] at Hs0
      iapply MycpuCycle.wp_load capacity .s0 shares rs ramRegion ramRegion cycleConfig memoryConfig
        image fixed whole gen era cpu ξ (.own 1) (entry .x8)
        none tick post $$ Hcert Hregs Hrun Hspan Hs0 Hresv
      iintro !> !> !> %fetchView %dataView %after %completed %nextTick Hregs Hrun Hspan Hs0 Hresv Hfetch Hdata
      isimp only [address] at Hs0
      have phase' : Phase entry 12 after := phase_next entry 11 rs after phase completed
      have next := ih 12 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨12, by decide⟩ pc
      have scalarConfig : MycpuCycle.Config rs (MycpuScalar.index ⟨8, by decide⟩) ramRegion := by
        simpa only [MycpuScalar.index] using cycleConfig
      iapply MycpuCycle.wp_scalar capacity shares rs (⟨8, by decide⟩ : Fin 9) ramRegion scalarConfig
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 13 after := phase_next entry 12 rs after phase completed
      have next := ih 13 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish
    · isimp [raAt] at Hra
      isimp [s0At] at Hs0
      isimp [reservationAt] at Hresv
      have cycleConfig := supervisor_cycle supervisor ⟨13, by decide⟩ pc
      iapply MycpuCycle.wp_return capacity shares rs ramRegion cycleConfig (supervisor_return supervisor)
        image fixed whole gen era cpu ξ none tick post $$ Hcert Hregs Hrun Hspan Hresv
      iintro !> !> %fetchView %after %completed %nextTick Hregs Hrun Hspan Hresv Hfetch
      have phase' : Phase entry 14 after := phase_next entry 13 rs after phase completed
      have next := ih 14 (by omega) after phase' nextTick
      simp [raAt, s0At, reservationAt] at next
      iapply next $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish

theorem wp_function shares frameShares entry (config : EntryConfig entry)
    image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu entry shares -∗ calleeFrame capacity era cpu entry frameShares -∗
      running capacity era cpu ξ -∗ shared capacity era -∗
      stackWords capacity era ξ entry oldRA oldS0 -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜Result entry after⌝ -∗
        cells capacity era cpu after shares -∗ calleeFrame capacity era cpu after frameShares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        stackWords capacity era ξ entry (entry .x1) (entry .x8) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle initialTick)) post) := by
  iintro #Hcert Hregs Hframe Hrun Hspan Hwords Hresv Hfinish
  iunfold stackWords at Hwords
  icases Hwords with ⟨Hra, Hs0⟩
  ihave %raRange := word_range capacity era ξ (raSlot entry) (.own 1) oldRA $$ Hra
  ihave %s0Range := word_range capacity era ξ (s0Slot entry) (.own 1) oldS0 $$ Hs0
  have first := chain capacity shares frameShares entry config image fixed whole gen era cpu ξ
    oldRA oldS0 rr post raRange s0Range 14 0 (by decide) entry (phase_zero entry) initialTick
  simp only [raAt, s0At, reservationAt, finish, Nat.zero_le, if_true] at first
  iapply first $$ Hcert Hregs Hframe Hrun Hspan Hra Hs0 Hresv Hfinish

theorem wp_hart shares frameShares entry (config : EntryConfig entry)
    image fixed whole gen era cpu ξ (oldRA oldS0 : BitVec 64) rr initialTick post
    (tp : entry .x4 = BitVec.ofNat 64 cpu.val) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu entry shares -∗ calleeFrame capacity era cpu entry frameShares -∗
      running capacity era cpu ξ -∗ shared capacity era -∗
      stackWords capacity era ξ entry oldRA oldS0 -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      (∀ after, ⌜HartResult entry after cpu⌝ -∗
        cells capacity era cpu after shares -∗ calleeFrame capacity era cpu after frameShares -∗
        running capacity era cpu ξ -∗ shared capacity era -∗
        stackWords capacity era ξ entry (entry .x1) (entry .x8) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        ∀ nextTick, RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle nextTick)) post) -∗
      RegisterWP.threadWP capacity image fixed whole (.hart gen cpu (cycle initialTick)) post) := by
  iintro #Hcert Hregs Hframe Hrun Hspan Hwords Hresv Hfinish
  iapply wp_function capacity shares frameShares entry config image fixed whole gen era cpu ξ
    oldRA oldS0 rr initialTick post $$ Hcert Hregs Hframe Hrun Hspan Hwords Hresv
  iintro %after %result Hregs Hframe Hrun Hspan Hwords Hresv %nextTick
  have exactResult : HartResult entry after cpu := ⟨result, by
    rw [result.value, tp]
    exact MycpuScalar.valid_hart cpu⟩
  iapply Hfinish $$ %after %exactResult Hregs Hframe Hrun Hspan Hwords Hresv %nextTick

theorem actual : Spec capacity := ⟨wp_function capacity, wp_hart capacity⟩

end Xv6.Kernel.MycpuBare
