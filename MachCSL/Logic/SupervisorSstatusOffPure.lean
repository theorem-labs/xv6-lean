import MachCSL.Logic.SupervisorSstatusOffSpec
namespace MachCSL.Logic.SupervisorSstatusOff
open Iris MachCSL.Machine LeanPaperStock.Functions
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem supports_landing_pad : hartSupports .Ext_Zicfilp = true := by unfold hartSupports; rfl

theorem lower_SIE (ms : BitVec 64) : _get_Sstatus_SIE (lower_mstatus ms) = _get_Mstatus_SIE ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SIE, _get_Mstatus_SIE, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_SPIE (ms : BitVec 64) : _get_Sstatus_SPIE (lower_mstatus ms) = _get_Mstatus_SPIE ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SPIE, _get_Mstatus_SPIE, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_SPP (ms : BitVec 64) : _get_Sstatus_SPP (lower_mstatus ms) = _get_Mstatus_SPP ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SPP, _get_Mstatus_SPP, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_VS (ms : BitVec 64) : _get_Sstatus_VS (lower_mstatus ms) = _get_Mstatus_VS ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 2
  · have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_VS, _get_Mstatus_VS, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_FS (ms : BitVec 64) : _get_Sstatus_FS (lower_mstatus ms) = _get_Mstatus_FS ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 2
  · have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_FS, _get_Mstatus_FS, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_XS (ms : BitVec 64) : _get_Sstatus_XS (lower_mstatus ms) = _get_Mstatus_XS ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 2
  · have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_XS, _get_Mstatus_XS, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_SUM (ms : BitVec 64) : _get_Sstatus_SUM (lower_mstatus ms) = _get_Mstatus_SUM ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SUM, _get_Mstatus_SUM, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_MXR (ms : BitVec 64) : _get_Sstatus_MXR (lower_mstatus ms) = _get_Mstatus_MXR ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_MXR, _get_Mstatus_MXR, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_SPELP (ms : BitVec 64) : _get_Sstatus_SPELP (lower_mstatus ms) = _get_Mstatus_SPELP ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SPELP, _get_Mstatus_SPELP, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_UXL (ms : BitVec 64) : _get_Sstatus_UXL (lower_mstatus ms) = _get_Mstatus_UXL ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 2
  · have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_UXL, _get_Mstatus_UXL, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem lower_SD (ms : BitVec 64) : _get_Sstatus_SD (lower_mstatus ms) = _get_Mstatus_SD ms := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 1
  · have cases : i = 0 := by omega
    rcases cases with rfl
    all_goals simp [lower_mstatus, Mk_Sstatus, _get_Sstatus_SD, _get_Mstatus_SD, _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.zeroExtend]
  · rw [BitVec.getLsbD_of_ge _ i (by omega), BitVec.getLsbD_of_ge _ i (by omega)]

theorem update_extract_self (x : BitVec w) (start len : Nat) :
 Sail.BitVec.updateSubrange' x start len (x.extractLsb' start len) = x := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 by_cases hs : i < start
 · simp [Sail.BitVec.updateSubrange', BitVec.zeroExtend, hi, hs]
 · have sub : start + (i-start) = i := by omega
   by_cases hl : i-start < len
   · simp [Sail.BitVec.updateSubrange', BitVec.zeroExtend, hi, hs, sub, hl]
   · simp [Sail.BitVec.updateSubrange', BitVec.zeroExtend, hi, hs, sub, hl]

theorem update_SIE_self (ms : BitVec 64) : _update_Mstatus_SIE ms (_get_Mstatus_SIE ms) = ms := by
  exact update_extract_self ms _ _

theorem update_SPIE_self (ms : BitVec 64) : _update_Mstatus_SPIE ms (_get_Mstatus_SPIE ms) = ms := by
  exact update_extract_self ms _ _

theorem update_SPP_self (ms : BitVec 64) : _update_Mstatus_SPP ms (_get_Mstatus_SPP ms) = ms := by
  exact update_extract_self ms _ _

theorem update_VS_self (ms : BitVec 64) : _update_Mstatus_VS ms (_get_Mstatus_VS ms) = ms := by
  exact update_extract_self ms _ _

theorem update_FS_self (ms : BitVec 64) : _update_Mstatus_FS ms (_get_Mstatus_FS ms) = ms := by
  exact update_extract_self ms _ _

theorem update_XS_self (ms : BitVec 64) : _update_Mstatus_XS ms (_get_Mstatus_XS ms) = ms := by
  exact update_extract_self ms _ _

theorem update_SUM_self (ms : BitVec 64) : _update_Mstatus_SUM ms (_get_Mstatus_SUM ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MXR_self (ms : BitVec 64) : _update_Mstatus_MXR ms (_get_Mstatus_MXR ms) = ms := by
  exact update_extract_self ms _ _

theorem update_SPELP_self (ms : BitVec 64) : _update_Mstatus_SPELP ms (_get_Mstatus_SPELP ms) = ms := by
  exact update_extract_self ms _ _

theorem update_UXL_self (ms : BitVec 64) : _update_Mstatus_UXL ms (_get_Mstatus_UXL ms) = ms := by
  exact update_extract_self ms _ _

theorem update_SD_self (ms : BitVec 64) : _update_Mstatus_SD ms (_get_Mstatus_SD ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MIE_self (ms : BitVec 64) : _update_Mstatus_MIE ms (_get_Mstatus_MIE ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MPIE_self (ms : BitVec 64) : _update_Mstatus_MPIE ms (_get_Mstatus_MPIE ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MPP_self (ms : BitVec 64) : _update_Mstatus_MPP ms (_get_Mstatus_MPP ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MPRV_self (ms : BitVec 64) : _update_Mstatus_MPRV ms (_get_Mstatus_MPRV ms) = ms := by
  exact update_extract_self ms _ _

theorem update_TVM_self (ms : BitVec 64) : _update_Mstatus_TVM ms (_get_Mstatus_TVM ms) = ms := by
  exact update_extract_self ms _ _

theorem update_TW_self (ms : BitVec 64) : _update_Mstatus_TW ms (_get_Mstatus_TW ms) = ms := by
  exact update_extract_self ms _ _

theorem update_TSR_self (ms : BitVec 64) : _update_Mstatus_TSR ms (_get_Mstatus_TSR ms) = ms := by
  exact update_extract_self ms _ _

theorem update_MPELP_self (ms : BitVec 64) : _update_Mstatus_MPELP ms (_get_Mstatus_MPELP ms) = ms := by
  exact update_extract_self ms _ _

theorem write_value (ms : BitVec 64) (off : _get_Mstatus_SIE ms = 0#1) :
    writeValue ms = lower_mstatus ms := by
  have bit : (lower_mstatus ms).getLsbD 1 = false := by
    have h := congrArg (fun x : BitVec 1 => x.getLsbD 0) (lower_SIE ms |>.trans off)
    simpa [Sail.BitVec.extractLsb, _get_Sstatus_SIE] using h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [writeValue, BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h : i = 1
  · subst i; simp only [bit, Bool.false_and]
  · have two : (2#64).getLsbD i = false := by
      change (BitVec.twoPow 64 1).getLsbD i = false
      simp [BitVec.getLsbD_twoPow, Ne.symm h]
    simp only [two, hi, decide_true, Bool.not_false, Bool.and_true]

theorem lift_lower (ms : BitVec 64) (facts : SupervisorBits.MsFacts ms) :
    lift_sstatus ms (lower_mstatus ms) = ms := by
  obtain ⟨mprv, sxl, mxr, tsr, xs, fs, vs, sd, mpp, tvm⟩ := facts
  unfold lift_sstatus
  simp only [lower_SIE, lower_SPIE, lower_SPP, lower_VS, lower_FS, lower_XS,
    lower_SUM, lower_MXR, lower_SPELP, lower_UXL]
  have dirty : bool_to_bit ((extStatus_map_backwards (_get_Mstatus_FS ms) == .Dirty) ||
    ((extStatus_map_backwards (_get_Mstatus_XS ms) == .Dirty) ||
      (extStatus_map_backwards (_get_Mstatus_VS ms) == .Dirty))) = _get_Mstatus_SD ms := by
    rw [fs, xs, vs, sd]; rfl
  rw [dirty]
  simp only [update_SD_self, update_UXL_self, update_SPELP_self, update_MXR_self,
    update_SUM_self, update_XS_self, update_FS_self, update_VS_self,
    update_SPP_self, update_SPIE_self, update_SIE_self]

theorem legalized_self (ms : BitVec 64) (facts : SupervisorBits.MsFacts ms) :
    legalized ms ms = ms := by
  obtain ⟨mprv, sxl, mxr, tsr, xs, fs, vs, sd, mpp, tvm⟩ := facts
  unfold legalized
  simp only [mpp, ite_true]
  have lfs : legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS ms) = _get_Mstatus_FS ms := by
    rw [fs]; rfl
  have lvs : legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS ms) = _get_Mstatus_VS ms := by
    rw [vs]; rfl
  rw [lfs, lvs, ← xs]
  simp only [update_MPELP_self, update_SPELP_self, update_TSR_self, update_TW_self,
    update_TVM_self, update_MXR_self, update_SUM_self, update_MPRV_self,
    update_XS_self, update_FS_self, update_VS_self, update_MPP_self,
    update_SPP_self, update_MPIE_self, update_SPIE_self, update_MIE_self, update_SIE_self]
  have dirty : bool_to_bit ((extStatus_map_backwards (_get_Mstatus_FS ms) == .Dirty) ||
    ((extStatus_map_backwards (_get_Mstatus_XS ms) == .Dirty) ||
      (extStatus_map_backwards (_get_Mstatus_VS ms) == .Dirty))) = _get_Mstatus_SD ms := by
    rw [fs, xs, vs, sd]; rfl
  rw [dirty, update_SD_self]

theorem result_self (ms : BitVec 64) (facts : SupervisorBits.MsFacts ms)
    (off : _get_Mstatus_SIE ms = 0#1) : result ms = ms := by
  rw [result, write_value ms off, lift_lower ms facts, legalized_self ms facts]

theorem result_facts (ms : BitVec 64) (facts : SupervisorBits.MsFacts ms)
    (off : _get_Mstatus_SIE ms = 0#1) : SupervisorBits.MsFacts (result ms) := by
  rw [result_self ms facts off]; exact facts

theorem result_bits (ms : BitVec 64) (facts : SupervisorBits.MsFacts ms)
    (off : _get_Mstatus_SIE ms = 0#1) :
    _get_Mstatus_SIE (result ms) = 0#1 ∧
    _get_Mstatus_SPP (result ms) = _get_Mstatus_SPP ms ∧
    _get_Mstatus_SPIE (result ms) = _get_Mstatus_SPIE ms ∧
    _get_Mstatus_SPELP (result ms) = _get_Mstatus_SPELP ms ∧
    _get_Mstatus_MPELP (result ms) = _get_Mstatus_MPELP ms := by
  rw [result_self ms facts off]; exact ⟨off, rfl, rfl, rfl, rfl⟩

theorem lower_sie_zero (ms : BitVec 64) (off : _get_Mstatus_SIE ms = 0#1) :
    _get_Sstatus_SIE (lower_mstatus ms) = 0#1 := (lower_SIE ms).trans off

end MachCSL.Logic.SupervisorSstatusOff
