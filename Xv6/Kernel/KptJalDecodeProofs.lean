import Xv6.Kernel.KptJalEncodingProofs
import Xv6.Kernel.KptJalPlanProofs

namespace Xv6.Kernel.KptJal
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem low15_ne imm : (Sail.BitVec.extractLsb (encoding imm) 14 0 == 0x6013#15) = false := by
  apply Bool.eq_false_iff.mpr
  intro same
  have eq := of_decide_eq_true same
  have low := congrArg (fun x : BitVec 15 => x.extractLsb' 0 7) eq
  have norm : (Sail.BitVec.extractLsb (encoding imm) 14 0).extractLsb' 0 7 = 0x6f#7 := by
    change ((encoding imm).extractLsb' 0 15).extractLsb' 0 7 = _
    rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
    exact opcode imm
  rw [norm] at low
  contradiction

private theorem low20_ne imm : (Sail.BitVec.extractLsb (encoding imm) 19 0 == 0x00033#20) = false := by
  apply Bool.eq_false_iff.mpr
  intro same
  have eq := of_decide_eq_true same
  have low := congrArg (fun x : BitVec 20 => x.extractLsb' 0 7) eq
  have norm : (Sail.BitVec.extractLsb (encoding imm) 19 0).extractLsb' 0 7 = 0x6f#7 := by
    change ((encoding imm).extractLsb' 0 20).extractLsb' 0 7 = _
    rw [BitVec.extractLsb'_extractLsb'_of_le (by decide)]
    exact opcode imm
  rw [norm] at low
  contradiction

private theorem pause_ne imm : (encoding imm == 0x0100000f#32) = false := by
  apply Bool.eq_false_iff.mpr
  intro same
  have low := congrArg (fun x : BitVec 32 => Sail.BitVec.extractLsb x 6 0) (of_decide_eq_true same)
  rw [opcode] at low
  contradiction

/-- Complete decoder prefix: even a JAL checks both earlier extension arms.
No register events from those checks are erased by the bitfield proof. -/
theorem decode_factor imm (even : Encodable imm) : ext_decode (encoding imm) =
    (currentlyEnabled .Ext_Zihintpause >>= fun _ => currentlyEnabled .Ext_Zicfilp >>= fun _ => pure (instruction imm)) := by
  have low12 : Sail.BitVec.extractLsb (encoding imm) 11 0 = 0xef#12 := slice_low imm
  unfold ext_decode encdec_backwards
  simp only [low15_ne,low20_ne,Bool.and_false,Bool.false_eq_true, if_false,BootPmp.sail_pure_bind]
  simp only [BootPmp.sail_bind_assoc]
  congr 1
  funext pause
  simp only [pause_ne,Bool.and_false,Bool.false_eq_true, if_false,BootPmp.sail_pure_bind]
  congr 1
  funext lpe
  simp only [low12,show (0xef#12 == 0x017#12) = false from rfl,Bool.and_false,Bool.false_eq_true, if_false, if_true,
    opcode,destination,show encdec_uop_backwards_matches 0x6f#7 = false from rfl,
    show encdec_reg_backwards_matches 1#5 = true from rfl, Bool.true_and,Bool.and_false,
    beq_self_eq_true,BootPmp.sail_pure_bind]
  simp only [show encdec_reg_backwards 1#5 = pure (.Regidx 1#5) from rfl,BootPmp.sail_pure_bind,
    field_sign,field_ten,field_middle,field_eight]
  exact congrArg (fun x : BitVec 21 => (pure (.JAL (x,.Regidx 1#5)) : SailM _root_.instruction))
    (reassemble imm even)

end Xv6.Kernel.KptJal
