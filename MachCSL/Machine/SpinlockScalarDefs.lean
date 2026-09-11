import MachCSL.Machine.SpinlockDecodeDefs

namespace MachCSL.Machine.SpinlockScalar
open LeanPaperStock.Functions

/-- The seven straight-line register instructions in the integration image. -/
def index (i : Fin 7) : Fin 17 :=
  match i.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨3, by decide⟩
  | 2 => ⟨4, by decide⟩
  | 3 => ⟨5, by decide⟩
  | 4 => ⟨6, by decide⟩
  | 5 => ⟨8, by decide⟩
  | _ => ⟨11, by decide⟩

/-- Expected register effects, retaining arbitrary unrelated registers. -/
def after (i : Fin 7) (rs : RegisterFile) : RegisterFile :=
  match i.val with
  | 0 => Sail.Registers.write rs .x6
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (rs .x5) (sign_extend (m := 64) 2#12))))
  | 1 => Sail.Registers.write rs .x10 (rs .PC + sign_extend (m := 64) (1#20 +++ 0#12))
  | 2 => Sail.Registers.write rs .x10 (rs .x10 + sign_extend (m := 64) 0xff4#12)
  | 3 => Sail.Registers.write rs .x14 (0#64 + sign_extend (m := 64) 1#12)
  | 4 => Sail.Registers.write rs .x15 (rs .x14 + sign_extend (m := 64) 0#12)
  | 5 => Sail.Registers.write rs .x15
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (rs .x15 + sign_extend (m := 64) 0#12) 31 0))
  | _ => Sail.Registers.write rs .x16
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (rs .x16 + sign_extend (m := 64) 1#12) 31 0))

end MachCSL.Machine.SpinlockScalar
