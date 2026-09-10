import Sail
import Sail.ConcurrencyInterfaceV1Free
import LeanPaperStock.Defs

open Sail ConcurrencyInterfaceV1

namespace Sail

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := Free.PreSail.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := Free.PreSail.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := Free.PreSail.undefined_unit ()
abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := Free.PreSail.undefined_bit ()
abbrev undefined_bool (_ : Unit) : SailM Bool := Free.PreSail.undefined_bool ()
abbrev undefined_int (_ : Unit) : SailM Int := Free.PreSail.undefined_int ()
abbrev undefined_range (low high : Int) : SailM Int := Free.PreSail.undefined_range low high
abbrev undefined_nat (_ : Unit) : SailM Nat := Free.PreSail.undefined_nat ()
abbrev undefined_string (_ : Unit) : SailM String := Free.PreSail.undefined_string ()
abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := Free.PreSail.undefined_bitvector n
abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := Free.PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := Free.PreSail.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := Free.PreSail.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := Free.PreSail.readReg reg

abbrev RegisterRef := @Sail.ConcurrencyInterfaceV1.RegisterRef Register RegisterType

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := Free.PreSail.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := Free.PreSail.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := Free.PreSail.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := Free.PreSail.assert p s

namespace ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1

abbrev sail_mem_write (req : Mem_write_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak) : SailM (Result (Option Bool) Arch.abort) :=
  Free.PreSail.sail_mem_write req

abbrev sail_mem_read (req : Mem_read_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak) : SailM (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := Free.PreSail.sail_mem_read req

abbrev sail_barrier (a : Arch.barrier) : SailM Unit := Free.PreSail.sail_barrier a

abbrev sail_cache_op (op : Arch.cache_op) : SailM Unit := Free.PreSail.sail_cache_op op
abbrev sail_tlbi (op : Arch.tlb_op) : SailM Unit := Free.PreSail.sail_tlbi op
abbrev sail_translation_start (ts : Arch.trans_start) : SailM Unit := Free.PreSail.sail_translation_start ts
abbrev sail_translation_end (te : Arch.trans_end) : SailM Unit := Free.PreSail.sail_translation_end te
abbrev sail_take_exception (f : Arch.fault) : SailM Unit := Free.PreSail.sail_take_exception f
abbrev sail_return_exception (a : Arch.pa) : SailM Unit := Free.PreSail.sail_return_exception a

end ConcurrencyInterfaceV1

abbrev cycle_count (a : Unit) : SailM Unit := Free.PreSail.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := Free.PreSail.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := Free.PreSail.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := Free.PreSail.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := Free.PreSail.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := Free.PreSail.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := Free.PreSail.PreSailME.run m

def SailME.throw (e : α) : SailME α β := Free.PreSail.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := Free.PreSail.sailTryCatchE e h

def unwrapValue (computation : SailM α)
    (pure : Free.IsPure computation := by exact True.intro) : α :=
  Free.unwrapValue computation pure

end Sail
