-- =======================================================================================
--   This Sail RISC-V architecture model, comprising all files and
--   directories except where otherwise noted is subject the BSD
--   two-clause license in the LICENSE file.
--
--   SPDX-License-Identifier: BSD-2-Clause
-- =======================================================================================

import Sail.Sail
import LeanPaperStock.Defs

open Sail
open ConcurrencyInterfaceV1

def print_bits (_ : String) (_ : BitVec n) : Unit := ()
def print_string (_ : String) (_ : String) : Unit := ()
def prerr_string (_: String) : Unit := ()
def putchar {T} (_: T ) : Unit := ()
def string_of_int (z : Int) := s!"{z}"

-- The two arbitrary but fixed predicates of xv6iris_extras.v.
class Platform where
  match_reservation : Arch.pa → Bool
  valid_reservation : Unit → Bool

export Platform (match_reservation valid_reservation)

-- Exact pure/no-op definitions from the pinned paper's extras.
def load_reservation (_ : Arch.pa) (_ : Nat) : SailM Unit := pure ()
def cancel_reservation (_ : Unit) : SailM Unit := pure ()
def plat_term_write (_ : BitVec 8) : SailM Unit := pure ()
def sys_enable_experimental_extensions (_ : Unit) : Bool := false

-- No interpretations are supplied for unused pure foreign operations.
class UnboundPureHooks where
  riscv_f16Add : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f16Sub : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f16Mul : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f16Div : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f32Add : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f32Sub : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f32Mul : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f32Div : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f64Add : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f64Sub : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f64Mul : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f64Div : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f16MulAdd : BitVec 3 → BitVec 16 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f32MulAdd : BitVec 3 → BitVec 32 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f64MulAdd : BitVec 3 → BitVec 64 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f16Sqrt : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 16)
  riscv_f32Sqrt : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f64Sqrt : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f16ToI32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  riscv_f16ToUi32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  riscv_i32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  riscv_ui32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  riscv_f16ToI64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  riscv_f16ToUi64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  riscv_i64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  riscv_ui64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  riscv_f32ToI32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f32ToUi32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_i32ToF32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_ui32ToF32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  riscv_f32ToI64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  riscv_f32ToUi64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  riscv_i64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  riscv_ui64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  riscv_f64ToI32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  riscv_f64ToUi32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  riscv_i32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  riscv_ui32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  riscv_f64ToI64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f64ToUi64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_i64ToF64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_ui64ToF64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  riscv_f16ToF32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  riscv_f16ToF64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  riscv_f32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  riscv_f32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  riscv_f64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  riscv_f64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  riscv_f32ToBF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  riscv_f16Lt : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  riscv_f16Lt_quiet : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  riscv_f16Le : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  riscv_f16Le_quiet : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  riscv_f16Eq : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  riscv_f32Lt : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  riscv_f32Lt_quiet : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  riscv_f32Le : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  riscv_f32Le_quiet : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  riscv_f32Eq : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  riscv_f64Lt : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  riscv_f64Lt_quiet : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  riscv_f64Le : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  riscv_f64Le_quiet : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  riscv_f64Eq : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  riscv_f16roundToInt : BitVec 3 → BitVec 16 → Bool → (BitVec 5 × BitVec 16)
  riscv_f32roundToInt : BitVec 3 → BitVec 32 → Bool → (BitVec 5 × BitVec 32)
  riscv_f64roundToInt : BitVec 3 → BitVec 64 → Bool → (BitVec 5 × BitVec 64)

export UnboundPureHooks (riscv_f16Add riscv_f16Sub riscv_f16Mul riscv_f16Div riscv_f32Add riscv_f32Sub riscv_f32Mul riscv_f32Div riscv_f64Add riscv_f64Sub riscv_f64Mul riscv_f64Div riscv_f16MulAdd riscv_f32MulAdd riscv_f64MulAdd riscv_f16Sqrt riscv_f32Sqrt riscv_f64Sqrt riscv_f16ToI32 riscv_f16ToUi32 riscv_i32ToF16 riscv_ui32ToF16 riscv_f16ToI64 riscv_f16ToUi64 riscv_i64ToF16 riscv_ui64ToF16 riscv_f32ToI32 riscv_f32ToUi32 riscv_i32ToF32 riscv_ui32ToF32 riscv_f32ToI64 riscv_f32ToUi64 riscv_i64ToF32 riscv_ui64ToF32 riscv_f64ToI32 riscv_f64ToUi32 riscv_i32ToF64 riscv_ui32ToF64 riscv_f64ToI64 riscv_f64ToUi64 riscv_i64ToF64 riscv_ui64ToF64 riscv_f16ToF32 riscv_f16ToF64 riscv_f32ToF64 riscv_f32ToF16 riscv_f64ToF16 riscv_f64ToF32 riscv_f32ToBF16 riscv_f16Lt riscv_f16Lt_quiet riscv_f16Le riscv_f16Le_quiet riscv_f16Eq riscv_f32Lt riscv_f32Lt_quiet riscv_f32Le riscv_f32Le_quiet riscv_f32Eq riscv_f64Lt riscv_f64Lt_quiet riscv_f64Le riscv_f64Le_quiet riscv_f64Eq riscv_f16roundToInt riscv_f32roundToInt riscv_f64roundToInt)

-- No generated call reaches these hooks in the pinned configuration.
-- The entry-point audit rejects any dependency on this class or its projections.
-- If one becomes reachable, it needs an explicit Empty-result stuck event.
class UnboundEffectfulHooks where
  plat_term_read : Unit → SailM (BitVec 8)
  get_16_random_bits : Unit → SailM (BitVec 16)

export UnboundEffectfulHooks (plat_term_read get_16_random_bits)

-- Termination of currentlyEnabled
instance : SizeOf extension where
  sizeOf := extension.ctorIdx

macro_rules | `(tactic| decreasing_trivial) => `(tactic| decide)
