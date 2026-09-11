import MachCSL.Logic.SupervisorRetirementFactorDefs
import MachCSL.Logic.SupervisorClockDefs
import MachCSL.Logic.RestartWPDefs

namespace MachCSL.Logic.SupervisorRetirement
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

def flag (mc : BitVec 32) (cfg : BitVec 64) (priv : Privilege) : Bool :=
  (_get_Counterin_IR mc == 0#1) && (counter_priv_filter_bit cfg priv == 0#1)

def setupAfter (rs : RegisterFile) (priv : Privilege) : RegisterFile :=
  Sail.Registers.write rs .minstret_increment (flag (rs .mcountinhibit) (rs .minstretcfg) priv)

def tickPCAfter (rs : RegisterFile) : RegisterFile :=
  Sail.Registers.write rs .PC (rs .nextPC)

def completeAfter (rs : RegisterFile) : RegisterFile :=
  if rs .minstret_increment then
    Sail.Registers.write (tickPCAfter rs) .minstret (_root_.Sail.BitVec.addInt (rs .minstret) 1)
  else tickPCAfter rs

def retirementFootprint : RegisterFootprint.Footprint :=
  [(.minstret, .own 1), (.minstret_increment, .own 1),
   (.mcountinhibit, .discard), (.minstretcfg, .discard)]

def pcFootprint : RegisterFootprint.Footprint :=
  [(.PC, .own 1), (.nextPC, .own 1)] ++ retirementFootprint ++
    SupervisorClock.clockFootprint

/-- Exact source `minstret_res`: two linear cells and two discarded cells. -/
def minstretRes {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (name : GName) : IProp GF :=
  iprop(∃ rs : RegisterFile, RegisterFootprint.cells capacity name rs retirementFootprint)

/-- Register part of `pc_is`, separated only to expose the actual restart's
reservation update without duplicating the reservation fragment. -/
def pcRegs {GF : BundledGFunctors} (capacity : Registers.Capacity GF)
    (name : GName) (pc : BitVec 64) : IProp GF :=
  iprop(Registers.regPointsto capacity name .PC (.own 1) pc ∗
    Registers.regPointsto capacity name .nextPC (.own 1) pc ∗
    minstretRes capacity name ∗ SupervisorClock.clockRes capacity name)

/-- Exact source `pc_is`, including the reservation token. Ambient fractional
privilege and active-hart cells are additional context, not silently included. -/
def pcIs {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (pc : BitVec 64) : IProp GF :=
  iprop(Registers.regPointsto capacity.era.registers (era.registers cpu) .PC (.own 1) pc ∗
    Registers.regPointsto capacity.era.registers (era.registers cpu) .nextPC (.own 1) pc ∗
    minstretRes capacity.era.registers (era.registers cpu) ∗
    SupervisorClock.clockRes capacity.era.registers (era.registers cpu) ∗
    Reservations.resvAny capacity.era.reservations era.reservations cpu)

/-- Readable extra cells may use any share. The caller owns each listed cell. -/
structure SetupMembers (fp : RegisterFootprint.Footprint) where
  privilege : DFrac
  inhibit : DFrac
  config : DFrac
  readPrivilege : (.cur_privilege, privilege) ∈ fp
  readInhibit : (.mcountinhibit, inhibit) ∈ fp
  readConfig : (.minstretcfg, config) ∈ fp
  writeFlag : (.minstret_increment, .own 1) ∈ fp

structure CompleteMembers (fp : RegisterFootprint.Footprint) where
  hart : DFrac
  next : DFrac
  readHart : (.hart_state, hart) ∈ fp
  readNext : (.nextPC, next) ∈ fp
  writePC : (.PC, .own 1) ∈ fp
  writeCounter : (.minstret, .own 1) ∈ fp
  readFlag : DFrac
  readFlagMember : (.minstret_increment, readFlag) ∈ fp

end MachCSL.Logic.SupervisorRetirement
