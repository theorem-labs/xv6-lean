import MachCSL.Logic.SupervisorFetchReadDefs
import MachCSL.Machine.SupervisorBareDefs
import MachCSL.Logic.SupervisorMemOuterDefs

namespace MachCSL.Logic.SupervisorBareFetch
open Iris MachCSL.Machine LeanPaperStock.Functions

structure Shares where
  translation : SupervisorBare.Shares
  physical : SupervisorFetchRead.Shares

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  SupervisorBare.footprint shares.translation ++ SupervisorFetchRead.footprint shares.physical

def outerShares (shares : Shares) : SupervisorMemOuter.Shares :=
  ⟨shares.translation.status, shares.translation.privilege⟩

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

def program (start address : BitVec 64) (n : Nat) : SailM (FetchBytes_Result n) :=
  fetch_bytes start address n

end MachCSL.Logic.SupervisorBareFetch
