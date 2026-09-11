import MachCSL.Logic.TsoReadAtProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.TsoReadAt
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Latest-value visibility at the existing shared machine capacity. -/
theorem registry_power_read (fixed : MachineInterp.FixedNames)
    (g : State) (gen : Nat) (era : Era.Record) (live : ThreadLive g gen)
    (cpu : CPU) (a : PhysicalAddress) (n : Nat) (dq : DFrac)
    (word : BitVec (8 * n)) (time : Nat) :
    iprop(⊢ MachineInterp.powerInterp UartGhost.machineCapacity fixed g -∗
      MachineInterp.generationCertificate UartGhost.machineCapacity fixed gen era -∗
      TsoRead.byteWindow UartGhost.ledgerCapacity era.heap a n dq word -∗
      timestampWindow UartGhost.ledgerCapacity era.timestamps a n dq time -∗
      Tso.Views.viewLB UartGhost.eraCapacity.views era.views era.logLength (hartAgent cpu) time -∗
      ⌜∀ view, g.views cpu ≤ view → ReadsBytes g.image g.log (hartAgent cpu) view a n word⌝) :=
  power_read UartGhost.machineCapacity fixed g gen era live cpu a n dq word time

end MachCSL.Logic.TsoReadAt
