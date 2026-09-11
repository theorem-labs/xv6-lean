import MachCSL.Logic.DeadThreadDefs
import MachCSL.Logic.EraSpec
import MachCSL.Logic.ObservationInvariantDefs

namespace MachCSL.Logic.PowerWP
open Iris Iris.BI MachCSL.Machine

/-- Explicit outstanding boot obligation, quantified over every actual boot
result, including arbitrary preboot registers. All eleven fork WPs are owed. -/
def bootHandler {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (template : Era.Record) : IProp GF :=
  iprop(□ ∀ (g : State) (era : Era.Record) (memory : Tso.AddressMap Memory.Byte),
    ⌜BootFacts image g⌝ -∗ ⌜Memory.FiniteMap.decode memory = g.memory⌝ -∗
    ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ -∗
    MachineInterp.generationCertificate capacity fixed g.generation era -∗
    Era.bootClients capacity.era era memory g fixed.diskSize ={⊤}=∗
    [∗list] thread ∈ powerFork g.generation,
      DeadThread.threadWP capacity image fixed whole thread (fun _ => iprop(True)))

end MachCSL.Logic.PowerWP
