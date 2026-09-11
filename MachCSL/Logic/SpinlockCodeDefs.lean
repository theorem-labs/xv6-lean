import MachCSL.Logic.BootWindowProofs
import MachCSL.Logic.JalBootResourcesShare
import MachCSL.Machine.SpinlockFetchDefs
import MachCSL.Logic.SpinlockBootResourcesDefs
import MachCSL.Logic.MemoryWriteWPDefs

namespace MachCSL.Logic.SpinlockCode
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

def instruction (era : Era.Record) (dq : DFrac) (i : Fin 17) : IProp GF :=
  iprop(TsoRead.byteWindow capacity.era.heap.ledger era.heap
    (SpinlockImage.instructionAddress i) 4 dq (SpinlockImage.word i) ∗
    TsoRead.pristineWindow capacity.era.heap.ledger era.timestamps
      (SpinlockImage.instructionAddress i) 4)

def allCode (era : Era.Record) (dq : DFrac) : IProp GF :=
  iprop([∗list] i ∈ List.finRange 17, instruction capacity era dq i)

def shared (era : Era.Record) : IProp GF :=
  iprop([∗set] _cpu ∈ GlobalRegisters.allCPUs,
    allCode capacity era (.own JalBootResources.codeShare))

end MachCSL.Logic.SpinlockCode
