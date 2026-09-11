import MachCSL.Logic.BootWindowDefs
import MachCSL.Machine.SpinlockImageDefs

namespace MachCSL.Logic.SpinlockBootResources
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine

def codeWord (i : Fin 17) : BootWindow.Word :=
  ⟨SpinlockImage.instructionAddress i, 4, SpinlockImage.word i⟩

def lockWord : BootWindow.Word := ⟨SpinlockImage.lockAddress, 4, 0#32⟩
def counterWord : BootWindow.Word := ⟨SpinlockImage.counterAddress, 4, 0#32⟩

/-- Instruction order is the decoded image's order, followed by the two
separate writable words. No map order is imposed on the initial heap. -/
def codeWords : List BootWindow.Word := List.ofFn codeWord
def words : List BootWindow.Word := codeWords ++ [lockWord, counterWord]

variable {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF) (names : TsoStore.Names)

def codeWindows : IProp GF :=
  iprop([∗list] w ∈ codeWords,
    TsoStore.storedWindow capacity names w.address w.size w.value 0)

def lockWindow : IProp GF :=
  TsoStore.storedWindow capacity names SpinlockImage.lockAddress 4 0#32 0

def counterWindow : IProp GF :=
  TsoStore.storedWindow capacity names SpinlockImage.counterAddress 4 0#32 0

/-- Both exact residual maps, retaining all unselected full cells. -/
def remainder (memory : Tso.AddressMap Byte) : IProp GF :=
  iprop(BootWindow.mapBytes capacity.heap.ledger names.tso.ledger.bytes
      (JalBootResources.deleteKeys memory (BootWindow.wordKeys words)) ∗
    BootWindow.mapTimes capacity.heap.ledger names.tso.ledger.timestamps
      (JalBootResources.deleteKeys (Tso.Interp.bootTimestamps memory) (BootWindow.wordKeys words)))

def windows : IProp GF := iprop(codeWindows capacity names ∗
  lockWindow capacity names ∗ counterWindow capacity names)

end MachCSL.Logic.SpinlockBootResources
