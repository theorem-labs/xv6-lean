import Xv6.Kernel.MycpuCycleEntryDefs
import Xv6.Kernel.MycpuCycleShellDefs

namespace Xv6.Kernel.MycpuCycle
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := MycpuCycleBody.Shares
abbrev cells := @MycpuCycleBody.cells
abbrev shared := @MycpuFetch.shared
abbrev started := MycpuCycleShell.started
abbrev Completed := MycpuCycleShell.completed

/-- All source entry facts are stated before the actual retirement setup. -/
structure Config (rs : RegisterFile) (i : Fin 14) (region : PMA_Region) : Prop extends
    MycpuActive.Config rs i region where
  active : rs .hart_state = .HART_ACTIVE ()

def scalarBeforeFinish (i : Fin 9) (rs : RegisterFile) : RegisterFile :=
  MycpuCycleEntry.scalarAfter i (started rs)
def storeBeforeFinish (slot : MycpuMemory.Slot) (rs : RegisterFile) : RegisterFile :=
  MycpuActive.prepared (MycpuMemory.storeIndex slot) (started rs)
def loadBeforeFinish (slot : MycpuMemory.Slot) (rs : RegisterFile) (word : BitVec 64) : RegisterFile :=
  MycpuCycleEntry.loadAfter slot (started rs) word
def returnBeforeFinish (rs : RegisterFile) : RegisterFile :=
  MycpuCycleEntry.returnAfter (started rs)

end Xv6.Kernel.MycpuCycle
