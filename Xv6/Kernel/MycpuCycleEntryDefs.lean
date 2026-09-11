import Xv6.Kernel.MycpuCycleBodyDefs

namespace Xv6.Kernel.MycpuCycleEntry
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := MycpuCycleBody.Shares
abbrev cells := @MycpuCycleBody.cells
abbrev shared := @MycpuFetch.shared
abbrev prepared := MycpuActive.prepared

/-- Successful active-step result, before retirement and the clock. -/
def result (i : Fin 14) : Step :=
  .Step_Execute (.Retire_Success (), MycpuActive.instbits i)

/-- Configurations refer to the original file; preparation only changes nextPC. -/
abbrev Config := MycpuActive.Config

def scalarAfter (i : Fin 9) (rs : RegisterFile) : RegisterFile :=
  MycpuScalar.after i (prepared (MycpuScalar.index i) rs)
def loadAfter (slot : MycpuMemory.Slot) (rs : RegisterFile) (word : BitVec 64) : RegisterFile :=
  MycpuMemory.after slot (prepared (MycpuMemory.loadIndex slot) rs) word
def returnAfter (rs : RegisterFile) : RegisterFile :=
  MycpuReturn.after (prepared ⟨13, by decide⟩ rs)

end Xv6.Kernel.MycpuCycleEntry
