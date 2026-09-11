import Xv6.Generated.KernelMapsCode
import Xv6.Generated.KernelMapsData
import Xv6.Generated.KernelMapsMetadata
import Xv6.Generated.KernelMapsInstructions
import Xv6.Generated.KernelMapsProvenance

/-! Sparse maps imported from the pinned source lists, separately from the ELF.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
namespace Xv6.Kernel

abbrev codeRuns := Generated.KernelMaps.codeRuns
abbrev dataRuns := Generated.KernelMaps.dataRuns

def code : Elf.MemoryImage := runMap codeRuns
def data : Elf.MemoryImage := runMap dataRuns
def fileBytes : Elf.MemoryImage := Elf.union code data

def codeEntries := codeRuns.flatMap ByteRun.entries
def dataEntries := dataRuns.flatMap ByteRun.entries

abbrev entry := Generated.KernelMaps.kernelEntry
abbrev memoryBase := Generated.KernelMaps.kernelMemBase
abbrev memoryEnd := Generated.KernelMaps.kernelMemEnd
abbrev rodataEnd := Generated.KernelMaps.kernelRodataEnd
abbrev instruction := Generated.KernelMaps.instruction
abbrev symbols := Generated.KernelMaps.symbols
abbrev sections := Generated.KernelMaps.sections
abbrev segments := Generated.KernelMaps.segments

end Xv6.Kernel
