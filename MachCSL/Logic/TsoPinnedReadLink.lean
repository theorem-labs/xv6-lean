import MachCSL.Logic.TsoPinnedReadProofs
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.TsoPinnedRead
open Iris

/-- Existing shared byte/timestamp/history/views capacity; no new slot or name. -/
theorem nativeSpec : ReadSpec FsBlockGhost.eraCapacity.tso := actual _

end MachCSL.Logic.TsoPinnedRead
