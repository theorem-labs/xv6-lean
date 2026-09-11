import MachCSL.Logic.TsoContextBytesDefs
import MachCSL.Logic.TsoContextStoreDefs

namespace MachCSL.Logic.TsoContextBytesStore
open Iris MachCSL.Memory MachCSL.Machine
abbrev Capacity := TsoContext.Capacity
abbrev window := @TsoContextBytes.window
abbrev Readback := TsoContextBytes.Readback
end MachCSL.Logic.TsoContextBytesStore
