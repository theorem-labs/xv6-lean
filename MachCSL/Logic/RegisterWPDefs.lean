import MachCSL.Logic.DeadThreadDefs
import MachCSL.Logic.EraStateDefs

/-! Ownership specializations of the direct register nodes in `HartRegNode.v`.
These predicates use the actual generated dependent register types and machine WP. -/
namespace MachCSL.Logic.RegisterWP
open Iris Iris.BI MachCSL.Machine
abbrev threadWP := @DeadThread.threadWP
end MachCSL.Logic.RegisterWP
