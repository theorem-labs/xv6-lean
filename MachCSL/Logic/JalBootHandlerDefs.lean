import MachCSL.Logic.PowerWPDefs
import MachCSL.Logic.EventWPJalUniversalSpec
import MachCSL.Logic.UartWPSpec
import MachCSL.Logic.PlicWPSpec
import MachCSL.Logic.ResetDiskWPSpec
import MachCSL.Logic.JalBootResourcesDefs

namespace MachCSL.Logic.JalBootHandler
open Iris Iris.BI MachCSL.Machine

structure Namespaces where
  observations : Namespace
  uart : Namespace
  plic : Namespace
  wires : Namespace
  uart_observations : (↑observations : CoPset) ⊆ ⊤ \ ↑uart

end MachCSL.Logic.JalBootHandler
