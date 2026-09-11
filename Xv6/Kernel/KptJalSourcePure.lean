import Xv6.Kernel.KptJalSourceSpec
import Xv6.Kernel.KptJalSconfPure

namespace Xv6.Kernel.KptJalSource
open MachCSL.Machine MachCSL.Logic

theorem stack pc file : SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file :=
  KptJalSconf.stack pc file

theorem saved pc file : MycpuOff.Saved file (afterFile pc file) := KptJalSconf.saved pc file

theorem boundary pc imm initial after (before : SieOffPacket.Boundary pc initial)
    (done : MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started initial)) after) :
    SieOffPacket.Boundary (KptJal.target pc imm) after := KptJalSconf.boundary pc imm initial after before done

theorem pureSpec : PureSpec := ⟨stack,saved,boundary⟩

end Xv6.Kernel.KptJalSource
