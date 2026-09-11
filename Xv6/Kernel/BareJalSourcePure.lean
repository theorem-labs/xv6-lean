import Xv6.Kernel.BareJalSourceSpec
import Xv6.Kernel.KptJalSconfPure
import Xv6.Kernel.MycpuKptEntryPure
namespace Xv6.Kernel.BareJalSource
open MachCSL.Machine MachCSL.Logic

theorem config pc control (ambient : SieOffPacket.Ambient pc control) (pma : control .pma_regions = pmaBoot) :
    BareJal.Config control := MycpuKptEntry.config pc control ambient pma

theorem stack pc file : SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file := rfl

theorem saved pc file : MycpuOff.Saved file (afterFile pc file) := KptJalSconf.saved pc file

theorem boundary pc imm control after (before : SieOffPacket.Boundary pc control)
    (done : MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started control)) after) :
    SieOffPacket.Boundary (KptJal.target pc imm) after := KptJalSconf.boundary pc imm control after before done

theorem nativePureSpec : PureSpec := ⟨config,stack,saved,boundary⟩
end Xv6.Kernel.BareJalSource
