import Xv6.Kernel.CalleeSavedDefs
import Xv6.Kernel.MycpuScalarDefs
import Xv6.Kernel.MycpuMemoryDefs
import Xv6.Kernel.MycpuReturnDefs

/-! Pure register bookkeeping of `ProofMycpu.v:73–95,250–318`.
These are the post-state expressions used to compose the actual instruction
rules. They do not define a machine execution or assert that loads read saved
values: the native stack ownership must separately establish that premise. -/
namespace Xv6.Kernel.MycpuRegisterSequence
open MachCSL.Machine

def pushed (entry : RegisterFile) : RegisterFile := MycpuScalar.after ⟨0, by decide⟩ entry
def framed (entry : RegisterFile) : RegisterFile := MycpuScalar.after ⟨1, by decide⟩ (pushed entry)

/-- The address calculation explicitly receives the AUIPC instruction's PC.
Fetching/retirement must establish that PC in the enclosing function proof. -/
def computed (entry : RegisterFile) : RegisterFile :=
  MycpuScalar.addressCalc (MycpuScalar.offsetCalc
    (MachCSL.Sail.Registers.write (framed entry) .PC (MycpuDecode.address ⟨7, by decide⟩)))

/-- These are precisely the load-rule post-states when the two saved words
have been obtained from native stack ownership. -/
def restored (entry : RegisterFile) : RegisterFile :=
  MycpuMemory.after .s0 (MycpuMemory.after .ra (computed entry) (entry .x1)) (entry .x8)

def popped (entry : RegisterFile) : RegisterFile := MycpuScalar.after ⟨8, by decide⟩ (restored entry)
def returned (entry : RegisterFile) : RegisterFile := MycpuReturn.after (popped entry)

end Xv6.Kernel.MycpuRegisterSequence
