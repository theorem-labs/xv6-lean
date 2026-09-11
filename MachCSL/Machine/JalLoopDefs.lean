import MachCSL.Machine.FetchJal
import MachCSL.Machine.DeviceSteps

/-! Canonical register states for repeated execution of the fetched JAL x0,0.
Dynamic counters, timer threshold, pending bits and hardware pins are unrestricted. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions

structure Dynamic where
  retired : BitVec 64
  increment : Bool
  cycles : BitVec 64
  time : BitVec 64
  timecmp : BitVec 64
  pending : BitVec 64
  supervisor : BitVec 1
  machine : BitVec 1

/-- Every static register is exactly the actual generated boot result for this hart. -/
def override (base : RegisterFile) (d : Dynamic) (r : Register) : RegisterType r :=
  match r with
  | .minstret => d.retired
  | .minstret_increment => d.increment
  | .mcycle => d.cycles
  | .mtime => d.time
  | .mtimecmp => d.timecmp
  | .mip => d.pending
  | .sig_seip => d.supervisor
  | .sig_meip => d.machine
  | other => base other

def registers (cpu : CPU) (d : Dynamic) : RegisterFile :=
  override (bootRegisters jalImage.vector (BitVec.ofNat 64 cpu.val)) d

def Canonical (cpu : CPU) (rs : RegisterFile) : Prop := ∃ d, rs = registers cpu d

def AllCanonical (rs : CPU → RegisterFile) : Prop := ∀ cpu, Canonical cpu (rs cpu)

def dynamic (rs : RegisterFile) : Dynamic :=
  ⟨rs .minstret, rs .minstret_increment, rs .mcycle, rs .mtime,
    rs .mtimecmp, rs .mip, rs .sig_seip, rs .sig_meip⟩

/-- Retirement uses the model's modular addition, with no nonoverflow premise. -/
def retire (d : Dynamic) : Dynamic :=
  { d with retired := _root_.Sail.BitVec.addInt d.retired 1, increment := true }

/-- Exact clock effects for the boot configuration: cycle/time increments and
MTI recomputation. The disabled supervisor timer does not change mip.STI. -/
def clock (d : Dynamic) : Dynamic :=
  { d with
    cycles := _root_.Sail.BitVec.addInt d.cycles 1
    time := _root_.Sail.BitVec.addInt d.time 1
    pending := _root_.Sail.BitVec.updateSubrange d.pending 7 7
      (bool_to_bit (zopz0zIzJ_u d.timecmp (_root_.Sail.BitVec.addInt d.time 1))) }

def afterCycle (tick : Bool) (d : Dynamic) : Dynamic :=
  if tick then clock (retire d) else retire d

end MachCSL.Machine.JalLoop
