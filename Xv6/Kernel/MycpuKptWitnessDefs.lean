import Xv6.Kernel.MycpuBareWitnessDefs
import Xv6.Kernel.Sv39TlbDefs

/-! A configured operational Sv39 witness checkpoint. The actual table bytes
are part of both initial memory and its TSO image. No boot reachability or
native Iris resource inhabitation is asserted by these definitions. -/
namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

abbrev platform := MycpuBareWitness.platform
attribute [local instance] platform
abbrev cpu := MycpuBareWitness.cpu

def rootBase : Nat := 0x80050000
def middleBase : Nat := 0x80051000
def leafBase : Nat := 0x80052000

def rootPointer : BitVec 64 := (0x80051#64 <<< 10) ||| 1#64
def middlePointer : BitVec 64 := (0x80052#64 <<< 10) ||| 1#64
/-- V,R,X,A,D; no W,U,G,PBMT or reserved high bits. -/
def codePte : BitVec 64 := (0x80001#64 <<< 10) ||| 0xcb#64
/-- V,R,W,A,D; no X,U,G,PBMT or reserved high bits. -/
def stackPte : BitVec 64 := (0x8003f#64 <<< 10) ||| 0xc7#64

def tableWord (page slot : Nat) : BitVec 64 :=
  if page = 0 ∧ slot = 2 then rootPointer
  else if page = 1 ∧ slot = 0 then middlePointer
  else if page = 2 ∧ slot = 1 then codePte
  else if page = 2 ∧ slot = 63 then stackPte
  else 0

def tableRange (a : PhysicalAddress) : Prop :=
  rootBase ≤ a.toNat ∧ a.toNat < rootBase + 3 * 4096
instance (a : PhysicalAddress) : Decidable (tableRange a) := inferInstanceAs (Decidable (_ ∧ _))

def tableByte (offset : Nat) : Byte :=
  nthByte (tableWord (offset / 4096) ((offset % 4096) / 8)) (offset % 8)

/-- All bytes outside the three full table pages retain the actual loaded image. -/
def image : ByteMap 64 := fun a =>
  if tableRange a then some (tableByte (a.toNat - rootBase)) else MycpuBareWitness.image a

/-- The old checked image cache remains only an optimization of the fallback. -/
def cachedImage : ByteMap 64 := fun a =>
  if tableRange a then some (tableByte (a.toNat - rootBase)) else MycpuBareWitness.cachedImage a

def satpValue : BitVec 64 := 0x8000000000080050#64

def entry (r : Register) : RegisterType r :=
  match r with
  | .satp => satpValue
  | .tlb => Vector.replicate 64 none
  | r => MycpuBareWitness.entry r

def codeTlb : Sv39Tlb.Tlb := Sv39Tlb.filled (entry .tlb) 0#16 0x80001#27
  0x80001#44 codePte (.Physaddr 0x80052008#64) false

def bothTlb : Sv39Tlb.Tlb := Sv39Tlb.filled codeTlb 0#16 0x8003f#27
  0x8003f#44 stackPte (.Physaddr 0x800521f8#64) false

def tlbAt (k : Nat) : Sv39Tlb.Tlb :=
  if k = 0 then entry .tlb else if k = 1 then codeTlb else bothTlb

/-- A compact expected full file, not an alternate instruction evaluator. -/
def checkpoint (k : Nat) : RegisterFile :=
  Sail.Registers.write
    (Sail.Registers.write (MycpuBare.reference entry k) .minstret (BitVec.ofNat 64 k))
    .tlb (tlbAt k)

def initial : LocalState Devices.State := ⟨entry, image, Devices.initial, [], 0, none⟩

def storeState (writer : CPU) (s : LocalState Devices.State)
    (req : Logic.MemoryWriteWP.WriteRequest n) (word : BitVec (8*n)) : LocalState Devices.State :=
  { s with memory := writeBytes s.memory req.pa n word
           log := s.log ++ [⟨snapshot req.pa n word, hartAgent writer⟩]
           reservation := none }

/-- Generic image-parameterized version of the frozen write-pausing evaluator.
All actual reads use the supplied image and real common view/log; unsupported
write forms and other unsupported events fail. Its soundness must be proved
before any successful certificate is used as an operational witness. -/
noncomputable def run (cache : ByteMap 64) (writer : CPU) :
    Nat → SailM Unit → LocalState Devices.State → Option (LocalState Devices.State)
  | 0, _, _ => none
  | fuel + 1, program, s => do
    let (rest, regs) ← SpinlockWitness.pauseRun
      (Memory.read cache s.log (hartAgent writer) s.view) 2000 program s.registers
    let t := { s with registers := regs }
    match rest with
    | .pure _ => some t
    | .impure (.writeMem _ req) k =>
      if deviceAddress req.pa || accessExclusive req.access_kind then none else
      match req.value with
      | none => none
      | some word => run cache writer fuel (k (.Ok none)) (storeState writer t req word)
    | _ => none
termination_by structural fuel _ _ => fuel

inductive Cycles : Nat → LocalState Devices.State → LocalState Devices.State → Prop
  | nil (s) : Cycles 0 s s
  | cons {n s t u} :
      NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
        (cycle false) { s with reservation := none } (.pure ()) t →
      Cycles n t u → Cycles (n+1) s u

def logAt (k : Nat) : WriteLog 64 :=
  (if 1 < k then [⟨snapshot (MycpuBare.raSlot entry) 8 (entry .x1), hartAgent cpu⟩] else []) ++
  (if 2 < k then [⟨snapshot (MycpuBare.s0Slot entry) 8 (entry .x8), hartAgent cpu⟩] else [])

def memoryAt (k : Nat) : ByteMap 64 :=
  let first := if 1 < k then writeBytes image (MycpuBare.raSlot entry) 8 (entry .x1) else image
  if 2 < k then writeBytes first (MycpuBare.s0Slot entry) 8 (entry .x8) else first

def stateAt (k : Nat) : LocalState Devices.State :=
  ⟨checkpoint k, memoryAt k, Devices.initial, logAt k, 0, none⟩

def configured : State :=
  { MycpuBareWitness.configured with
    registers := updateHart (fun _ => zeroRegisters) cpu entry
    memory := image
    image := image }

def finalState : State := writeBack configured cpu (stateAt 14)

/-- The source function's register conclusions, with an explicit Sv39 endpoint.
The Bare.Result predicate is inapplicable because its config requires Bare. -/
structure Result (after : RegisterFile) : Prop where
  exact_file : after = checkpoint 14
  stable : MycpuBare.Stable entry after
  saved : CalleeSaved.Preserved entry after
  ra : after .x1 = entry .x1
  pc : after .PC = MycpuReturn.retPC (entry .x1)
  nextPC : after .nextPC = MycpuReturn.retPC (entry .x1)
  value : after .x10 = MycpuScalar.mycpuRet (entry .x4)
  cpuAddress : (after .x10).toNat = 0x800123e8 + 128 * cpu.val
  sv39 : after .satp = satpValue
  tlb : after .tlb = bothTlb

end Xv6.Kernel.MycpuKptWitness
