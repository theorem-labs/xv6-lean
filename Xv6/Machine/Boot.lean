import MachCSL.Machine.Power
import MachCSL.Machine.ColdBootFacts
import Xv6.Elf.ImageFacts
import Xv6.Elf.ParserRepresentation
import Xv6.Image.Coverage

/-! Specialization of the shared machine to the actual paper kernel ELF.
RAM contains the parsed loadable bytes, with zero at every missing address,
including BSS and free RAM. The source's filtered dumped text/data maps still
require their separate cross-representation correspondence; this file proves
facts about the actual packed ELF and the actual generated boot execution.
No kernel safety or filesystem correctness theorem is asserted here. -/
namespace Xv6.Machine
open MachCSL

private theorem header_present : (Elf.parseHeader Images.kernel).isSome = true := by
  rw [Elf.Kernel.header]
  rfl

/-- Extract the header whose successful parsing is kernel checked. -/
def kernelHeader : Elf.Header := (Elf.parseHeader Images.kernel).get header_present

theorem kernelHeader_eq : kernelHeader =
    ⟨0x80000000, 64, 56, 3, 284216, 64, 21, 20⟩ := by
  simp only [kernelHeader, Elf.Kernel.header, Option.get_some]

def byteOfUInt8 (b : UInt8) : Memory.Byte := BitVec.ofNat 8 b.toNat

theorem byteOfUInt8_value (b : UInt8) : (byteOfUInt8 b).toNat = b.toNat := by
  apply Nat.mod_eq_of_lt b.toNat_lt_size

/-- Zero-defaulting covers both the ELF's zero tail and free physical RAM. -/
def bootByte (address : Int) : Memory.Byte :=
  byteOfUInt8 ((Elf.loadedImage Images.kernel address).getD 0)

def bootImage : MachCSL.Machine.BootImage :=
  ⟨BitVec.ofInt 64 kernelHeader.entry, bootByte⟩

theorem bootImage_entry : bootImage.vector = 0x80000000#64 := by
  simp only [bootImage, kernelHeader_eq]
  rfl

theorem bootImage_parsed_entry :
    (Elf.parseHeader Images.kernel).map (fun h => BitVec.ofInt 64 h.entry) =
      some bootImage.vector := by
  rw [Elf.Kernel.header, bootImage_entry]
  rfl

/-- The machine byte map also equals the proved contiguous-list ELF parser/image. -/
theorem bootByte_list (address : Int) : bootByte address =
    byteOfUInt8 ((Elf.loadedImageList Images.kernel.toBytes
      (Elf.loadsList Images.kernel.toBytes) address).getD 0) := by
  unfold bootByte
  rw [Elf.loadedImage_eq_parsed_list Images.kernel Image.Coverage.kernel]

theorem bootByte_present (address : Int) (b : UInt8)
    (h : Elf.loadedImage Images.kernel address = some b) : bootByte address = byteOfUInt8 b := by
  simp only [bootByte, h, Option.getD_some]

theorem bootByte_missing (address : Int)
    (h : Elf.loadedImage Images.kernel address = none) : bootByte address = 0 := by
  simp only [bootByte, h, Option.getD_none]
  rfl

/-- The actual file-backed interval maps to the actual ELF bytes after its 4096-byte prefix. -/
theorem loaded_file (address : Int)
    (h : 0x80000000 ≤ address ∧ address < 0x80000000 + 41632) :
    Elf.loadedImage Images.kernel address =
      Images.kernel.getByte? (4096 + (address - 0x80000000).toNat) := by
  simp only [Elf.loadedImage, Elf.Kernel.load_segments, Elf.segmentsUnion,
    List.foldr_cons, List.foldr_nil, Elf.union, Elf.segment]
  have hf : Elf.fileWindowLength Images.kernel
      ⟨1, 7, 4096, 0x80000000, 0x80000000, 41632, 144840, 4096⟩ = 41632 := by decide
  simp [Elf.segmentFile, hf, Elf.segmentZero, h.1,
    show address - 0x80000000 < (41632 : Int) by omega,
    show ¬ (2147525280 : Int) ≤ address by omega]

theorem bootByte_file (address : Int)
    (h : 0x80000000 ≤ address ∧ address < 0x80000000 + 41632) :
    bootByte address =
      byteOfUInt8 ((Images.kernel.getByte? (4096 + (address - 0x80000000).toNat)).getD 0) := by
  rw [bootByte, loaded_file address h]

theorem bootByte_bss (address : Int)
    (h : 0x80000000 + 41632 ≤ address ∧ address < 0x80000000 + 144840) :
    bootByte address = 0 := by
  rw [bootByte, Elf.Kernel.bss h]
  rfl

/-- ELF absence outside its one segment makes all remaining RAM zero. -/
theorem loaded_outside (address : Int)
    (h : address < 0x80000000 ∨ 0x80000000 + 144840 ≤ address) :
    Elf.loadedImage Images.kernel address = none := by
  simp only [Elf.loadedImage, Elf.Kernel.load_segments, Elf.segmentsUnion,
    List.foldr_cons, List.foldr_nil, Elf.union, Elf.segment]
  have hf : Elf.fileWindowLength Images.kernel
      ⟨1, 7, 4096, 0x80000000, 0x80000000, 41632, 144840, 4096⟩ = 41632 := by decide
  simp [Elf.segmentFile, hf, Elf.segmentZero]
  constructor
  · intro low high
    omega
  · omega

theorem bootByte_outside (address : Int)
    (h : address < 0x80000000 ∨ 0x80000000 + 144840 ≤ address) : bootByte address = 0 :=
  bootByte_missing address (loaded_outside address h)

/-- All RAM above the file-backed image is zero, including BSS and free pages. -/
theorem bootByte_after_file (address : Int) (h : 0x80000000 + 41632 ≤ address) :
    bootByte address = 0 := by
  by_cases hm : address < 0x80000000 + 144840
  · exact bootByte_bss address ⟨h, hm⟩
  · exact bootByte_outside address (Or.inr (by omega))

/-- Coverage proves that no file-backed byte is synthesized by the zero default. -/
theorem bootByte_file_present (address : Int)
    (h : 0x80000000 ≤ address ∧ address < 0x80000000 + 41632) :
    bootByte address = byteOfUInt8
      (Images.kernel.pageByte (4096 + (address - 0x80000000).toNat)) := by
  rw [bootByte_file address h,
    Images.kernel.getByte?_eq_some_pageByte Image.Coverage.kernel]
  · rfl
  · change 4096 + (address - 0x80000000).toNat < 285560
    omega

/-- Explicit specialization; reboot retains the incoming durable image. -/
def boot (before : MachCSL.Machine.State) : MachCSL.Machine.State :=
  MachCSL.Machine.bootState bootImage before

theorem boot_facts (before : MachCSL.Machine.State) :
    MachCSL.Machine.BootFacts bootImage (boot before) :=
  MachCSL.Machine.boot_facts bootImage before

theorem boot_shape (before : MachCSL.Machine.State) :
    MachCSL.Machine.BootShape bootImage before (boot before) :=
  MachCSL.Machine.boot_shape bootImage before

theorem boot_memory (before : MachCSL.Machine.State) :
    (boot before).memory = MachCSL.Machine.loadedRam bootImage := rfl

theorem boot_ram (before : MachCSL.Machine.State) :
    MachCSL.Machine.RamShape bootImage (boot before).memory :=
  MachCSL.Machine.loadedRam_shape bootImage

theorem boot_ram_byte (before : MachCSL.Machine.State) (address : Int)
    (low : (MachCSL.Machine.ramLow : Int) ≤ address)
    (high : address < (MachCSL.Machine.ramHigh : Int)) :
    (boot before).memory (BitVec.ofInt 64 address) = some (bootByte address) :=
  (boot_ram before).2 address low high

theorem boot_ram_zero (before : MachCSL.Machine.State) (address : Int)
    (low : 0x80000000 + 41632 ≤ address)
    (high : address < (MachCSL.Machine.ramHigh : Int)) :
    (boot before).memory (BitVec.ofInt 64 address) = some 0 := by
  rw [boot_ram_byte before address (by unfold MachCSL.Machine.ramLow; omega) high,
    bootByte_after_file address low]

theorem boot_ram_only (before : MachCSL.Machine.State) (address : Memory.PhysicalAddress)
    (h : ¬ (MachCSL.Machine.ramLow ≤ address.toNat ∧
      address.toNat < MachCSL.Machine.ramHigh)) : (boot before).memory address = none := by
  change MachCSL.Machine.loadedRam bootImage address = none
  exact if_neg h

theorem boot_memory_ok (before : MachCSL.Machine.State) :
    MachCSL.Machine.MemoryOK (boot before) :=
  MachCSL.Machine.boot_memory_ok bootImage _ (boot_facts before)

theorem boot_reservations_ok (before : MachCSL.Machine.State) :
    MachCSL.Machine.ReservationsOK (boot before) :=
  MachCSL.Machine.boot_reservations_ok bootImage _ (boot_facts before)

theorem boot_disk (before : MachCSL.Machine.State) :
    (boot before).devices.virtio.v_disk = before.devices.virtio.v_disk := rfl

theorem boot_virtio_reset (before : MachCSL.Machine.State) :
    (boot before).devices.virtio = Devices.Virtio.virtio_reset before.devices.virtio := rfl

theorem boot_real_run (before : MachCSL.Machine.State) (cpu : MachCSL.Machine.CPU) :
    MachCSL.Machine.Run Devices.bus
      (MachCSL.Machine.bootProgram bootImage.vector (BitVec.ofNat 64 cpu.val)
        MachCSL.Machine.pmaBoot)
      ⟨MachCSL.Machine.zeroRegisters, Memory.empty, Devices.initial⟩ ()
      ⟨(boot before).registers cpu, Memory.empty, Devices.initial⟩ :=
  MachCSL.Machine.boot_run Devices.bus _ _ Memory.empty Devices.initial

theorem boot_pc (before : MachCSL.Machine.State) (cpu : MachCSL.Machine.CPU) :
    (boot before).registers cpu .PC = 0x80000000#64 ∧
      (boot before).registers cpu .nextPC = 0x80000000#64 := by
  have h := MachCSL.Machine.bootRegisters_pc bootImage.vector (BitVec.ofNat 64 cpu.val)
  rw [bootImage_entry] at h
  change MachCSL.Machine.bootRegisters bootImage.vector _ .PC = _ ∧
    MachCSL.Machine.bootRegisters bootImage.vector _ .nextPC = _
  rw [bootImage_entry]
  exact h

theorem boot_misa (before : MachCSL.Machine.State) (cpu : MachCSL.Machine.CPU) :
    (boot before).registers cpu .misa = 0x800000000014112d#64 :=
  MachCSL.Machine.bootRegisters_misa _ _

/-- Every off state admits an actual on transition for the pinned ELF. -/
theorem powerOn (before : MachCSL.Machine.State) (off : before.power = false) :
    MachCSL.Machine.PowerStep bootImage before [.powerOn] (boot before)
      (MachCSL.Machine.powerFork before.generation) :=
  .on off (boot before) (boot_shape before)

theorem boot_exists (before : MachCSL.Machine.State) :
    ∃ after, MachCSL.Machine.BootShape bootImage before after := ⟨boot before, boot_shape before⟩

/-- The literal initial mkfs disk, zero outside the file, is separate from reboot. -/
def imageDisk (address : Int) : Memory.Byte :=
  if 0 ≤ address then byteOfUInt8 ((Images.disk.getByte? address.toNat).getD 0) else 0

theorem imageDisk_negative (address : Int) (h : address < 0) : imageDisk address = 0 := by
  simp [imageDisk, show ¬ 0 ≤ address by omega]

theorem imageDisk_after_end (address : Int) (h : (Images.disk.byteLength : Int) ≤ address) :
    imageDisk address = 0 := by
  have ha : 0 ≤ address := by omega
  have hn : Images.disk.byteLength ≤ address.toNat := by omega
  rw [imageDisk, if_pos ha, Images.disk.getByte?_out_of_bounds hn]
  rfl

theorem imageDisk_list (address : Int) (h : 0 ≤ address) :
    imageDisk address = byteOfUInt8 ((Images.disk.toBytes[address.toNat]?).getD 0) := by
  rw [imageDisk, if_pos h, Image.Coverage.disk_lookup]

theorem boot_imageDisk (before : MachCSL.Machine.State)
    (h : before.devices.virtio.v_disk = imageDisk) :
    (boot before).devices.virtio.v_disk = imageDisk := h

/-- A real boot state exists for every durable disk and advertised capacity.
This supplies a witness without asserting any filesystem or capacity contract. -/
theorem boot_disk_exists (disk : Devices.Virtio.Disk) (capacity : BitVec 64) :
    ∃ after : MachCSL.Machine.State,
      MachCSL.Machine.BootFacts bootImage after ∧
      after.devices.virtio.v_disk = disk ∧ after.devices.virtio.v_cap = capacity := by
  let before : MachCSL.Machine.State := {
    registers := fun _ => MachCSL.Machine.zeroRegisters
    memory := Memory.empty
    devices := { Devices.initial with virtio :=
      { Devices.Virtio.virtio0_state with v_disk := disk, v_cap := capacity } }
    generation := 0
    power := false
    reservations := fun _ => none
    image := Memory.empty
    log := []
    views := fun _ => 0 }
  exact ⟨boot before, boot_facts before, rfl, rfl⟩

theorem boot_initial_image_exists (capacity : BitVec 64) :
    ∃ after : MachCSL.Machine.State,
      MachCSL.Machine.BootFacts bootImage after ∧
      after.devices.virtio.v_disk = imageDisk ∧ after.devices.virtio.v_cap = capacity :=
  boot_disk_exists imageDisk capacity

end Xv6.Machine
