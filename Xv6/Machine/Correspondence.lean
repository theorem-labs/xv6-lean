import Xv6.Machine.Boot
import Xv6.Kernel.Correspondence

/-! The boot byte function agrees with the source language's filtered dumped
code/data map, defaulted to zero. The input-map importer remains untrusted;
the exact imported maps are independently tied to the actual parsed ELF. -/
namespace Xv6.Machine

def dumpedBootByte (address : Int) : MachCSL.Memory.Byte :=
  byteOfUInt8 ((if address < 0x8000a2a0 then Kernel.fileBytes address else none).getD 0)

private theorem zeroImage_default (address : Int) :
    (Elf.zeroImage Images.kernel address).getD 0 = 0 := by
  simp only [Elf.zeroImage, Elf.Kernel.load_segments, Elf.segmentsUnion,
    List.foldr_cons, List.foldr_nil, Elf.union, Elf.segmentZero]
  split <;> rfl

theorem bootByte_file_default (address : Int) :
    bootByte address = byteOfUInt8 ((Kernel.fileBytes address).getD 0) := by
  unfold bootByte
  rw [← Kernel.fileBytes_union_bss]
  cases h : Kernel.fileBytes address with
  | none => simp only [Elf.union, h, Option.orElse_none, zeroImage_default]; rfl
  | some byte => simp [Elf.union, h]

/-- All integer addresses, including BSS, free RAM and addresses outside the image. -/
theorem bootByte_eq_dumped (address : Int) : bootByte address = dumpedBootByte address := by
  rw [bootByte_file_default]
  unfold dumpedBootByte
  split
  · rfl
  · rename_i outside
    rw [Kernel.fileBytes_outside address (Or.inr (by omega))]

theorem bootImage_eq_dumped : bootImage =
    (⟨0x80000000, dumpedBootByte⟩ : MachCSL.Machine.BootImage) := by
  have vector := bootImage_entry
  have bytes : bootByte = dumpedBootByte := funext bootByte_eq_dumped
  unfold bootImage
  change BitVec.ofInt 64 kernelHeader.entry = 0x80000000#64 at vector
  rw [vector, bytes]
  rfl

end Xv6.Machine
