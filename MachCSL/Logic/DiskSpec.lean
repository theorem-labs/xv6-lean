import MachCSL.Logic.DiskDefs

/-! Independently importable contract for the pinned `DiskImg.v` resource layer. -/
namespace MachCSL.Logic.Disk
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Devices.Virtio

structure DiskSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  readCons : ∀ disk offset n,
    disk_read disk offset (n + 1) = disk offset :: disk_read disk (offset + 1) n
  readLength : ∀ disk offset n, (disk_read disk offset n).length = n
  readLookup : ∀ disk offset n j, j < n →
    (disk_read disk offset n)[j]? = some (disk (offset + (j : Int)))
  readAgree : ∀ disk disk' n, disk_read disk 0 n = disk_read disk' 0 n →
    ∀ x : Int, 0 ≤ x ∧ x < (n : Int) → disk x = disk' x
  bytesCons : ∀ γ offset byte bytes,
    imageBytes capacity γ offset (byte :: bytes) ⊣⊢
      imageByte capacity γ offset byte ∗ imageBytes capacity γ (offset + 1) bytes
  bytesRead : ∀ γ map disk offset bytes, disk_view map disk →
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes -∗
      ⌜disk_read disk offset bytes.length = bytes⌝)
  bytesUpdateGen : ∀ γ map offset bytes bytes', bytes'.length = bytes.length →
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗ imageBytes capacity γ offset bytes' ∗
      ⌜∀ (j : Nat) byte, bytes'[j]? = some byte → map'[offset + (j : Int)]? = some byte⌝ ∗
      ⌜∀ x : Int, (∀ j : Nat, j < bytes'.length → x ≠ offset + (j : Int)) →
        map'[x]? = map[x]?⌝)
  bytesUpdate : ∀ γ map offset bytes bytes', bytes'.length = bytes.length →
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗ imageBytes capacity γ offset bytes' ∗
      ⌜∀ disk : Devices.Virtio.Disk, disk_view map disk →
        disk_view map' (disk_write disk offset bytes')⌝)
  bytesMint : ∀ γ map disk offset n, disk_view map disk →
    (∀ j : Nat, j < n → map[offset + (j : Int)]? = none) →
    iprop(⊢ mapAuth capacity γ map ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗
      imageBytes capacity γ offset (disk_read disk offset n) ∗ ⌜disk_view map' disk⌝)
  bytesMintDom : ∀ γ map disk offset n, disk_view map disk →
    (∀ j : Nat, j < n → map[offset + (j : Int)]? = none) →
    (∀ (x : Int) (byte : Byte), map[x]? = some byte → True) →
    iprop(⊢ mapAuth capacity γ map ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗
      imageBytes capacity γ offset (disk_read disk offset n) ∗ ⌜disk_view map' disk⌝ ∗
      ⌜∀ (x : Int) (byte : Byte), map'[x]? = some byte →
        map[x]? = some byte ∨ (offset ≤ x ∧ x < offset + (n : Int))⌝)
  alloc : ∀ disk n, iprop(⊢ |==> ∃ γ, imageAuth capacity γ disk ∗
    imageBytes capacity γ 0 (disk_read disk 0 n))
  sizedAlloc : ∀ disk n, iprop(⊢ |==> ∃ γ, imageAuthSized capacity γ n disk ∗
    imageBytes capacity γ 0 (disk_read disk 0 n))
  sizedRead : ∀ γ n disk offset bytes,
    iprop(⊢ imageAuthSized capacity γ n disk -∗ imageBytes capacity γ offset bytes -∗
      ⌜disk_read disk offset bytes.length = bytes⌝)
  sizedWrite : ∀ γ n disk disk',
    iprop(⊢ imageAuthSized capacity γ n disk -∗
      imageBytes capacity γ 0 (disk_read disk 0 n) ==∗
      imageAuthSized capacity γ n disk' ∗ imageBytes capacity γ 0 (disk_read disk' 0 n))

end MachCSL.Logic.Disk
