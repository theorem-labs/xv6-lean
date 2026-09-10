import Xv6

private def checkPacked (name : String) (packed : Xv6.Image.Packed)
    (raw : ByteArray) : IO Unit := do
  unless packed.byteLength == raw.size do
    throw (IO.userError s!"{name}: packed length mismatch")
  for page in List.range ((raw.size + 4095) / 4096) do
    for within in [0, 2048, 4095] do
      let offset := page * 4096 + within
      if offset < raw.size then
        unless packed.getByte? offset == some raw[offset]! do
          throw (IO.userError s!"{name}: packed byte mismatch at {offset}")
  unless packed.getByte? (raw.size - 1) == some raw[raw.size - 1]! do
    throw (IO.userError s!"{name}: final byte mismatch")
  unless packed.getByte? raw.size == none &&
      packed.readBytes? (raw.size - 1) 2 == none &&
      packed.readBytes? raw.size 0 == some ByteArray.empty do
    throw (IO.userError s!"{name}: packed read bounds regression")

-- Executable checks, not theorem evidence about ELF loading or filesystem validity.
#eval do
  unless Xv6.Image.decodeChunks ["00ff", "aB"] == some (ByteArray.mk #[0, 255, 171]) do
    throw (IO.userError "hex decoding/order regression")
  unless Xv6.Image.decodeChunks ["0", "0"] == none do
    throw (IO.userError "unaligned chunks must be rejected")
  unless Xv6.Image.decodeChunks ["zz"] == none do
    throw (IO.userError "malformed hex must be rejected")
  let some kernel := Xv6.Images.kernelElf | throw (IO.userError "kernel decode failed")
  unless kernel.size == 285560 do throw (IO.userError "kernel size mismatch")
  unless kernel.extract 0 4 == ByteArray.mk #[127, 69, 76, 70] do
    throw (IO.userError "kernel ELF magic mismatch")
  let some disk := Xv6.Images.initialDisk | throw (IO.userError "disk decode failed")
  unless disk.size == 2048000 do throw (IO.userError "disk size mismatch")
  checkPacked "kernel" Xv6.Images.kernel kernel
  checkPacked "disk" Xv6.Images.disk disk
  IO.println s!"Decoded exact image inputs: kernel={kernel.size}, disk={disk.size} bytes"
