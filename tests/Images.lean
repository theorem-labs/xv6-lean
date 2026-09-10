import Xv6

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
  IO.println s!"Decoded exact image inputs: kernel={kernel.size}, disk={disk.size} bytes"
