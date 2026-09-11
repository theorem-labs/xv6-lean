import Xv6.Fs.InodeRegionImageDefs

namespace MachCSL.Logic.FsInodeRegion
open Xv6.Fs MachCSL.Memory

/-- Consecutive source 64-byte records; malformed short inputs still decode
through the same total byte reader, while roundtrip requires exact length. -/
def decodeRecords : Nat → List Byte → List Dinode
  | 0, _ => []
  | n + 1, bytes => decodeDinode bytes :: decodeRecords n (bytes.drop 64)

def decodeImage (blocks : List (List Byte)) : List (List Dinode) := blocks.map (decodeRecords 16)

end MachCSL.Logic.FsInodeRegion
