import Xv6.Fs.BitmapDefs
import Xv6.Fs.LinksDefs

namespace Xv6.Fs

/-- Exact initial-image fsimg_wf (FsImg.v3442–3453). Durable predicates are separate. -/
def fsimgValid (image : Blocks) (sb : Superblock) : Bool :=
  superblockValid sb && logClean image sb && inodesValid image sb &&
  blocksBitmapValid image sb && dirsValid image sb && rootValid image sb &&
  dotsAll image sb && linksValid image sb

end Xv6.Fs
