import Xv6.Fs.ValidityDefs

namespace Xv6.Fs

structure FsimgChecks (image : Blocks) (sb : Superblock) : Prop where
  superblock : superblockValid sb = true
  log : logClean image sb = true
  inodes : inodesValid image sb = true
  blocks : blocksBitmapValid image sb = true
  directories : dirsValid image sb = true
  root : rootValid image sb = true
  dots : dotsAll image sb = true
  links : linksValid image sb = true

end Xv6.Fs
