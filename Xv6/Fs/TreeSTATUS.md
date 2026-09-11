# Pure inode-keyed tree vocabulary

`TreeDefs`/`TreeSpec` follow FsTree.v128–162,605–847 exactly: a finite extensional
map from signed inode numbers to file bytes or directory maps, plus a root.
Missing nodes and hard links are representable; neither connectivity nor acyclicity
is built into the carrier. Names retain arbitrary byte lists and the existing
first-winner directory view. `nodeOf` reads every non-directory type's declared
file bytes, including malformed devices with nonzero size.

`NodeRep` carries allocation and the exact bytes/map equation; only its directory
arm requires name uniqueness. `TreeProofs` establishes determinacy, allocation,
entry bridges, fold-left path laws, the visited chain, and the source acyclicity
consequence. `InumsOK`, `RootDirectory`, `TreeWellFormed`, `ProperPath`, and
`DirectoriesAcyclic` remain distinct source propositions. Kernel checks cover
malformed device data and empty paths from absent nodes.

Directory byte updates/deletion and uniqueness maintenance later in FsTree.v
remain subsequent operational proof work; the core tree representation does not
pretend that first-winner maps are invertible.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
