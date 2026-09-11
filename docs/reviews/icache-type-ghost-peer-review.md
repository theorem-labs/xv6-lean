# Native inode type one-shot review

Coordinator review: pass for all four IcacheTypeGhost modules, read against
Xv6Cameras.v:607–613, IcacheRef.v:1192–1298 and FsReady.v:385–391 at the pinned
paper source. The raw non-unital Csum/Excl camera, invalid branches and actual
ownership are preserved. Pending is exclusive, shot is persistent, and its
BitVec 16 value is unrestricted, including the source's exact zero sealing
witness. Native validity proves agreement and pending/shot exclusion.

The false boot regime remains exclusive; true runtime regime owns an
existential shot. The claim guard consumes an already extracted pure slot
disjunction and returns boot ownership. It does not supply the missing inode
invariant accessor. Same-name firing and fresh-name allocation retain arbitrary
frames in the existing world. Allocation has no boot/liveness caller in this
prefix; actual only packages the native specification. All prior registry
slots remain unchanged and only assigned slot 32 is extended.

The independent fresh full-origin audit checked 163 logical declarations,
including opaque bodies, types and constructors, with only the standard three
axioms and no exclusions, unsafe/partial dependency or Initial allocation call.
Evidence: /tmp/xv6-lean-research/icache-type-peer-audit.log. Full transaction
shelter, payload/liveness and filesystem-ready assembly remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
