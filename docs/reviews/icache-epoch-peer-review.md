# Independent inode epoch-receipt review

Status: independent review PASS for all four frozen modules and STATUS.
The sail-audit agent owns only this report and changed no implementation.

Read all four `IcacheEpoch{Defs,Spec,Proofs,Link}` modules and the complete
pinned `InodeRegion.v:1582–1711` definitions and proofs. The native receipts
retain the source per-inode observation counter, log-epoch lower bound and
conditional zero-link receipt. `Names` makes the observation-name function,
log epoch and logged-event names and signed inode-start address explicit.
The source `γ = icfg_log` side condition is specialized by using the same
fixed names in the inputs and output, not discarded between unrelated logs.
The source unsigned nlink equality to zero is equivalent to the Lean
`BitVec.toNat = 0`; no signed reinterpretation is introduced.

`izrcpt` retains the ordinary BI implication and exact disjunction: a zero
link count permits either observation value zero or a real logged-event
fragment at an epoch at least that value. `ireg_ep` owns full native
mono-nat authority at the observation name. `nlz_obs` is the actual
persistent mono-nat lower bound at that same per-inode name. No fresh-name
injectivity is assumed by these generic predicates; boot allocation must
supply usable resources at the selected names.

Initialization consumes the supplied zero observation authority and obtains
the native log lower bound zero. It preserves the source zero-observation
branch, including free records that have no logged event. Stability requires
exactly that a new zero link count implies an old zero count. Mint updates
the observation authority to max(old, observed epoch), combines the two
existing log lower bounds and discharges the receipt only because the
record's link count is nonzero. It returns the same inode receipt and the
observer's actual lower-bound fragment.

Use retains both explicit premises: zero links and a positive observed
epoch. Native authority/fragment validity proves observed epoch ≤ current
counter; the receipt gives counter ≤ logged epoch. This is the necessary
comparison through authority, not an invalid comparison between two lower
bounds. Positivity excludes the zero boot branch. The proof returns the
same native inode receipt and the same logged-event fragment. The deposit
accessor preserves authority in its continuation and requires the caller's
replacement receipt at the exact chosen value. It does not mint a replacement
receipt from an arbitrary pure record property.

The final `iblkOf_inum` bridge is kernel reflexivity against the actual
`Xv6.Fs.inodeBlock` definition on unsigned 32-bit inode inputs. General
signed keys retain Euclidean division by 16, without a new nonnegative
precondition.

The Link uses the existing LogEpoch capacity, with mono-nat slot 3 and logged
set slot 34. There is no new slot, complete region/log invariant, op-epoch
stability theorem, instruction execution, fresh observation allocation, or
initial-snapshot dependency in this layer. The stronger function-level
log-group theorem remains a separate source obligation.

The owner's complete build passes 476 jobs. A fresh independent run of
`/tmp/xv6-lean-research/IcacheEpochPeerAudit.lean` checks all 49 logical
declarations from the four physical module origins, including private helpers,
opaque theorem bodies, types and datatype constructor dependencies. All pass
with only `propext`, `Classical.choice`, and `Quot.sound`; zero roots are
excluded and no unsafe/partial or initial-snapshot dependency occurs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
