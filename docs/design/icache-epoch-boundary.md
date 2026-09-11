# Inode observation epoch receipt boundary

The next root-owned prefix is IcacheEpoch{Defs,Spec,Proofs,Link}+STATUS,
implementing the complete receipt section InodeRegion.v:1582–1711 at the
pinned paper source. All definitions and six native source laws in that
section have been read. The actual LogEpoch camera layer now supplies the
previously missing epoch and logged-block receipts.

Use the existing LogEpoch.Capacity, including shared MonoNat slot 3 and
append-set slot 34, with explicit log-epoch name, append-registry name,
per-signed-inum observation names and inode-start block. No new slot or
allocation is needed. The observation counter is a separate named authority;
it is not equated with the log's epoch authority or an inode generation.

Define iblkOf z = z / 16 + inodeStart using signed Euclidean division.
Define izrcpt z d v as the source BI implication: if d.nlink.toNat = 0,
then v = 0 or there exists e with actual logged_at e (iblkOf z) and v ≤ e.
Define ireg_ep z d as existential v with full observation-counter authority,
actual log_epoch_lb v and that receipt. nlz_obs z e0 is the persistent lower
bound at the same observation name. Preserve the boot zero disjunction:
free initial records have no historical logged receipt.

Implement exact native intro from supplied observation authority at zero;
record transport when newly zero implies previously zero; mint under nonzero
nlink plus the actual operation's log-epoch lower bound, raising the observation
counter to max(v,e0); use under zero nlink and 1 ≤ e0, combining actual
observation authority and fragment to rule out the boot disjunction, returning
the same ireg_ep plus an indexed logged receipt at e ≥ e0; and the deposit
accessor returning the epoch bound and a linear closure accepting the new
record's genuine receipt. Every bound and update is from native MonoNat
ownership. No comparison of two unrelated lower bounds substitutes for the
observation authority.

The log names are fixed explicit parameters shared by each premise; this
encodes the source's gamma = icfg_log tie without allocating another log.
All unsigned record facts use the existing full Dinode type, and signed block
geometry agrees with the source IBLOCK definition. Timeless/persistent
instances follow actual camera resources; ireg_ep itself remains linear.
Generic proofs precede a concrete link through LogEpoch.registryCapacity.

This prefix opens no inode invariant, allocates no region or log, and proves
no physical write or current-header membership. The complete slot, operation
entry tie, log_use_group and machine-code iupdate/commit remain separate.
Validate all modules and audit every physical declaration plus type, opaque
body and constructor cone with standard three axioms and zero unsafe/partial
or Initial dependencies, then request independent source review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
