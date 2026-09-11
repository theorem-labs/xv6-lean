# Filesystem boot-image contract review

Codex coordinator review: PASS. Reviewed all three BootImage modules against the
complete fifteen-conjunct definition in pinned `FsCfgBoot.v:584–652` and the
coverage predicate in `FsBoot.v:86`. Every conjunct remains present and ordered,
including parsed-superblock equality, the tighter ushort bound, exact file-link
counts, bare free records and the separate root-self-name exclusion.

The coverage predicate retains signed block arithmetic, excludes block zero and
requires the entire last byte of each covered block to lie inside the disk mint.
Generic proofs derive exact positive coverage from both coverage directions and
the disk bound. The concrete theorem instantiates the actual checked disk, all
thirteen rounded inode blocks, and exactly blocks 1 through 1999. It reuses
existing complete reader/checker certificates; no host computation is trusted.

The target build passed 278 jobs with the embedded 760-theorem dependency audit.
Rejection lemmas cover block zero and a disk one byte short. Global integration
also audits physical module origins and implementation/statement dependencies.
This is an initial-image premise only. Later reboot needs the durable snapshot
contract and its byte, ownership and native link-family validity obligations;
this result neither assumes a fresh disk on reboot nor allocates FS resources.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
