# Independent review: full initial durable snapshot

Verdict: PASS. Codex root read both SnapshotImage modules and the complete
FsDurImg.img_snap_ok source proof, along with the separately reviewed codec,
ownership, home-map and native link-family dependencies. All 21 Snapshot.Bytes
fields are discharged under exactly the existing fifteen BootImageWF premises.
Snapshot.OK adds the already proved full local-node predicate. The leaf applies
the generic proof to the actual checked disk, superblock, 13-block inode region
and initial coverage without fresh literal evaluation or extra hypotheses.

The bitmap equality retains all 1024 bytes and padding. Both inode domains
include the rounded free tail; records retain their exact signed offsets and
all address bytes. The data/indirect ties cover all held slots, including
allocations past EOF. W3/W4/W5 and bare free records pay ownership, metadata
exclusion and disjointness; no new coverage or ownership premise is introduced.
Link validity uses the actual whole-family camera theorem with root slack,
not just its pointwise ElemOK clause. The home-map domain bound follows the
source coverage/disk-size premises. The pure contract still permits block zero
generically; the image's own bitmap marks it used.

Fresh leaf build: 484 jobs passed. Physical-origin audit: all 16 declarations in
the two modules and all type/body dependencies pass with only propext,
Classical.choice and Quot.sound; no unsafe/partial dependencies, zero exclusions.
Records: /tmp/xv6-lean-research/SnapshotImageRootAudit.lean,
snapshot-image-root-build.log and snapshot-image-root-audit.log. The byte and
ownership dependencies independently passed 32- and 22-declaration audits.

This closes the full pure initial snap_ok theorem, including its concrete
inhabitant. It does not allocate P_dur, preserve it through commits or recovery,
verify kernel initialization, or close a whole-system theorem. Local elaboration
hints change no definition or premise.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
