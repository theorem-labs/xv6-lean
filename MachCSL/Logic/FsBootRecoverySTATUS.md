# Actual era disk replay to native filesystem bootstrap

Stage 3 is frozen in FsBootRecoveryDefs/Spec/Proofs/Link plus the separate
literal Xv6/Fs/FsBootImage leaf. All five public pure/client/native contracts
are implemented; 20 named theorems include the seven image facts and
existing-registry links. The exact Defs/Spec received coordinator source
review before native proofs.

The canonical map comes from replaying the actual disk header. Facts
contains full recovered blocks and view, exact home domain, restriction
identity, raw agreement off the complete header write set, and log-slot
ties. The recovered_boot_ghosts rule requires only source CovIn and
HeaderWF. Every other native mint premise is proved from recovery, including
fullness and exception containment. No independent committed map,
Snapshot.OK, or success oracle appears as an extra premise.

The capacity structurally shares Era.disk with all physical/logged byte
rules. forEra changes only img and retains the other fourteen protocol
names. separate_clients is a checked separating equivalence with the exact
five non-disk Era.bootClients legs. era_boot_ghosts returns the SAME complete
Era.interp, including its physical disk authority, those five client legs,
the complete filesystem mint output, exact unused physical byte remainder
and arbitrary frame. Its disk is state.devices.virtio.v_disk at every point;
neither the state nor authority is replaced during allocation.

The literal leaf derives HeaderWF from Image.log_clean and CovIn from the
independently checked fifteen-premise Image.boot_image_wf. Replay equals
the actual initial home map, exceptions are empty, and the committed view
equals raw blocks at every signed address. boot_era_filesystem requires
explicit state.devices.virtio.v_disk = Image.disk before specializing the
native rule. Merely framing physical authority is not treated as this disk
identity. The result still uses the original era name and retains the full
empty exception HANDLE; no seal or Bio invariant is silently added.

Validation: generic Link build passed **532 jobs**, and full literal build
passed **634 jobs**. New modules elaborate in about one second. A fresh
physical-origin audit checked **88 logical declarations in all five
modules**, including private/generated roots, complete opaque bodies,
types and datatype constructors. Standard three foundational axioms only,
zero excluded roots, no unsafe/partial or Initial allocation dependency.
Evidence: /tmp/xv6-lean-research/FsBootRecoveryOwnerAudit.lean,
fs-boot-recovery-owner-audit.log, fs-boot-recovery-build.log,
fs-boot-image-build.log. Capacity projection normalization was made explicit
for native proof-mode unification, and the literal leaf uses maxRecDepth
2048 for its existing finite-container aliases. No approved definitions
were changed to make the proofs hold.

Generic HeaderWF remains explicit until supplied by the future native P_fs
recovery interface. This closes the actual disk-to-fs_alloc bootstrap seam;
it does not claim the complete FsCrash history/permit/receipt state,
configuration initialization, LogRes state, or Bio invariant allocation.
No new camera, registry or initial snapshot mint is introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
