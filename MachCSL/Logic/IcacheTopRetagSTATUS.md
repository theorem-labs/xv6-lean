# Native top-map retagging

`IcacheTopRetagSpec.lean` and `IcacheTopRetagProofs.lean` are frozen after
owner validation. They port exactly `InodeRegion.v:3294–3340` using the
existing complete `IcacheTopRegistry` body and native invariant.

`retag` requires the exact durable local predicate at the new inode value.
It opens the invariant, updates the supplied top fragment with the actual
authority, proves clean preservation for the new map, closes the invariant
and returns the new full fragment. The arm map and all parked transaction
shares remain unchanged.

`retag_armed` instead requires the actual full receipt and membership of
the inode in its recorded set. Native authoritative lookup first establishes
the receipt's full transaction/share/set entry. That entry contradicts the
clean predicate's unarmed premise at the modified inode, so the new node is
arbitrary; no local-node condition or narrowed carrier is added. The full
original receipt and updated top fragment are returned. Every other inode's
clean condition is preserved. Both rules retain the source namespace
inclusion and restore the original mask.

The two pure preservation theorems are `clean_retag` and
`clean_retag_armed`. The public two-field Spec, generic `actual` and concrete
`nativeSpec` use the existing slot-38 registry and same-world InvGS. No
registry, resource definition, ghost name or camera is changed or allocated.
The frozen TopRegistry and all repository umbrella files remain untouched.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheTopRetagProofs`
passes all 484 jobs. Six named theorems are checked. Fresh
`/tmp/xv6-lean-research/IcacheTopRetagOwnerAudit.lean` covers all 14 physical
module declarations, private/generated helpers, opaque bodies, types and
datatype constructor dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` occur; zero roots are excluded and no unsafe/partial or
`FsDurSnapshot.Initial` dependency occurs.

This closes the source's two top-retag operations. It supplies no byte
update, region-record update, transaction pin, byte invariant, recovery seal
or whole filesystem boot proof; those remain explicit caller resources or
subsequent source dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
