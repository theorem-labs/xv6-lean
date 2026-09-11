# Independent supplied-disk bootstrap review

Reviewed all eight frozen modules and the full FsBoot332–445 source contract.
The DiskClient carrier retains all fifteen source names. BioView retains its
names, device, coverage, content predicates and Timeless witnesses; no abstract
buffer invariant or driver allocation is assumed.

The pure coverage proof derives an exact signed-byte submap from the real
physical disk. Native carving splits the supplied image-byte resource at its
original name and returns both all covered full blocks and the exact difference
of unused bytes, preserving an arbitrary frame. The source affine carve is an
explicit corollary. Neither operation mints another physical authority.

The bootstrap proof invokes the checked native logged-byte mint and combines
its raw mclean resource with each physical pool block. It returns every source
column: cache and dirty authorities, fixed committed-byte invariant, full
unsealed exception handle, second dirty halves, committed home blocks and
parked raw cache halves outside home. Supplied link/top names are retained.
The physical and logged bytes use the existing Disk12 camera; no Initial
constructor or new registry slot is used.

A fresh independent audit checked 140 logical declarations in all eight
physical modules, private helpers, types, opaque bodies and constructors.
Only propext, Classical.choice and Quot.sound occur; zero exclusions and no
unsafe/partial or Initial allocation dependency. Evidence:
FsBootBytesPeerAudit.lean and fs-boot-bytes-peer-audit.log in
/tmp/xv6-lean-research.

PASS for supplied-byte carving and native byte bootstrap. Current-era recovery
installation and preservation of filesystem invariants remain later layers.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
