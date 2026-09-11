# Actual mycpu physical boot resources

Implemented and owner-frozen for independent review. Five modules:
`MycpuBootResources{Defs,Spec,Proofs,Sharing,Link}.lean`.
Source pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`extract_initial` consumes exactly one unique 34-byte physical span at
`0x800018ba` from the existing full byte and timestamp-zero client maps. The
actual byte values are proved from `MycpuFetchBytes` and the loaded pinned
kernel, through arbitrary actual xv6 `BootFacts` and a finite-map decode proof.
Both exact maps with those 34 keys deleted are returned; outside-key byte and
timestamp lookups are unchanged. No authority or fragment is reallocated.

`extract_clients` additionally preserves every other `Era.bootClients`
conjunct: all initial register cells, all heap metadata tokens (including the
34 selected addresses), device fragments, durable disk bytes, and reservation
fragments. The initial log-length receipt is returned separately.

`allocate_boot` calls the existing native era allocator and its proved
component implementations on `Xv6.Machine.boot before`, for arbitrary prior
state, template, and disk size. It returns the actual entire era interpretation,
the span, exact remainders, log receipt, and all other clients. The actual
`boot_facts` and `FiniteMap.decode_encodeAll` discharge the boot and representation
premises. `encodeAll` is only the existing logical finite-domain witness: its
64-bit enumeration is never evaluated. The extraction interface also supports
any practical finite map whose decode equality is proved.

Sharing has two explicit paths:

- `context_intro` retains full timestamp ownership; `context_split` splits byte
  and timestamp fractions together. `fetch_access` returns the selected actual
  two/four-byte window plus a linear wand restoring the entire span. Overlapping
  fractional windows therefore use reassembly or previously separated shares.
- `physical_intro` explicitly persists the existing timestamp-zero clients.
  `physical_split` splits byte fractions while sharing those persistent receipts.
  `physical_persist` consumes byte ownership to produce discarded ownership.
  `discarded_context` converts this only to a discarded context window;
  it does not upgrade discarded timestamps to a requested owned fraction.
  `discarded_windows` and `discarded_contexts` retain the physical span and
  legitimately supply all fourteen overlapping windows for arbitrary contexts.

`allocate_shared_boot` composes real allocation and persistence, retaining the
entire interpretation and client remainder while supplying all fourteen windows
for each context in any finite list. The separate `Spec` records the main
allocation, extraction, access, and sharing contracts; `nativeSpec` discharges
them without external resource callbacks or a new camera slot.

The 34-byte word is resource packaging, not a 34-byte machine read. Each actual
fetch remains two or four bytes, using `MycpuFetchBytes.width/word`. The pinned
`Ext_Ziccif` enabled proof justifies the aligned four-byte footprint. The final
fetch includes `01 11` after the 32-byte function body; the literal windows
are not falsely treated as disjoint.

Source mapping:

| Source | Implemented correspondence |
| --- | --- |
| `BootCarve.v:154–211,1220–1255` | Extract existing bytes and timestamp clients; explicit persistence with exact remainder |
| `KMap.v:217–238` | Only its physical byte/pristine ingredients; static mapping, canonical/tier claims remain separate |
| `KernelText.v:58–108` | Persistent hart-independent physical sharing and concrete overlapping windows |
| Actual `MycpuFetchBytes` image certificates | All 34 source bytes and fourteen exact subword byte equalities |

This is a physical boot-text resource slice. It does not yet implement the full
source `text_pointsto`, `kernel_text`, `instr_bytes`, KPT/tier resources, supervisor
translation, mycpu execution WP, or whole-kernel safety. The eleven kernel
auxiliary names remain exactly those of the supplied template, as the existing
era allocator specifies; their ownership is not invented.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuBootResourcesLink`
  passed 523 jobs. Proofs 1.4s, Sharing 1.1s, final Link 1.1s.
- Fresh independent-of-umbrella physical-origin audit of all **61 declarations**
  in all five modules passed. Full type/opaque-value/constructor dependency
  traversal, `collectAxioms` on every declaration, zero excluded roots, no
  unsafe/partial logical dependency, only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Audit driver `/tmp/xv6-lean-research/MycpuBootResourcesAudit.lean`; logs
  `/tmp/xv6-lean-research/mycpu-boot-resources-{build,audit}.log`.
- No `sorry`, custom axiom, native decision procedure, generated model edit,
  frozen dependency edit, or runtime evaluation of `encodeAll`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
