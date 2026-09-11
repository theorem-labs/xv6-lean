# Independent complete JAL boot-handler review

Result: **PASS.** Reviewed the frozen
`MachCSL/Logic/JalBootHandler{Defs,Proofs,Link}.lean` files, their actual resource
split helpers, and the previously reviewed hart/UART/PLIC/reset-disk WP contracts.
The reviewer (`artifact_audit`) did not implement these three assembly files.
A separate review by `lean_logic_audit`, who implemented the final safety linkage,
is preserved in `jal-boot-handler-peer-review.md`. No source correction or edit
was required by either review.

## Every boot and every worker

`boot_handler` constructs the persistent `PowerWP.bootHandler`, universally
quantified over the actual boot state, arbitrary freshly allocated complete era,
and finite memory map with its decoding equality. It uses `BootFacts jalImage`,
not the canonical `bootState` register witness. The per-hart family is derived
for every CPU, retaining arbitrary permitted preboot register values.

`cpu_to_list` uses the complete CPU set and duplicate-free `List.finRange 8`.
`harts_wp` supplies all eight actual `loop generation cpu` WPs. The final list
is exactly `powerFork generation`: eight harts followed by UART, disk, and PLIC.
All eleven forked workers are paid for at their actual generation.

This matches the machine-only all-worker obligation shape of pinned
`iris/RiscvAdequacy.v:1453–1488` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. It does not implement the source
filesystem crash, custody, or lending resources.

## Resource accounting

The handler consumes the actual `Era.bootClients` returned by allocation:

* Register ownership splits into 178 CPU-owned cells per hart and two full
  interrupt-pin cells per hart. The pin cells enter `wireInv`; the harts retain
  no duplicate ownership of them.
* `boot_code_lookup` derives all four instruction bytes from the actual memory
  decoding equation and boot RAM equality. The code timestamps become persistent
  pristine receipts. Three exact fractional halvings yield eight positive
  one-eighth byte shares, one per hart.
* The reservation map becomes a separating conjunction with one fragment per CPU.
  Each hart receives its own value wrapped in `resvAny`; actual restart clears it.
* The three device halves are separated once. UART ownership and freshly
  allocated UART ghosts enter `uartInv`. PLIC ownership enters `plicInv`, with
  its plan derived from the actual reset PLIC. The reset Virtio half goes to the
  reset-disk WP using the boot witness's existential previous device. No medium
  is replaced or assumed equal to a preferred initial image.

Only persistent assertions are duplicated: generation certificates, native
invariants, and pristine receipts. Register cells, byte fractions, reservations,
and device halves are partitioned by checked ownership laws.

The remaining byte/timestamp ownership, metadata tokens, log-length receipt,
era disk fragments, and UART initialization clients are discarded affinely.
None is assumed back by a continuation. The fixed durable authority remains in
state interpretation; discarding era fragments does not remove it. This disposal
is legitimate for the read-only JAL gate and proves no filesystem crash invariant
or active Virtio driver protocol.

## Invariants and concrete linkage

The namespaces record supplies the observation/UART mask inclusion required by
the UART permit. Wire, UART, and PLIC invariants are allocated by their existing
native rules. The observation invariant is the caller's shared invariant,
retained persistently, rather than an independently allocated trace ledger.

`registry_boot_handler` uses the caller's `InvGS_gen hlc UartGhost.registry`.
It discharges all hart, register, RAM-read, restart, UART, PLIC, and reset-disk
contracts in that same world at the common 23-slot capacity. No new invariant
world, camera, runtime-name assumption, preservation oracle, or callee-WP premise
is supplied by the client. It is suitable for the world passed by strong adequacy.

The unused auxiliary-template equality is harmless: these JAL workers consume
no kernel auxiliary-name tokens. All names actually used come from the arbitrary
allocated era and its concrete boot clients.

## Independent validation

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.JalBootHandlerLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/JalBootHandlerIndependentAudit.lean
```

The build passed 509 jobs, with only the existing unused CPU-binder warning in
`JalBootResourcesShare`. The fresh physical-origin audit checked all 25 logical
declarations in the three handler modules and their complete logical dependency
cones. Only `propext`, `Classical.choice`, and `Quot.sound` occurred; there was no
unsafe or partial semantic dependency and zero runtime exclusions. The direct
`registry_boot_handler` axiom check passed the same allowlist.

The handler closes the eleven-worker JAL boot obligation. Applying adequacy to
an actual initial state remains a separate linkage step. It establishes neither
the paper's xv6 kernel/filesystem theorem nor cross-language RISC-V refinement.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
