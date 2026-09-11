# Independent universal JAL review

Result: **PASS for the declared per-hart scope.** Reviewed the frozen
`Machine/JalLoopUniversalFetch.lean`, `Machine/JalLoopUniversal.lean`, and
`Logic/EventWPJalUniversal{Spec,Proofs,Link}.lean`, plus their status record. No
correction was required and no implementation file was changed. The reviewer
did not implement these five files, but did implement their previously reviewed
`BootPmp` dependency; that dependency was checked here for correct use rather
than counted as a new independent review of its implementation.

## Actual fetch and boot quantification

`UniversalFamily` is exactly the thirteen-field `BootUniversal.StaticBoot`
predicate and `BootPmp.Off`. `bootFacts_family` obtains both from every actual
`BootFacts jalImage` witness. There is no assumption of a zero preboot register
file, canonical PMP addresses, zero unrelated PMP configuration bits, fixed
counter filters, fixed counters, or fixed asynchronous pin values.

The fetch proof unfolds the actual generated functions. The relevant source
locations checked were `LeanPaperStock/Fetch.lean:216,232`,
`Vmem.lean:556`, `Mem.lean:221,262,393,404,460`, and
`PhysMemInterface.lean:335`. It retains the PC checks, alignment and extension
guards, Machine-mode translation, PMA checks, PMP traversal, MMIO test, RAM
request, byte assembly, and fetch-result discrimination. In this actual reset
configuration the enabled extension and alignment branches select one four-byte
fetch; PMA returns `CannotSplit` and granule exponent zero, yielding one access
of width four. The generated PMP checker still performs the configuration and
current/previous address reads for its sixteen entries. OFF makes the match
result independent of the arbitrary addresses; it does not remove those reads.

The private helper certificates use a six-field snapshot whose coverage is
proved from `Static`, with a RAM oracle that always returns `none`. Their
successful kernel reductions are converted to event plans by the checked
`snapshotPlanRun_plan` theorem. Thus they can cover no hidden RAM access or pin
read. The public universal fetch and cycle signatures have no concrete
`fetchSnapshot` coverage premise or evaluator-success assumption.

The access label follows the executable source: `read_kind_of_flags false false
false` is `Read_plain`, and `read_ram` converts it to explicit plain, normal
access even though the surrounding operation is an instruction fetch. The
`ExecPlan.readMem` proof checks both `deviceAddress req.pa = false` and
`accessExclusive req.access_kind = false`. The complete typed request remains in
the actual event; the expected response is the 32-bit word `0x6f` with no tag.
The abstract `CodeRead` predicate constrains the four-byte address and word; it
does not replace the request or itself assume successful hardware execution.

`codeRamAccess` supplies and restores the four actual byte fragments and
persistent pristine timestamp windows. The event fold invokes the concrete
pristine RAM rule, retaining its universal chosen-view continuation. This is the
ownership-backed specialization of the plain RAM read shape in pinned
`iris/HartEvents.v:137–164`; it does not assume the log is empty or require
ownership of the rest of RAM. Arbitrary MMIO or exclusive reads are not claimed
by this slice.

## Cycle closure and native infinite WP

The new cycle theorem composes the universal fetch with the existing generated
dispatch, decode, JAL execution, retirement, and clock plans. The composition
starts the fetch at `enableAfter rs`, with separate proofs that both static and
PMP facts still hold. It proves closure of the family after either tick choice.
Both counter-enable branches, the real modular arithmetic, timer comparisons,
and callback reads remain covered. Pending bits and the two hardware pins are
not assumed constant: pin reads branch independently through `ExecPlan.readPin`,
and the ownership map excludes those two pin cells. `family_pin` and
`family_plic` also show that both actual PLIC pin-write arms preserve the family.

`universal_loop_wp` uses native guarded Löb recursion. Its recursive call is
guarded by the actual restart WP's later; that rule quantifies over both clock
choices and clears the real reservation. Each cycle returns the register and
code ownership needed for the next iteration, and the returned `none`
reservation fragment is explicitly rewrapped as `resvAny`. The proof does not
infer an infinite WP from a finite execution witness.

The generic proof files expose event/restart specifications, while
`registryUniversalJalWPSpec` discharges them with the actual native register,
memory-read, and restart implementations at the shared 23-slot registry.
`registry_boot_loop` specializes to the same `jalImage` language and arbitrary
actual boot witness. Its remaining generation certificate, 178 owned register
cells, code resources, and reservation custody are real spatial premises for
the boot allocator to supply.

## Independent validation and limits

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.EventWPJalUniversalLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/JalUniversalIndependentAudit.lean
```

The build passed all 474 jobs. A fresh replay of the physical-module audit
checked all 67 logical declarations in the five modules, including private
helpers. The audit accepted only `propext`, `Classical.choice`, and `Quot.sound`,
found no unsafe or partial declaration in the logical dependency cone, and
excluded zero runtime companions. Direct axiom checks of
`universal_fetch_plan`, `bootFacts_family`, and
`registryUniversalJalWPSpec` also passed that allowlist.

The status accurately identifies a universal native **per-hart** NotStuck WP
under allocated resources. Full eleven-worker allocation and composition,
the closed machine gate, the xv6 kernel proof, filesystem crash guarantees, and
cross-language Sail/Rocq/Lean refinement are not conclusions of these files.
The pinned Rocq artifact used for source obligations is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
