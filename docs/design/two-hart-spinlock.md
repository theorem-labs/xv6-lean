# Two-hart spinlock gate: proposed contract

This is a design for review, not an implemented lock theorem. The next gate will
execute real lock instructions on the existing eight-hart machine, prove native
resource transfer and safety under arbitrary interleavings, and expose a separate
operational mutual-exclusion theorem. Harts zero and one participate; harts two
through seven execute a checked branch into a real `jal x0, 0` loop. UART, PLIC,
the reset disk, clocks, TSO views, reservations, and power cycles retain their
current transition rules.

The paper's Section 3 spinlock illustration explicitly assumes sequential
consistency. Its implementation pattern is useful, but its displayed SC
points-to invariant cannot be imported as a TSO proof. The pinned artifact is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; all source references below refer to
that revision. The generated RISC-V model remains at the existing paper-model
pin `23dcf8fd923eb8a1958795393d2975632aa940b2`, with the already checked runtime
and platform adapter. No instruction or event definition changes are proposed.

## Concrete program and image

The proposed image has 68 instruction bytes at `0x80000000`, a four-byte lock at
`0x80001000`, and a four-byte protected counter at `0x80001004`. The existing
boot-image rule supplies zero to RAM outside the instruction image, so both data
words start at zero on every boot. All accesses are naturally aligned and lie
in the existing RAM/PMA interval. These data words and the code window are
pairwise disjoint. The initial durable disk remains a separate arbitrary input.

The program uses uncompressed 32-bit encodings to keep byte offsets explicit.
It implements the paper's simplified acquire/release pattern in M-mode, plus
hart selection and a protected increment. It is not the compiled xv6
`acquire`/`release` implementation: it has no owner field, stack frame,
`holding`, `push_off`, `pop_off`, supervisor translation, migration, cancellation,
or lock-ranking contract. Those source contracts remain later port targets.

| Offset | Little-endian bytes | Instruction |
| --- | --- | --- |
| `00` | `f3 22 40 f1` | `csrrs t0, mhartid, zero` |
| `04` | `13 b3 22 00` | `sltiu t1, t0, 2` |
| `08` | `63 0c 03 02` | `beq t1, zero, park` |
| `0c` | `17 15 00 00` | `auipc a0, 1` |
| `10` | `13 05 45 ff` | `addi a0, a0, -12` |
| `14` | `13 07 10 00` | `addi a4, zero, 1` |
| `18` | `93 07 07 00` | `spin: addi a5, a4, 0` |
| `1c` | `af 27 f5 0c` | `amoswap.w.aq a5, a5, (a0)` |
| `20` | `9b 87 07 00` | `addiw a5, a5, 0` |
| `24` | `e3 9a 07 fe` | `bne a5, zero, spin` |
| `28` | `03 28 45 00` | `lw a6, 4(a0)` |
| `2c` | `1b 08 18 00` | `addiw a6, a6, 1` |
| `30` | `23 22 05 01` | `sw a6, 4(a0)` |
| `34` | `0f 00 10 03` | `fence rw, w` |
| `38` | `23 20 05 00` | `sw zero, 0(a0)` |
| `3c` | `6f f0 df fd` | `jal zero, spin` |
| `40` | `6f 00 00 00` | `park: jal zero, park` |

The proposal was assembled and linked with `norvc`, `norelax`,
`-march=rv64ima_zicsr`, and `--no-relax`; disassembly and raw bytes agree.
The raw `.text` SHA-256 is
`4672cbbba2c4565cea551da3b8fe8bfc16f545a78aae0b8bb83f5fdebd6ee24a`.
Research files are under `/tmp/xv6-lean-research/two-hart-spinlock/`.
This assembler check is a design check only. Acceptance requires kernel-checked
byte lookups and the actual generated fetch/decode/execute plans for these words;
assembler correctness will not become a logical premise.

`BootHartId.bootFacts_hartid` now proves the exact hart ID for every actual
`BootFacts` witness through `registerRun_unique`; its selection theorem proves
the unsigned comparison agrees with CPU index below two. The existing universal
reset facts also retain atomics-enabled `misa` and clear machine interrupt-enable
fields. These facts must discharge the actual generated AMO and interrupt checks. The control-state family must separate the fixed reset fields from the
changing PC/nextPC and scratch registers. It must retain arbitrary counter
configuration, pending interrupts, PMP addresses, unrelated PMP bits, and both
clock choices. The existing `BootPmp.Off` and 16-entry generated PMP plans should
be reused for instruction fetch and data accesses.

## Required conclusions

The closed safety root should have the same external shape as
`JalMachineSafety.safe`, replacing only the boot image. It must discharge the
complete eleven-worker handler and quantify over every actual finite
`PoolSteps` run from the powered-off generation-zero initial state. There must
also be an explicit platform/state inhabitant and a positive real execution.

The lock API must establish genuine ownership transfer. Successful acquisition
returns one exclusive holder token and the protected counter resources; failed
acquisition returns neither. Release consumes both and returns them to the lock
invariant. A native entailment `held 0 ∗ held 1 ⊢ False` is necessary, but is not
alone an operational mutual-exclusion theorem.

The primary operational target is exclusion of simultaneous holder windows.
A holder window is defined over actual PC and generated continuation: it starts
at the successful conditional-write arm whose reservation recorded zero, and
ends at the successful unlock-write event. It includes the intermediate branch
and unlock stages, with precise before/after-event boundaries. A corollary is
that no reachable powered-on state has both CPU zero and CPU one in the critical-body PC set
`{0x80000028, 0x8000002c, 0x80000030, 0x80000034}`. The unlock instruction at
`0x80000038` is deliberately outside this set: its memory event can release the
lock before the instruction retires and before its PC changes. The proof must
track actual generated continuations, not infer instruction completion from a
PC value alone. Stale-era threads and power-off states must be handled explicitly.

For interference, require a checked positive schedule in one era that includes:

1. After CPU zero reads zero exclusively, keep its exact zero snapshot live.
   Schedule CPU one's exclusive read and record its blocked result: its cursor
   remains at that read and its reservation is now `none`.
2. Complete CPU zero's swap and first counter increment. Let CPU one read the
   held lock word, installing a snapshot containing one, but do not yet commit
   CPU one's swap. Schedule CPU zero's unlock write and record its blocked
   self-loop with CPU one's reservation still live.
3. Commit CPU one's swap of one, which fails to acquire and clears its reservation.
   Then complete CPU zero's pending release.
4. Let CPU one acquire successfully, read counter value one, increment to two,
   and release. The final log contains exactly seven authored messages, the lock
   is zero and the counter is two.

Each endpoint must expose its actual intermediate configuration and continuation,
not merely an existential final `PoolSteps` result. The zero snapshot in item 1
is gone after CPU zero's successful swap, and the one snapshot in item 2 is gone
after CPU one's successful write; neither can be asserted at those later states.
All other workers remain in the pool. Counter arithmetic is `BitVec 32` modular
addition. The gate requires the concrete counter-two witness above; a separate
universal counting invariant must count completed increments, accounting for a
holder's pending release, rather than equating the counter with completed
releases in the middle of the critical section. Safety and exclusion do not
assert fairness or completion on every schedule; power may fail at any event.

## TSO and atomic-event boundaries

The source event contracts are `HartEvents.v:763` (`swp_hart_ram_read_excl`),
`:797` (`swp_hart_ram_write`), and `:841` (`swp_hart_ram_write_cond`). Their
generated AMO adapters are `HartSMem.v:4698`, `:4736`, and `:4767`; `WpAmo.v`
provides the actual AMOSWAP read/write/execute decomposition.

An AMOSWAP is not one operational step. Its exclusive read either blocks,
clearing this hart's reservation, or reads the current flat bytes, advances this
hart's view to the log length, and installs their exact snapshot as a
reservation. Later register, translation, and callback steps remain
interruptible. A successful RAM write appends exactly one authored snapshot,
updates the physical bytes, and clears the reservation. The conditional AMO
write advances the writer's view past its own new append. Conflicting writes
self-loop without clearing reservations or changing views. None of these arms
may be removed by a proof-side disjointness assumption. The pool supplies the
actual conflict set from every other CPU reservation, and `ReservationsOK`
quantifies over those same fields. The existing era interpretation already
carries that invariant; event and device rules must preserve it, and boot must
initialize it. A source node parameter cannot be instantiated with an invented
empty conflict set.

The read callback opens and recloses the lock invariant for that single event.
It returns the observed word and reservation custody, not an invariant held
open across the rest of the instruction. At the conditional write, reservation
agreement and the actual `ReservationsOK` interpretation establish that the
current old bytes still equal the exclusive-read result. The write callback can
then perform the lock resource transfer and close the invariant at the new word.
The proof must preserve the actual optional write payload/result protocol;
absent payloads return purely in the builtin and do not create a write event.

A failed AMOSWAP still writes one. Consequently the latest lock-word author can
be a spinner while the holder is the other CPU. The invariant must not identify
the latest writer with the lock owner. The source documents this exact issue in
`WpLock.v:1329–1370` and uses an acquisition-position/state ghost tie instead.

`fence rw,w` is non-draining in the actual ZTSO semantics
(`RiscvLang.v:735–747`). A draining fence orders W→R and sets the view to
`max oldView (ownPub hart log)`, not to the log top. `HartBarrier.v` distinguishes
`pub_step` from `ghost_step`: the latter accesses the live interpretation without
inventing a drain receipt and applies even to non-draining barriers. The gate
must preserve `rw,w` as written. Its next successful AMO supplies the acquire
view that sees the preceding owner's counter writes: the exclusive read sets
the view to the then-current log length, timestamp validity bounds the protected
counter's position by that length, and the conditional write advances the view
past its own append. A native view receipt transports this bound to the later
plain read. This uses the actual exclusive-read rule, not the `.aq` bit or a
store-ordering claim about the non-draining fence. `TsoReadAt.window_read` and
`power_read` now prove the ownership-to-read bridge with arbitrary timestamp
payloads. The fence can use `BarrierWP.wp_identity` for this gate. Replacing the fence with a stronger one would
change the proposed program and would not prove its existing bytes.

## Ownership and invariant contract

The code window uses the existing native physical-byte fractions and pristine
timestamp resources. Share it across all eight CPUs, retaining the separate 16
full PLIC pin cells. The writable lock and counter keep full byte and timestamp
fragments; neither becomes discarded/pristine. Heap metadata remains framed
through updates, and boot resource extraction returns all unselected memory.

The first machine-mode lock layer can expose physical ledger words and explicit
timestamp/view receipts, because this gate has no context migration or virtual
translation. Its protected resource is a full four-byte counter ledger at an
explicit timestamp, plus the facts needed to establish visibility after acquire.
Full source `TsoCtx` transport is not claimed by this restricted API. The later
xv6 API must port `ctx_deposit`, `ctx_absorb_lb`, `lock_pay`, and `lock_pay_won`
(`TsoCtx.v`, `TsoCtxAbsorbLb.v`, `WpLock.v:1242–1254`) rather than silently
replacing context-indexed payloads by hart-indexed facts.

A proposed native lock ghost uses the source product of exclusive authorities
for lock state and acquisition position (`Xv6Cameras.v:111`), with explicit
capacity and names. Its slot must extend `FsLink.registry` without changing
slots 0–23: the filesystem occupies slot 23, so the proposed lock camera uses
slot 24. The simplified
gate uses the holder-window state and does not pretend to establish the source
owner-field/held-lock-set assertions. No new camera is needed for the basic TSO
store and barrier rules.

Observation, UART, PLIC, wires, and lock namespaces should be concrete distinct
siblings. The callback that opens the lock invariant must contain that namespace
in its current mask and restore it before executing another machine event.
The native memory-event rules use the existing top-to-empty/empty-to-top mask
discipline with the required later; a whole AMO, function call, or busy loop must
not be treated as the duration of one invariant opening. Frame the generation
certificate and actual reservation fragment through every intermediate event.
Dead-generation behavior remains the existing stale-thread step.

## First implementation contracts and ownership

The root owns new `TsoAppend{Defs,Proofs}`: untouched-address append preservation
for all `WindowOK`, `ReleaseOK`, `WordPinOK`, and `TimestampOK` payload arms, then
the exact `TimestampMapOK` update bridge. This is required even when a new write
mints `payNone`, because all untouched timestamp payloads remain in the map.
The store proof must not assume those framed payloads are absent. This layer
is now proved: `appendTimestamps_lookup` gives the exact pointwise new-or-old
lookup, and `timestampMapOK_store` uses it to discharge the right-biased map
replacement. No conclusion relies on the union-bias comment alone.

Proposed first owned implementation: `TsoStore{Defs,Spec,Proofs,Link}`. Its core
is the native counterpart of `TsoCtx.ledger_store_ok` at line 3951, followed by
the byte-window specialization at line 4153. Inputs are full native heap and TSO
interpretations plus full old physical-ledger fragments over a finite map.
The old and new finite maps have equal domains. The explicit successor equations
are unchanged image, one appended message authored by the supplied agent,
left-biased overlay into physical memory, monotone hart views bounded by the new
log length. Outputs are the updated full heap/TSO interpretation, a persistent
receipt for the exact new message, and full new byte/timestamp fragments at
`oldLog.length + 1`. The new timestamps use `payNone`; framed existing payloads
are preserved by the root's append bridge. All heap metadata and runtime names
are retained. The finite-map decoder ties the message to the actual functional
snapshot; no second byte camera or independent physical authority is allocated.

Next, `MemoryWriteWP{Defs,Spec,Proofs,Link}` lifts this update through the actual
RAM event, power interpretation, reservation authority, and observations.
The rule accepts a present payload, keeps its complete request, and proves
both the blocked self-loop and successful append cases with native guarded
recursion. It returns the actual `Ok none`, the cleared reservation on success,
and the exact post-view receipt. Its conditional-write specialization takes an
actual snapshot reservation and proves the old-byte equation from state
interpretation validity; it does not assume the old value or invent a success
flag. The ordinary word-window specialization should state the source's width
bound below `2^64` where snapshot injectivity is used.

`BarrierWP{Defs,Spec,Proofs,Link}` can be a small independent follow-up: an
all-barrier native rule implementing exact `fencePost`, plus separate draining
publication and general ghost-step interfaces matching `HartBarrier`. It must
not introduce a receipt of the global log top for a draining fence, or a drain
receipt for this gate's `rw,w` fence.

`MemoryExclusiveWP{Defs,Spec,Proofs,Link}` then provides the exclusive-read rule
and its reservation result, including the clearing blocked arm. Combine it with
the conditional-write rule and actual generated AMO plans. Extend `ExecPlan`
through a separately reviewed interface for write, barrier, and exclusive read
events; the existing JAL plan constructors remain valid. A resource extraction
and restoration contract must discharge each event, not accept a callee-WP
oracle or an existential selected schedule.

## Remaining proof architecture before claiming the gate

Generated instruction plans are needed for the CSR read, hart branch, address
construction, AMO, ordinary data load/store, fence, and all back edges. Fetch
ownership must be generalized from one fixed JAL word to the certified image
at every reachable PC. The parked-six proof still executes real instructions
and clocks; it is not a semantic halt or an unscheduled-thread assumption.
The UART, PLIC and reset-disk worker implementations can be reused because this
program never configures a device. The boot handler must allocate fresh lock
resources per era and retain the common observation invariant across eras.

The chosen operational bridge is a concrete annotated-pool simulation over
actual generated continuations, with native Iris WPs retained for safety and
resource transfer. An annotation marks dispatch, pending/read-reserved AMO,
post-swap success/failure, held body, pending unlock and post-unlock phases;
its control relation refers to the actual residual Sail program. The simulation
must lift every actual pool step, including device, stale-thread and power
steps, to a matching annotation successor. Erasing annotations leaves the
machine and its transition relation unchanged. No preservation callback may
remain as a premise of the closed theorem.

[The architecture appendix](spinlock-exclusion-architecture.md) records the
bounded `ControlAt`, `ProtocolInv`, `protocol_pool_step`, all-run lifting,
holder-window exclusion and PC-inclusion interfaces. First freeze the exact
phase boundaries, prove the small protocol transition's unique-owner law, and
prove one actual AMO residual decomposition. Reuse generated event plans and
machine inversions across the native and pure proofs.

This choice avoids changing the fixed `MachineInterp.irisGS` underneath every
existing WP rule. Native `wp_strong_adequacy_gen` already exposes the final
state interpretation, but that interface receives only a thread count and
cannot inspect intermediate continuations. A state-only extension can support
a PC corollary; it does not supply the stronger holder window by itself.
Nor can the source lock's full exclusive authority be duplicated between the
lock invariant and an extra state-interpretation component. A PC/owner extension
would require explicit authority placement and concrete proof transport for all
relevant events. PLIC writes both hardware pin registers and must be treated by
its actual PC-preservation proof. A spinlock safety checkpoint leaves the
operational target open; the gate requires safety, exclusion and the
interference witness together.

The full source lock contracts remain visible dependencies rather than claimed
outputs: `SpecAcquire`/`ProofAcquire` (the guarded spin loop at line 102),
`SpecRelease`/`ProofRelease` (the actual `rw,w` and store at lines 288–302),
`WpSconfLock`, the owner-state invariant in `WpLock`, and context transport.
They inform the primitive rules now and delimit the additional work required
to port actual xv6 acquire/release later.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
