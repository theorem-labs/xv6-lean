# Kernel spinlock port: source contracts and next boundary



The next production prerequisite is the source's **name-keyed held-lock set**,
including its rank and interrupt-depth laws. The first whole kernel function
target is `mycpu`, followed by `holding`, `push_off`/`pop_off`, and
`acquire`/`release`. The existing two-hart test establishes useful machine and
native WP foundations, but its protocol is not the kernel lock invariant.

## Sources and inspection

The paper artifact is pinned at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` (`arxiv-v1`); the kernel C source is
mit-pdos/xv6-riscv `45071c74c56b216a76bc08213d6c7a90b8f0688b`.
This review read the complete kernel `spinlock.c`, `spinlock.h`, and `proc.h`;
the complete `Code{Mycpu,Holding,PushOff,PopOff,Acquire,Release}.v`,
`Spec{Mycpu,Holding,PushOff,Acquire,Release}.v`, `ProofMycpu.v`, `WpLock.v`,
`LockSet.v`, `LockRank.v`, `CpuOwn.v`, and `WpNext.v`.
It additionally inspected the dependency/import boundaries of the other four
whole-function proof files, `ProcGeom.v`'s CPU geometry, `IntrDefs.v`'s actual
capability/count/handler definitions, and `TsoCtx.v`'s running/parked context
definitions. This is a design review, not a review of every proof in the
4,005-line interrupt or 6,739-line context module.

The paper's complete text was read earlier in the project. The concrete
contracts below follow the pinned definitions and proofs. Several historical
comments in `WpLock.v`, `ProofHolding.v`, and `IntrDefs.v` describe superseded
half-owner cells or an evidence-free `holding` result. The current definitions
and public specifications use **whole owner cells** and exact answers.

An independent Python ELF-segment check matched every instruction word in the
six code files against the imported `KernelElfRaw.v` bytes, including the
unreachable branches. It found contiguous coverage with these bounds:

| Function | Actual entry | Bytes | Instructions |
|---|---:|---:|---:|
| `mycpu` | `0x800018ba` | 32 | 14 |
| `holding` | `0x80000b54` | 44 | 19 |
| `push_off` | `0x80000b80` | 58 | 24 |
| `pop_off` | `0x80000bfa` | 72 | 26 |
| `acquire` | `0x80000bba` | 64 | 25 |
| `release` | `0x80000c42` | 56 | 20 |

This check is provenance evidence. Future Lean instruction theorems must use
the checked imported kernel maps and actual generated decoder, including the
two-byte alignment and mixed 16/32-bit fetch windows.

## Actual instruction and API obligations

`mycpu` saves `ra` and `s0` in a two-slot stack frame, reads **`tp`**, sign
extends its low 32 bits, shifts by seven, and adds the actual `cpus` address
`0x800123e8`. Its `AUIPC`/`ADDI` pair is `0x00011517`/`0xb2050513` at offsets
`0x0e`/`0x12`. It restores the frame and returns by `C.JR ra` at `+0x1e`.
`ProcGeom.mycpu_ret` preserves this exact modular expression; for a valid CPU
it equals `cpus + 128 * cpu`. `SpecMycpu` requires SIE=false and at least two
usable stack slots. It returns the same capability count, the exact return
PC, callee-saved agreement, and the computed `a0`. There is no CPU-cell load.
The `tp` pin must be real register ownership; the API cannot silently replace
the actual mid-function read with `mhartid`.

`holding` first loads the four-byte word at `lk+0`. Its zero fast path returns
without allocating a stack frame. The nonzero path uses four stack slots,
loads the eight-byte owner pointer at `lk+16`, calls `mycpu` at `+0x16`, and
computes equality by `SUB`/`SLTIU`. Its six-slot requirement includes the
callee's two slots. Both public forms require SIE=false. The nonholder form
takes held-set authority, `name ∉ held`, an opening credential `Tc`, and a
refutation `Tc -∗ Dc -∗ False`; it returns exactly zero and both resources.
The holder form takes and returns `locked γ cpu`, refutes `Dc` with that
token, and returns exactly one. Neither form permits a fabricated panic
continuation to absorb the wrong answer.

`push_off` uses the **single actual `CSRRCI sstatus,2` instruction**
`0x100177f3` at `+0x0a`, returning the old flags in `a5`. Splitting this into
a separate read and clear would change the interrupt boundary. When `noff`
was zero it stores the old SIE bit in `intena`; it increments `noff` at the
shared suffix. `noff` and `intena` are 32-bit words at CPU offsets 120 and
124. `SpecPushOff` requires `n+1 < 2^31` and six usable slots, preserves the
held set, returns depth `n+1`, disables SIE, and returns `arm_pay`.

`pop_off` reads `sstatus` at `+0x0c`, proves the SIE guard false, proves the
signed positive-count guard, decrements `noff`, and conditionally executes
`CSRRSI sstatus,2` (`0x10016073`) at `+0x24`. Its contract requires four
usable slots and `|held| ≤ n` when unwinding `n+1` to `n`. That premise is
essential: `|held| ≤ n+1` alone does not license the pop. Exit SIE is the
saved base bit when `n=0`, otherwise false.

`acquire` calls `push_off` at `+0x0c`, `holding` at `+0x12`, then executes
`AMOSWAP.W.AQ` (`0x0cf4a7af`) at `+0x1c`, with base `s1` and value/result
`a5`. A losing spinner still writes `1`. The loop includes the actual
`C.ADDIW a5,0` and backward `C.BNEZ`. After winning it calls `mycpu` and
stores the owner pointer at `+0x28`. The public API requires ten usable
slots and offers both the minimal fresh-family and ranked-policy tiers.
It returns the payload at the **same thread context**, a holder token at the
winning CPU, an acquire-view receipt, the enlarged held set, depth `n+1`,
and SIE=false. The log-lower-bound variants also return the corresponding
context floor; they cannot be replaced by an unrelated timestamp witness.

`release` first calls `holding`, clears the owner by eight-byte store at
`+0x12`, executes `FENCE rw,w` (`0x0310000f`) at `+0x16`, clears the
four-byte lock word at `+0x1a`, then calls `pop_off`. The invariant's
close-or-destroy choice occurs **inside that last store's callback**. The
generic, preparked, static, and cancelling specifications are distinct
clients of one proof. The cancelling form returns writable ledger storage
for both fields; discarding their ownership would prevent reclamation.

The source uses `unreachable("acquire"/"release"/...)` at the C guards.
Some proof comments call these panic arms. The instruction bytes remain in
the image; their unreachability must follow from the stated resources.

## Native prerequisites and exact resource distinctions

1. **Held sets and ranks.** `lockSetR = authR (gset_disjUR string)`.
   Authority is per CPU at `era_lockset_name`; a singleton fragment lives
   beside the owner cell only in `Some(cpu,true)`. This is disjoint-set
   ownership, not the persistent union-set membership used by dirty sets.
   Insertion requires absence; deletion consumes the singleton and proves
   membership. Names distinguish families even if ranks coincide. The
   source table is log=1, bcache=2, cons=3, sleep lock=4, pipe=5, time=6,
   virtio_disk=7, wait_lock=8, proc=9, nextpid=10, kmem=11, itable=14,
   ftable=15, pr=16, uart=17; unknown names have rank zero. Ranked acquisition
   is a policy tier over freshness, not a fairness or global termination
   theorem. The documented `iput` exception cannot be erased.
2. **Lock state and acquisition position.** The exact product camera is
   already at slot 24. Kernel `locked` additionally carries a context floor
   at the same position as its fragment. The physical transitions are free,
   acquired-with-owner-zero, owner-set, owner-cleared, free. The existing test
   uses only the owner-zero arm and cannot be substituted here.
3. **Two different ledger payloads.** `lock_word_pin B` constrains every
   post-acquire byte to the corresponding byte of `1`, so losing AMOs can
   preserve the holder's fact. The owner cell instead uses an eight-byte
   `TsWin` with per-agent own-last records, mint floor, and anchored
   visibility. Only the current owner may lack an own-last record. CPU
   pointers are injective and nonzero, but there is no single byte that
   distinguishes every CPU from all others: the proof needs a whole-word
   window. Existing `TsoStore` writes payNone; it does not yet implement the
   pin-preserving/window-preserving source store gates.
4. **Thread contexts.** The existing mono-nat and dirty-set cameras support
   the construction, but `TsoCtx`'s full native running/parked tokens,
   clean/dirty byte ownership, context morphisms, deposit/absorb, and
   `lk_floor = ctx_floor ∨ own-write witness` still need their source laws.
   A bare log-length receipt does not prove a creator observed its buffered
   store. `lock_pay` parks a fresh context on each publication; acquisition
   absorbs it using actual top-view evidence. No context-irrelevance axiom
   or universally visible mutable owner word is acceptable.
5. **Supervisor execution and migration.** `sconf` owns Supervisor privilege,
   real mstatus plus its SIE/SPP/SPIE ghost ties, source hardware/configuration
   facts, `minstret_inv`, `mie=MIE_S`, delegation, and MENVCFG constraints.
   `sie_cap` adds stack ownership, translation invariant/tier witness,
   running context, timer capability, and the SIE-dependent arm. SIE shares
   are one half tied to mstatus, one eighth in the cap, one eighth in the
   depth token, and one quarter with the installed-handler resource.
   The enabled arm carries the CPU-private cells/held set and trap resources;
   duplicating them outside that arm would make the premise unsatisfiable.
6. **Exact context crossing.** `wp_next b p` may rebind the CPU but retains
   the thread context. It pins the CPU when SIE is false or `p=0`, the latter
   requiring the real handler's non-yield argument. `ihs` is a contractive
   native Iris fixpoint with an environment family and its crossing law.
   Acquire's entry may migrate before its clear; release may migrate after
   its enable. Trap reserve is 90 slots when enabled and zero when disabled;
   push/pop reindex the same total stack carve rather than allocating it.
7. **Translation and code.** The source universally quantifies the KT0/KT1
   tier. Its per-byte lock mapping claims and Supervisor fetch/PMP/page-walk
   rules remain explicit obligations. Current M-mode reset-PMP plans are not
   a proof for Supervisor mode (all-OFF PMP is particularly not its access
   proof). Source `kernel_text` is persistent discarded **text** ownership
   over checked image bytes; mutable lock/stack storage stays writable.

## Current critical path

The sixth Fable review moves the supervisor substrate and ordinary stack
readback ahead of the lock leaves. The detailed source-compatible boundary
is [mycpu-wp-boundary.md](mycpu-wp-boundary.md). It unfolds only the disabled
SIE capability, retains its SIE eighth and running context, and frames the
separate CpuOwn resources. Enabled interrupt dispatch and migration are not
prerequisites for this first function.

The source uses MENVCFG_S with ADUE and STCE set and PBMTE clear. Actual
translation must prove its Accessed/Dirty behavior, including any PTE stores,
and retain the real TLB behavior at both kernel tiers. Supervisor PMP grants,
mixed-width fetch, all cycle clock choices, native own-author readback,
ordinary context stores and fractional register folding precede the complete
function WP. Bare-only or decode-only results remain explicit prerequisites.

## Reviewed lock leaf implementation

New `LockRankDefs`/`LockRankProofs` and
`LockSetDefs`/`LockSetSpec`/`LockSetProofs`/`LockSetLink` expose the full
finite `Std.ExtTreeSet String` domain. The camera is native
`Auth (DisjointLeibnizSet Names)`, using Iris's actual inclusion, disjoint
allocation, and deallocation laws. It has an explicit `Capacity GF`; raw
predicates take an explicit ghost name, and era wrappers use
`Era.Record.heldLocks cpu` without inventing an allocation witness.

The concrete registry extension uses new slot **26**, preserves slots 0–25
of `FsTop.registry`, and exports explicit lifts for existing consumers.
No old capacity or canonical-name field changes. Allocation returns a fresh
authority at the empty set; connecting eight such names to an actual boot
era remains a later obligation. The proof/spec boundary includes agreement,
singleton exclusivity, fresh insert, consuming delete, level introduction and
elimination, upward weakening, releveling under the exact new size bound,
zero-level emptiness, and the exact rank/set/cardinality laws. Each is
kernel checked; the whole physical declaration cone has passed independent
audit. These leaves do not establish a kernel function theorem.

The subsequent `mycpu` checkpoint must retain the source contract: all
valid CPUs, arbitrary caller registers and writable two-slot frame, actual
mixed-width code/fetch/execute, Supervisor SIE=false at both translation
tiers, callee-saved/return-PC facts, and ordinary native WP continuation.
It may be developed through explicit lower-level proved contracts, but will
not be reported as a completed function port until those contracts have
native implementations. A fixed reset-state execution sample would not
discharge this boundary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
