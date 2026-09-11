# Native supervisor `mycpu` proof boundary



This is an implementation proposal, not an implemented function WP. The
smallest source-compatible boundary is the **interrupts-disabled branch of
`sie_cap_gpr`, with its real context-indexed stack**, followed through the
actual fetched Sail instruction cycles. It does not require the enabled
interrupt-handler fixpoint or `CpuOwn.cpu_own`. It does require supervisor
translation and PMP grants, fractional register ownership, ordinary-store
forwarding, and both choices of the actual cycle clock. A Bare-only or
execute-only theorem would be a named intermediate milestone, not the
source `MYCPU` interface.

All source references below are relative to `.upstream/xv6iris/iris/`, pinned
to `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The kernel is
`45071c74c56b216a76bc08213d6c7a90b8f0688b`. The full `SpecMycpu.v` and
`ProofMycpu.v` were read, together with the definition/proof sections cited
below. This document does not claim a full read or port of the 6,500-line
`TsoCtx.v` or all interrupt-handler proofs.

## Exact public contract and executable footprint

`SpecMycpu.v:31–47` requires `2 ≤ n`, `sie_cap_gpr kt m0 n false p`, kernel
text, and `pc_is KernelSyms.mycpu`. It returns the same capability count,
context, hart, tier, and `p`; `pc_is (ret_pc ra0)`; the actual callee-saved
relation; and `a0 = mycpu_ret (rget m0 tp)`. The function proof
`ProofMycpu.v:59–317` uses all 14 image instructions. Its JAL-call wrapper
is `SpecMycpu.v:58–77` / `ProofMycpu.v:323–351`.

The bytes occupy 32 bytes at `0x800018ba`. `CodeMycpu.v` supplies the
instruction facts; a separate agent owns their Lean image/decode port.
The addresses and old-value stack obligations are:

| Offset | Actual operation | Resource effect |
|---|---|---|
| `00` | `c.addi sp,-16` | Split two eight-byte scratch slots from the free stack; remaining depth `n-2`. |
| `02`, `04` | `c.sdsp ra,8(sp)`; `c.sdsp s0,0(sp)` | Two separate ordinary eight-byte RAM writes, saving entry `ra` and `s0`. |
| `06` | `c.addi4spn s0,sp,16` | Set the frame pointer. |
| `08`, `0a`, `0c` | `c.mv a5,tp`; `c.addiw a5,0`; `c.slli a5,7` | Read actual `x4`, sign-extend its low 32 bits, multiply modulo 64 bits by 128. |
| `0e`, `12`, `16` | `auipc a0,0x11`; `addi a0,a0,-1248`; `c.add a0,a5` | Form the actual linked `cpus` address plus the computed offset. |
| `18`, `1a` | `c.ldsp ra,8(sp)`; `c.ldsp s0,0(sp)` | Read back both saved words at every permitted TSO read view. |
| `1c`, `1e` | `c.addi sp,16`; `c.jr ra` | Return the two slots, restore stack depth, and jump to the actual cleared-low-bit return target. |

The exact modular result is `ProcGeom.v:772–785`; for a valid hart it is
`0x800123e8 + 128 * cpu`. Preserve the modular form as the primary theorem.
`CalleeSaved.v:34–47` preserves `sp`, `s0`, `s1`, and `s2` through `s11`.
It does not preserve every register. `ra` is additionally restored by this
particular function. The scratch stack contents may change: the returned
stack assertion existentially hides its words.

`HartTp.v:50–70` defines `tp_pin` and `rget`: the source register map's
nominal `tp` entry is replaced by the actual hart identifier. A Lean
interface must either own a GPR projection with this same override, or
explicitly require and preserve actual `x4 = cpu`. It cannot replace the
mid-function `x4` read by `mhartid` or assume a generated read returns the
nominal map entry.

## Unfold only the off branch

`IntrDefs.v:3224–3229` expands the public bundle into active hart state,
`sconf`, `sie_cap`, and `gpr_file (tp_pin m)`. At `false`, the capability is
exactly the following source partition:

- `stack_own kt sp n`, because `trap_res false = 0`
  (`IntrDefs.v:571–577`, `2762–2769`).
- `strans_inv`, whose alternatives are the Bare pending half, actual Bare
  translation resources and an existential `stvec` cell, or the KPT
  authority and existential-root `tlb_res_pt`
  (`IntrDefs.v:1212–1214`).
- A canonical SIE ghost eighth at zero, using
  `Era.Record.supervisorInterruptEnable cpu`
  (`IntrDefs.v:309`, `2672–2685`).
- `own_context ξ`, the persistent timer capability, and the tier witness
  (`IntrDefs.v:2762–2769`).

The false branch contains no `intr_res`, `cpu_claim`, `cpu_hart`, enabled
`sepc/scause/stval` bundle, or recursive handler specification. In particular,
`CpuOwn.v:66–98` defines a different resource: it becomes `cpu_hart` while
off, and a pure depth/enable/empty-set fact while on. **Do not add it to
`mycpu`'s premises.** A caller can frame its CPU cells, interrupt nesting
count, held-lock authority, and current-process ownership through this
function. The function's `p` parameter is not a requirement to own or read
`cpus[cpu].proc` in this off branch.

`WpNext.v:54–57,69–88` proves that `wp_next false p K` is equivalent to the
same-hart continuation. This is a resource equivalence, not a license to
assume interrupt dispatch succeeds. The generated dispatch proof must
establish the no-interrupt result from actual supervisor status and mask
reads. The enabled migration and handler-return contracts remain outside
this first boundary.

## Concrete hardware, cycle, and translation resources

The off `sconf` must retain its source definition, not a reset snapshot.
`IntrDefs.v:595–625` owns supervisor privilege, actual `mstatus` with its SIE
half and SPP/SPIE ties, `mie = 0x220`, an arbitrary `mideleg` satisfying
`mie & ~mideleg = 0`, and `menvcfg = 0xA000000000000000` with the listed
PBMTE=0/PMM/LPE/FIOM facts; ADUE=1 and STCE=1. `sconf_ms_facts` at lines 196–206 requires MPRV
clear, SXL=64, MXR clear, TSR clear, XS/FS/VS Off, SD clear, valid MPP and
TVM clear. SIE=0 follows by agreement with the off eighth. Preserve other
unconstrained status bits; do not require reset `mstatus` or MIE=0.

`RiscvFetchExec.v:288–333` supplies persistent hardware resources:
`misa = 0x800000000014112D`, `mseccfg = 0`, permissive actual PMA regions,
HTIF base `None`, non-expected ELP, `senvcfg = 0`, the stated extension and
masking facts, static mapping claims, generation certificate, and arbitrary
`scounteren`/HPM-counter read resources. Its old prose about counter-config
placement is not authoritative; use the current definitions.

`InstrBytes.v:701–706` makes `pc_is pc` own **both PC and nextPC** at `pc`,
`minstret_res`, `clock_res`, and an arbitrary reservation fragment. In the
pinned source `minstret_inv = emp` (`MinstretInv.v:341`). The actual resource
bodies at lines 349–363 own mutable `minstret`, `minstret_increment`,
`mcycle`, `mtime`, and `mip`, with persistent `mcountinhibit` and
`minstretcfg` reads. A native port must not resurrect an invariant held
open across multiple counter subevents.

The generated clock also reads `mcyclecfg` and `mtimecmp`; no facts about
their values are required. Their occurrences can use the existing
`RegisterWP.readAny` rule with universally quantified continuations, just
as actual hardware pin reads do. Where the exact source resource closure
already owns a cell, use that ownership without allocating a duplicate.
`timer_cap` is `sstc_enabled ∗ stimecmp_inv`
(`TimerCap.v:54–56,78–83`): the source's `mcounteren.TM=1` persistent fact
and a real invariant holding an arbitrary full `stimecmp` cell. It is
preserved even though `mycpu` does not issue a timer CSR instruction.

The source supervisor constant enables STCE. Therefore the actual
`Platform.clint_dispatch` Sstc branch must be retained, including its
`stimecmp` read and STIP update, as well as MTIP, overflow, every inhibit
branch, and conditional CSR callback. Read/write subevents may interleave;
there is no frozen `mip` or zero deadline premise. Pending timer/external
pins remain arbitrary. The actual `mie`/delegation/SIE facts dismiss their
delivery rather than deleting their reads. The existing Machine-mode JAL
clock/dispatch proofs are useful decompositions, not supervisor theorems.

Translation is a genuine second prerequisite:

- `SmodePte.v:31–39` requires actual PMP vector ownership and entry 0 in
  TOR mode, positive upper bound, RWX permission, and coverage through the
  end of RAM. Later entries and irrelevant bits stay unconstrained. The
  actual grant lemmas start at lines 86 and 125. The existing
  `BootPmp.check_off_plan` is explicitly for Machine privilege and does
  not supply this grant.
- Bare (`SRegime.v:833–837`) owns `satp` with Mode=Bare and PMP resources;
  it deliberately owns **no TLB cell**. Its data claims are identity
  mappings. Arbitrary ASID/PPN fields consistent with Bare stay allowed.
- KT1 permits nonidentity kernel-stack mappings. It requires the actual
  KPT/TLB resource and its all-claims witness. KT0 identity-mapped data can
  also be used after KPT installation. Do not equate KT0 with an exclusively
  Bare current hart. `RiscvPtsto.v:1206–1209` and
  `SRegime.v:1762–1766` state these two distinct tier conditions.
- The mutable stack's per-byte claims are KP_rw; text claims are executable.
  Page walks, TLB hits/misses, protection checks and source A/D conditions
  need actual generated proofs. A `translateCorrect` callback assumed as
  a theorem premise would merely relocate the missing software proof.

## Small context and stack implementation slice

Reuse the existing native mono-nat slot 3, view slot 2, dirty-set slot 5,
log slot 4, and byte/timestamp slots 0/1. No new context camera is needed.
Use two explicit fresh names per `CtxId`; do not identify their authority
with the global log length or duplicate a CPU view authority.

Implement exactly `TsoCtx.v:244–305`:

```text
ctxAt ξ q B D = monoAuth ξ.bound q B ∗ dirtyAuth ξ.dirty q D
ownContext era cpu ξ =
  ∃ B K W D, ctxAt ξ 1 B D ∗ viewLB era cpu K ∗ ⌜B ≤ K⌝ ∗
    logLB era W ∗ ⌜∀ key ∈ D, key.time ≤ W⌝ ∗
    ∗ key ∈ D, dirtyOK era.logEntries (hartAgent cpu) B key
```

Implement the source physical byte assertion (`TsoCtx.v:2095–2101`):
full/fractional physical byte plus matching `(timestamp, payNone)` ownership,
justified either by `llb ξ.bound timestamp` or dirty-set membership
`(timestamp,address)`. The zero timestamp alternative is part of `llb`;
it is not an assumed global pristine-memory condition. Lift it with the
actual mapping claim, low canonical VA bound `< 2^38`, RAM fact, and tier
pin from `ctx_pointsto_def` at lines 628–638. The word assertion adds
8-byte alignment and eight individual byte facts (lines 845–849).

`StackOwn.v:155–157` then defines the complete finite stack as existential
words and a separating conjunction at `sp - 8*(i+1)`. Prove its exact
split/join laws (`170–208`), specialize to two slots, and retain arbitrary
contents and the remainder. No new 16-byte stack alignment premise is
needed: the source word assertions require eight-byte alignment. Do not
add a global no-wrap restriction in place of the source per-byte canonical
mapping/RAM conditions. Unsatisfiable overlapping ownership should be
refuted by validity, not silently excluded with a stronger public premise.

The two required native context gates are:

1. **Load:** from the live full heap/TSO interpretation, `ownContext` and a
   context byte, derive the same byte for every `view ≥ g.views cpu`,
   returning all resources. This is `ctx_load_ok`, lines 1804–1817. The
   clean arm reuses `TsoReadAt.byte_read`; the dirty arm needs the authored
   forwarding proof using existing `History.dirtyOK_visible`, log authority,
   timestamp validity and current value ownership. Neither arm assumes
   `timestamp ≤ view` for a dirty local store.
2. **Store:** for the actual same-domain RAM overlay and one authored log
   append, update the full heap/TSO and dirty authority, retain the running
   token, and return registered bytes at the new time. This is
   `ctx_store_ok`, lines 2572–2587, via `ctx_store_free_ok`, lines 2430–2450.
   Reuse `TsoStore` and its stored-window/log receipt. Insert all eight new
   dirty keys, update the watermark, and justify every new key by its real
   message. Old dirty members and off-address payloads remain intact.

These are concrete proved resource transformations, not assumed Access
fields. Their finite-window adapters must construct the actual native
`MemoryReadWP`/`MemoryWriteWP` callbacks. An ordinary stack store leaves the
hart view unchanged; adding a fence or receipt advance to make readback
convenient would change the function.

No context parking, `CtxMorph`, context domination, lock payload transfer,
interrupt-handler fixpoint, or process state is necessary to complete this
off-only slice. Those source APIs remain future work, not dummy definitions.

## Native theorem and proof execution boundary

The intended theorem, with the proposed names still unimplemented, is:

```text
wp_mycpu [Platform] [InvGS_gen hlc GF]
  (capacity : concrete KernelOff.Capacity GF)
  (image fixed whole gen era cpu ξ kt m0 n p post) (hn : 2 ≤ n) :
  ⊢ offCapGpr capacity era cpu ξ kt m0 n p -∗
    kernelText capacity era -∗ cycleAt capacity era cpu mycpuEntry -∗
    (∀ m', offCapGpr capacity era cpu ξ kt m' n p -∗
      cycleAt capacity era cpu (retPc (m0 ra)) -∗
      ⌜calleeSaved m0 m' ∧ m' a0 = mycpuRet (cidWord cpu)⌝ -∗
      threadWP capacity.machine image fixed whole (.hart gen cpu (pure ())) post) -∗
    threadWP capacity.machine image fixed whole (.hart gen cpu (pure ())) post
```

`offCapGpr` is the explicit off expansion above; `cycleAt` is the exact
`pc_is` partition. `kernelText` must tie its bytes to the imported image.
Generation/image obligations are real resources, not pure name equality.
The final continuation is the caller's native WP at the returned machine
boundary, not a callback asserting the correctness of `mycpu` or a cycle.
No function correctness, schedule restriction, chosen tick, read-result
oracle, or extra `InvGS` allocation occurs among the premises. This is a
conditional compositional function rule over real resources; it is not yet
a boot-to-kernel safety theorem. Its allocation/provenance and a concrete
satisfiability witness must accompany its eventual integration.

The existing `EventPlan.fold` cannot be applied unchanged: it demands full
ownership of all 178 non-pin cells, while this source bundle includes
persistent fractions and an invariant-owned timer cell. The implementation
should use a separate finite register-footprint fold or instruction-local
native folds built from `RegisterWP.read/write/readAny`. Fractional/discarded
reads return their tokens; writes require full tokens; unowned reads cover
all results. Opening `stimecmp_inv` is scoped to its one read node and
closes there. Do not recover the 178-cell premise by duplicating source
ownership or discarding writable cells. Existing `EventWP`/`EventPlan`
proofs stay unchanged and remain useful pure sequencing references.

Every instruction plan is over the generated `run_hart_active`, `try_step`
and both `cycle tick` alternatives, including mixed-width fetch,
compressed decode, default nextPC, restart reservation clearing,
retirement, clock, callbacks, and actual dependent V1 memory requests.
The native fold permits all other actual machine steps and handles power
death through the existing dead-thread rules. It never turns the 14
instructions, or even one instruction, into one atomic memory step.

Recommended order: (1) exact context physical gates and stack algebra;
(2) explicit off SIE/status/cycle resource partition with constructor and
agreement laws; (3) TOR supervisor grants and Bare fetched cycles as an
explicit intermediate; (4) fractional footprint fold and KT1
translation/fetch resource implementation; (5) the two stack accesses,
14-instruction composition and JAL-call wrapper at both tiers. Artifact
image/decode work runs independently. Completion of an earlier item does
not establish the final function interface.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
