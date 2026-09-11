# Complete Bare mycpu function chaining

This approved design is now implemented by `Xv6/Kernel/MycpuBare{Defs,Spec,Geometry,State,Reference,Config,Proofs,Link}.lean`; see MycpuBareSTATUS.md for the checked contracts, validation and remaining source boundaries. The design below records the agreed scope. It composes fourteen actual `MachCSL.Machine.cycle` rules; no new executable function interpreter or generated standalone `Functions.loop` is introduced. Existing Cycle, RegisterSequence, CalleeSaved, stack and context files remain frozen. Source KPT function correctness remains a separate target.

## Source contract and scope

The complete pinned `ProofMycpu.v` and `SpecMycpu.v` were read, including the jal-callable wrapper. The core source theorem is tier-polymorphic, takes `sie_cap_gpr kt m0 n false p`, kernel_text and entry pc_is, and returns the same capability count, return pc_is, all thirteen callee-saved values, and `a0 = mycpu_ret (rget m0 tp)`. Its two stack slots come from the capability's free stack, then rejoin it. Interrupts must be disabled because TP is read mid-function and the source must prevent migration.

The proposed Bare result proves the complete actual fourteen-instruction body and return boundary using the already native physical resources. It does not identify these resources with the source SIE/sconf capability or tier-polymorphic virtual stack. It also does not include the caller's preceding JAL instruction. The returned continuation is an ordinary WP of the next actual cycle at the proved return PC; proving arbitrary code at that PC remains the caller's obligation.

## One initial configuration

Define a pure `SupervisorConfig entry` consisting only of register facts supported by the existing 28-cell footprint:

- Actual current privilege is Supervisor, hart-state is HART_ACTIVE, and elp is zero.
- Full source MISA value `0x800000000014112d` and MENVCFG value `0xa000000000000000` support all checked decodes and data/return wrappers.
- MSTATUS has SIE false, MPRV zero, MXR zero and SXL=2. Other status fields are unrestricted. No full reset-status value or SIE-legalization fixpoint is added.
- `mie & ~mideleg = 0`; pending mip and both external interrupt pins remain unrestricted.
- SATP decodes as Bare in RV64; ASID and PPN fields remain unrestricted.
- The source-compatible TOR entry-zero grant, `htif_tohost_base = none`, and the actual board `pma_regions = pmaBoot`.

`EntryConfig` adds `entry.PC = MycpuDecode.address 0`. Initial nextPC and clock/counter values may be arbitrary; setup and preparation perform their actual writes. The additional source sconf ghost half, SIE capability, complete hardware invariant and KPT regime are not asserted. No unowned MSECCFG cell is silently added to the footprint.

All required MycpuCycle.Config, ReadConfig, WriteConfig and Return.Config instances will be derived from this one configuration plus proved phase facts. In particular, full MISA implies C/S, source MENVCFG implies disabled PMM/LPE, and the source MSTATUS facts give actual data effective privilege. A general pure board-PMA lemma will establish matching/grants for aligned RAM windows from pmaBoot; its input is address geometry, not a returned-memory-word or access-success oracle.

Clock changes are confined to mcycle, mtime and mip. None of the configuration facts depends on those values. The supervisor delegation/SIE theorem already handles arbitrary mip and external pins. Prove configuration stability under each actual `Completed` result rather than assuming a particular clock trace or taking one configuration premise per instruction.

## Linear resources and stack geometry

The main bundle remains exactly `MycpuCycle.cells` on 28 unique keys. It already contains full SP and S0, so the caller frame consists of exactly eleven remaining callee-saved keys: x9 and x18–x27. Define a separate `calleeFrame` with independently supplied DFrac shares on those keys. Prove its uniqueness and disjointness from the 28-cell keys; the combined resource has 39 keys. This frame is retained while the existing 28-cell native rules run, then transported to the final symbolic file using the derived preservation facts. No duplicate SP/S0 tokens or ownership of all 180 registers is required.

The actual running context and persistent discarded 34-byte text span are inputs. Two full context words lie at `StackPhysical.paStk entry.SP 1` and `paStk entry.SP 2`, initially with arbitrary scratch values. They are actual byte/timestamp/context resources, not assumptions that future loads return saved values. The first store changes the upper slot to entry.RA; the second changes the lower slot to entry.S0. Both resources are retained through the arithmetic instructions and justify the later all-view loads using the existing native context read rule. They remain owned at function return with those saved values; the old scratch contents are not claimed preserved.

The existing word assertion supplies eight-byte alignment and a RAM assertion for each byte. Extract these pure facts while preserving ownership. For the bounded board RAM interval, aligned base-in-RAM implies the complete eight-byte range is within RAM; prove that arithmetic lemma, then derive the actual PMA/PMP/data-wrapper conditions. Source modular SP subtraction is retained. SP alignment can be derived from either slot's native alignment, and the push/pop identity is modular for every SP. Do not add a 16-byte alignment condition or a global no-wrap SP bound. Native separation already prevents simultaneous writable stack ownership and aliased discarded text ownership; the proof does not assume an immutable-memory oracle.

A source-shaped physical stack corollary may take `StackPhysical.own ... entry.SP n` with `2 ≤ n`, split exactly two words with `frame_two`, frame the remaining n−2 words, and return `own ... entry.SP n` using the existing recombination laws. This still does not assert the virtual-tier or SIE-capability component of source stack ownership.

## Register phases and actual composition

Use a finite pure bookkeeping relation `Phase entry k rs` for k=0,…,14. It fixes the indexed PC (or final return target), the relevant GPR values, and the unchanged control/callee-frame projection; clocks and retirement counters are left to the actual Cycle.Completed relations. Its reference GPR expressions use the frozen MycpuRegisterSequence operations. These expressions are not an executable machine or a premise about an observed load.

Prove phase preservation as consequences of each already checked Cycle family postcondition, for every permitted post-clock register file. The body partition is scalar indices 0,3–9,12; stores 1,2; loads 10,11; return 13. Consecutive PCs use actual two/four instruction widths, including the two base instructions at offsets 14 and 18. AUIPC therefore reads the actual `mycpu+14` PC. The stack values used by load phase proofs are obtained from the two retained native word resources.

The state proof must relate the real composed GPR projection, despite setup/nextPC/retirement/clock writes, to `MycpuRegisterSequence.returned entry`. Reuse its checked callee-saved, saved-RA, return-address and result lemmas only after proving this projection relation; never treat the pure register sequence as a trace certificate. Existing CalleeSaved typed-write/frame laws handle the independent eleven-cell frame.

The native proof composes all fourteen cycles. Each selected current tick and every subsequent nextTick remain arbitrary. Memory and code resources are framed across actual register/clock/restart events. Restart clears reservations, so only the initial arbitrary rr needs accepting; all intermediate and final cycle boundaries own none. The native receipt facts can be affinely discharged after they have served the cycle rule; context ownership itself retains the updated context information. No extra ordering of receipts is assumed.

## Proposed public contract

The core `wp_mycpu` has the following schematic interface, with actual capacity/era/image/fixed-whole-trace arguments explicit in Lean:

```text
EntryConfig entry ->
cert -∗ cells28 entry -∗ calleeFrame entry -∗ running ξ -∗ sharedText -∗
word(paStk entry.SP 1, full, oldRA) -∗
word(paStk entry.SP 2, full, oldS0) -∗ resvFrag rr -∗
(∀ after, ⌜Result entry after⌝ -∗
  cells28 after -∗ calleeFrame after -∗ running ξ -∗ sharedText -∗
  word(paStk entry.SP 1, full, entry.RA) -∗
  word(paStk entry.SP 2, full, entry.S0) -∗ resvFrag none -∗
  ∀ nextTick, WP(hart gen cpu (cycle nextTick))) -∗
WP(hart gen cpu (cycle initialTick)).
```

`Result` includes the final PC and nextPC equal to `retPC entry.RA`, preserved RA, all thirteen callee-saved values, actual A0=`mycpuRet entry.TP`, and preserved SupervisorConfig. It can expose A5 and the unchanged control projection as useful derived facts. It does not falsely fix clock values. The final stack scratch words are the saved entry values, not the arbitrary old contents.

The public continuation is unguarded, matching the source function-CPS style. Internal Cycle rules retain their exact two/three guards; the proof introduces the required laters when composing continuations. Fourteen cycles provide 32 identified fetch/data/restart guard boundaries (ten two-guard register/return cycles and four three-guard memory cycles). No claimed step-count theorem or stronger 32-later public interface is needed for this first function result.

Keep the generic arithmetic result for arbitrary actual owned TP. A separate `wp_mycpu_hart` corollary takes `entry.x4 = BitVec.ofNat 64 cpu.val`, uses the existing `MycpuScalar.valid_hart`, and returns `after.x10.toNat = 0x800123e8 + 128*cpu.val`. The fixed CPU argument, disabled interrupts, and retained fractional TP ownership protect the mid-function read. This is an explicit actual register assumption; the source HartTp invariant is neither assumed allocated nor replaced with a silently hardcoded CPU value.

No final public contract accepts per-step correctness, a caller-supplied trace, fourteen configurations, memory readability, or state-preservation callbacks. The only residual-program obligation is the caller's ordinary next-cycle WP at the proved return boundary. Kernel-checked proof, full physical/type/opaque/constructor audit and independent review are required before any implemented-function claim.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
