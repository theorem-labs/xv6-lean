# Supervisor PMP entry-0 boundary: proposed implementation contract

This is a design proposal, not a compiled theorem or a supervisor execution result. The complete 529-line pinned `iris/SmodePte.v` was read before proposing this slice, together with actual generated `PmpRegs.lean` and `PmpControl.lean` and the existing `BootPmp{Defs,Proofs,Plan}` implementation. The upstream baseline is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

## Exact boundary

The next slice should prove an `EventWP.Returns` plan for actual `pmpCheck (Physaddr address) width access Supervisor`, returning `none` and the unchanged complete dependent register file. Entry0 is TOR with R/W/X all set, its raw upper-address word is positive, and its unsigned value multiplied by four covers the RAM upper bound. Every later configuration/address entry, entry0's L bit and other irrelevant configuration bits, and unrelated registers remain arbitrary. This is separate from the existing Machine-privilege, all-OFF reset theorem.

The source mappings are:

- `SmodePte.v:31–55`: `pmp_config` and its introduction lemma. `root_ppn` is an unused index here; the pure PMP predicate need not invent a dependency on it.
- `SmodePte.v:57–84`: TOR matching and raw `pmpReadAddrReg` value.
- `SmodePte.v:86–163`: entry0 fetch and page-table-load grants.
- `SmodePte.v:299–326`: positive-width range matching and RAM coverage.
- The rest of SmodePte contains actual PTE reads, translation-mode and TLB helpers. Those require separate PMA, translation, memory/resource and TLB work and are outside this slice.

Generated functions are `models/riscv/LeanPaperStock/PmpRegs.lean:281–300` and `PmpControl.lean:211–354`. This build fixes `sys_pmp_count = 16` and `sys_pmp_grain = 0`, while the register vectors have 64 entries. The grant must exit at entry0; no condition on the other 15 checked entries or remaining vector entries follows or is needed.

## Proposed files and interfaces

Own only new `MachCSL/Machine/SupervisorPmp{Defs,Proofs,Plan}.lean` and `SupervisorPmpSTATUS.md`. Existing BootPmp files remain frozen. The following signatures specify intended types; they have not yet been compiler-checked.

`SupervisorPmp.Defs` will define `entry0 rs := (rs .pmpcfg_n)[0]` and `upper0 rs := (rs .pmpaddr_n)[0]`, using the actual generated vector representation. `TorRam rs` will contain these source facts:

```lean
pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (entry0 rs)) = .TOR
0 < (upper0 rs).toNat
_get_Pmpcfg_ent_X (entry0 rs) = 1#1
_get_Pmpcfg_ent_W (entry0 rs) = 1#1
_get_Pmpcfg_ent_R (entry0 rs) = 1#1
ramHigh ≤ (upper0 rs).toNat * 4
```

The unsigned positivity field is equivalent to the source's `0 >=u pmpaddr0 = false`; keep an explicit equivalence lemma. Multiplication by four is unbounded natural-number arithmetic, as in the source integer range calculation. It must not be replaced with a wrapping 64-bit shift. RAM is the actual platform interval `[0x80000000, 0x88000000)`.

A source-facing `SourceConfig rs` will pair `TorRam rs` with `rs .mseccfg = 0#64` and `rs .cur_privilege = Supervisor`. These latter facts match the surrounding hardware/supervisor configuration. The lower-level PMP theorem will not need them: actual `pmpCheck` takes privilege explicitly, and the inspected generated PMP path reads neither `mseccfg` nor `cur_privilege`. No artificial read event should be introduced to consume an unused assumption.

For a bounded first access family, define `Supported access` as exactly instruction fetch, page-table-entry load, scalar data load, or scalar data store. This includes both fetch widths, the plain/exclusive PTE read's common PMP access type, and mycpu's stack accesses. The actual permission function has additional valid cases and explicit internal-error cases for malformed reserved/atomic payloads. Therefore no theorem may quantify arbitrary access constructors without a checked supported-case condition. AMO/vector/cache expansion is later work.

The main intended public plan is:

```lean
check_ram_plan
  (reads : EventWP.ReadAllowed) (rs : RegisterFile)
  (config : TorRam rs)
  (address : BitVec 64) (width : Nat)
  (positive : 0 < width)
  (low : ramLow ≤ address.toNat)
  (fits : address.toNat + width ≤ ramHigh)
  (access : MemoryAccessType mem_payload)
  (supported : Supported access) :
  EventWP.Returns reads rs
    (pmpCheck (.Physaddr address) width access .Supervisor) none rs
```

An equally concrete `source_check_ram_plan` will accept `SourceConfig rs` and discharge the TorRam component. Convenience fetch and PTE-load corollaries should use exactly `.InstructionFetch ()` and `.Load .PageTableEntry`. The positive-width and RAM-fit premises derive `width < 2^64`, so the conversion to the model's 64-bit width preserves its value. The generic source helper can separately retain a pure `pmpRangeMatch = PMP_Match` premise; the exported RAM plan must prove that premise from the arithmetic geometry above. Neither interface takes a translation-correctness or state-preservation oracle.

## Proof decomposition and retained events

1. Prove the pure range lemma `begin ≤ address`, `0 < width`, `address + width ≤ end` implies `pmpRangeMatch begin end address width = PMP_Match`. Derive the entry0 RAM instance, including the actual width conversion. Zero width is excluded exactly as in the source helper; no unchecked source quantifier comment is treated as a Lean hypothesis.
2. Prove actual `pmpReadAddrReg n` returns the raw vector value at grain0, retaining its configuration-vector read followed by its address-vector read. No OFF assumption is used. A bounded index is sufficient for this slice; the actual call is index0.
3. Prove the actual `pmpMatchAddr` TOR branch from enum-TOR, increasing unsigned bounds and the pure full-range result. At entry0 the previous raw address is the literal zero without a register read.
4. Prove actual `pmpCheckRWX` returns true for each supported access, using the relevant entry0 permission fields. Preserve the entry's L and reserved bits. Fetch needs X, loads R and stores W; the source-facing bundle retains all three.
5. Unfold only the first iteration of the actual inclusive `IntRange` loop and its `SailME` early-return handling. Pay these actual register events in order: read `pmpcfg_n` for entry0, read `pmpcfg_n` again inside `pmpReadAddrReg 0`, then read `pmpaddr_n`. After the full TOR match and true permission result, the model immediately returns `none`. Later entries are not read. No memory event, register write or platform fallback is asserted.
6. Build with the existing native `EventWP.Returns.bind` / read/pure combinators. Small local checked Except/loop helpers may be needed because BootPmpPlan's helpers are private. The plan can later be embedded in EventPlan or its native WP fold without allocating a new camera or adding a resource callback.

The existing `BootPmp` reset proofs are useful evidence for vector indexing and actual loop structure, but their `Off` premise and `.Machine` grant are not a replacement for this supervisor proof. No boot-to-TOR configuration construction is claimed in this slice: the later actual xv6 startup proof must produce TorRam/SourceConfig from its register writes.

## Validation and boundaries

Before freeze, compile all new modules with `tools/lake.py`; audit every physical declaration and its complete opaque-body/type/constructor dependency cone with `info.value? (allowOpaque := true)`, allowing only `propext`, `Classical.choice` and `Quot.sound`. No new axioms, `sorry`, native decision procedures, generated-model edits or unsupported event assumptions are permitted. Review will check the actual early return, raw upper-bound arithmetic, irrelevant-field freedom and exact read sequence.

This slice does not prove address translation, PMP configuration ownership, checked RAM reads, page-table consistency, supervisor dispatch, an instruction WP, or mycpu correctness. It proves the actual PMP grant subprogram under explicit source configuration and access geometry, ready for those later layers.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
