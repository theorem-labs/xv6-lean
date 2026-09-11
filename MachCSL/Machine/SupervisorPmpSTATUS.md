# Actual supervisor TOR-entry-0 PMP grant

`SupervisorPmp{Defs,Proofs,Plan}.lean` implements the approved boundary in `docs/design/supervisor-pmp-boundary.md`. `check_ram_plan` proves an `EventWP.Returns` plan for the actual generated `pmpCheck (Physaddr address) width access Supervisor`: the result is `none` and the complete dependent register file is unchanged. It takes the explicit `TorRam` configuration, positive width, RAM containment and a checked `Supported` access constructor. No translation or state-preservation callback occurs in the theorem.

`TorRam` contains exactly the source entry-0 TOR, positive unsigned upper word, R/W/X and RAM-coverage facts. Multiplication of the unsigned upper word by four is unbounded natural arithmetic, matching the nonnegative source integer expression; it is not a wrapping machine shift. Entry 0's L bit and irrelevant bits, every later configuration/address entry, and all unrelated registers are arbitrary. `SourceConfig` adds the surrounding `mseccfg = 0` and Supervisor current-privilege facts. The core PMP path reads neither register and takes privilege explicitly; `source_check_ram_plan` retains the source wrapper without inventing read events.

The access family is exactly instruction fetch, page-table-entry load, scalar data load and scalar data store. `fetch_plan` and `pte_load_plan` expose the source's two principal grants. The source configuration carries all three permission bits even though each checked access consumes only its relevant bit. No arbitrary-access theorem silently bypasses the generated internal-error branches for malformed reserved/atomic payloads.

The checked execution reads `pmpcfg_n` for entry 0, then reads `pmpcfg_n` again and `pmpaddr_n` inside `pmpReadAddrReg 0`. The previous address is literal zero. The match and permission checks are pure. `first_exit` proves the actual inclusive loop's first iteration returns through its `SailME` error/early-return channel; `pmpCheck` catches this as `none`. No later entry, memory event or write is included. The fixed generated platform has 16 checked entries and grain zero, with 64-element register vectors.

`read_address_plan` proves the actual grain-zero raw-address read for arbitrary configuration bits and every natural index, using the generated total `getElem!` operation. The main plan uses only the in-bounds index 0; no correspondence claim about negative Rocq indices or out-of-range source calls is made. `range_match` works for the generated natural-number range carrier. `unsigned_positive` explicitly relates the source unsigned comparison to natural positivity; `width_bound` and `width_unsigned` derive faithful 64-bit width conversion from RAM fit. Zero width is excluded as in the source RAM helper. The lower RAM-bound premise remains in the public contract, although positivity and the upper fit already suffice for this TOR interval beginning at zero.

Source mapping at pinned `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

- `iris/SmodePte.v:31–55`, `pmp_config` / introduction: `TorRam` and the surrounding `SourceConfig` distinction. The two native register ownership resources are not defined by this pure configuration predicate; that source ownership packaging remains a later layer. The unused source `root_ppn` index is not given invented semantic dependence.
- `SmodePte.v:57–84`, `exec_pmpMatchAddr_TOR_match` / `exec_pmpReadAddrReg_val`: `match_tor_plan` specializes the previous bound to zero; `read_address_plan` preserves the two actual reads.
- `SmodePte.v:86–163`, supervisor fetch/PTE-load grants: `check_ram_plan`, `fetch_plan` and `pte_load_plan`, with the actual first-iteration early return.
- `SmodePte.v:299–326`, full range and RAM matching: `range_match`, `ram_range` and the proved width conversion.
- Generated `LeanPaperStock/PmpRegs.lean:281–300` and `PmpControl.lean:211–354`: the actual operational definitions used in the proof, without model edits.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SupervisorPmpPlan` passes all 396 jobs; the final plan module checks in 977 ms. A fresh physical-origin audit checks all 70 declarations in the three modules, including private helpers and full opaque-body/type/inductive-constructor dependency traversal (`info.value? (allowOpaque := true)`). There are zero root exclusions. Only `propext`, `Classical.choice` and `Quot.sound` occur, with no unsafe or partial semantic dependency, new axiom, `sorry` or native decision procedure. Evidence: `/tmp/xv6-lean-research/SupervisorPmpAudit.lean`, `supervisor-pmp-audit.log` and `supervisor-pmp-build.log`.

The complete source `SmodePte.v` was read before design. This is the actual PMP grant subprogram under explicit configuration, ready for later partial-register ownership and supervisor fetch/PTE composition. It does not construct TOR configuration from xv6 startup, prove translation/PMA/PTE consistency, allocate ownership, or establish a supervisor instruction WP or `mycpu` correctness. No new ghost camera or registry slot is introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
