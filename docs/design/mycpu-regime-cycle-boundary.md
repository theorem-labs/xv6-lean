# Regime-independent mycpu cycle boundary

Status: all six modules are implemented and frozen. Both proof records are
constructed natively. This remains a cycle-shell interface, not the source
mycpu function theorem.

The source is the paper artifact at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The generated model is pinned at
`23dcf8fd923eb8a1958795393d2975632aa940b2`. No file named `HartSControl.v`
exists in that artifact: the relevant control and cycle boundaries are
`SmodeCore.v`, `WpSconfCtl.v`, `HartMCycle.v`, and `IntrDefs.v`.

## Exact source obligations

| Source | New boundary or remaining obligation |
|---|---|
| `SRegime.v:833–838`, `bare_inv` | Existential full SATP cell, decoded Mode=Bare, and full native source PMP configuration at the unused root index zero. There is deliberately **no TLB cell**. |
| `KptShare.v` residue, reused by `KptResidue` | Full SATP/TLB/PMP-vector ownership, exact rooted SATP facts, current canonical snapshot coherence, shared tree and boot/view credential. |
| `IntrDefs.v:1212–1248`, `strans_inv` | The source additionally owns pending/shot publication state and, in Bare, stvec. Those are not invented by the two concrete physical branches here. |
| `IntrDefs.v:1464–1477,1923–1938` | The source translation regime includes its own residue, tier witnesses, masked translation and slot-access laws. We reuse constructed native KPT operations; we do not replace this record with assumed preservation callbacks. |
| `InstrBytes.v:701–707` | PC and nextPC, source retirement resources, three full clock cells, and the reservation resource. The shell exposes the reservation separately so the actual restart can clear it. |
| `HartMCycle.v:693–715,720–850` | Actual arbitrary-value clock and setup/postlude factoring around `run_hart_active`. Both clock choices, inhibited counters and overflow remain. |
| `MinstretInv.v:341` | The source `minstret_inv` is intentionally `emp`; it does not supply counter ownership. |
| `RiscvFetchExec.v:288–334`, `IntrDefs.v:595–621,649–653` | `hw_config` and `sconf` include more than the registers used here. The packet includes the exact native mstatus/SIE/SRET component and shares for relevant controls; it is not the full source hardware or supervisor capability. |
| `IntrDefs.v:1980–2061` | The disabled SIE arm carries its real ghost eighth. The full capability also includes stack, translation, context, timer and tier witness; enabled arms additionally contain handler/trap/migration resources. |
| `SpecMycpu.v:29–43`, `ProofMycpu.v:1–27` | The eventual function quantifies the tier, requires interrupts disabled and at least two stack slots, and returns the same full capability and ABI facts. The mid-function TP read is tied to the same hart by actual pinned GPR ownership. |
| `WpSconfCtl.v:311–363`, `WpNext.v:55–88` | Actual C.JR/JALR return and the off-only same-hart continuation. No enabled interrupt/migration theorem is supplied by this shell. |

## Single ownership partition

`MycpuRegimeShell.controlFootprint` has 18 keys: PC, nextPC, four retirement
cells, three clock cells, and nine controls (privilege, MISA, MIE, MIDELEG,
MENVCFG, ELP, PMA, HTIF and hart state). One full native `msOwnAt` supplies
mstatus and its three source mirrors. One `HartTp.pinnedFile` supplies all 31
physical GPRs and the software x0 fact. The resulting flattened footprint
contains exactly 50 unique physical keys.

SATP, TLB and both PMP vectors are excluded from all 50 keys. `Regime.bare`
owns the source three translation cells; `Regime.kpt N root` owns the four
through the already-proved shared KPT residue. The totals are 53 and 54,
respectively. No copy of the former Bare 28-cell cycle bundle is an input.

`sourceShares` selects the source discarded MISA/PMA/HTIF/ELP shares and full
privilege/MIE/MIDELEG/MENVCFG/hart shares. The general interface also permits
other actual owned shares. Its remaining source hardware predicates and
registers can be framed; they are not silently manufactured. `bitFrame` keeps
the SIE half, SPP/SPIE ties, all `MsFacts` and the off eighth after extracting
the full mstatus cell.

The pure `entry` overlay is the existing typed GPR overlay. Unlisted fields
in a symbolic file carry no assertion about the physical file. KPT operations
may refresh the actual TLB while returning the same exposed control file;
coherence and the refreshed value stay in the residue. No whole-file equality
with a pretranslation snapshot is required.

## Compiled contract shape

`pureSpec` proves all six layout/setup/completion laws. `nativeSpec` and the
existing-registry `registrySpec` prove all five native laws:

1. Reversible partition into the 50 actual cells, native bit frame, x0 fact
   and the unchanged translation resource.
2. Derive disabled SIE from native bit agreement and the actual TP value from
   the full pinned GPR representation.
3. Execute actual setup and select the active branch, returning ownership at
   `started control` to the **literal**
   `run_hart_active 0 >>= finish tick` WP.
4. Execute actual successful postlude and optional clock, returning a symbolic
   file with the exact `Completed` relation and the same full GPR/software map,
   translation residue and bit ties.
5. Execute that tail and the actual restart: retain an arbitrary old reservation
   until restart, then return none under the real one-event guard and quantify
   the next clock choice universally.

The `start` residual is an explicit conditional composition seam. It is not
an interface pretending to prove fetch or instruction execution. `finish` and
`restart` start from the actual already-returned `Retire_Success` branch;
they do not claim that an arbitrary instruction returns that branch. The
underlying full generated postlude factor retains all other original arms.

All three laws accept a literal native resource frame and return it. A named
`kernelFrame` combines existing own-context, timer capability and virtual
stack ownership. The Bare arm only admits identity-tier stack words; the KPT
arm admits both tiers. This admissibility index is not a substitute for the
source pending/shot tier-publication witness.

## Concrete composition still to discharge

The independently owned `KptFetch` layer uses exactly seven cells: PC, MISA,
and the five `KptAddress` auxiliary controls. They are extracted from this
packet once. Its actual page-crossing translations, A/D events, read guards,
returned reservation and receipts must be threaded before decoding.

`KptMemory` already proves actual transformed virtual eight-byte accesses
from the same five auxiliary cells and source residue, with virtual context
word restoration. The four actual mycpu load/store instruction bodies still
need the regime-aware base/source read and loaded-register-write adapters.
The native register-only scalar and return bodies can be widened to this
footprint. Every body must return the actual result and restored owned cells;
it cannot assert arbitrary full-RF equality after a TLB fill.

The implemented shell runs its register plans over the 18 control cells.
It frames the full GPR ownership, mstatus/SIE/SRET bundle and translation
residue throughout. The actual clock plan returns a symbolic control file
with `Completed`; its mstatus equality reconstructs the original native bit
bundle. This avoids claiming that a separately framed GPR or hidden TLB
has the value of an unrelated symbolic field.

The final 14-cycle theorem must discharge fetch and body seams, preserve the
source branch guards rather than the old Bare fixed-later count, split and
rejoin the virtual two-slot stack with its remainder, and recover the source
callee-saved and returned-a0 facts. Full `hw_config`, the published translation
regime and source `sie_cap_gpr` assembly remain explicit dependencies. No
closed mycpu claim, installed-handler claim, boot allocation or new camera is
part of this checkpoint.

Validation: `tools/lake.py build Xv6.Kernel.MycpuRegimeShellLink` passed 885
jobs (native proof module 1.1 s, Link 968 ms). An independent audit script
selected all 149 declarations by physical origin across the six files, read
their types and full opaque bodies and traversed constructor dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial
dependency or excluded declaration was found. These checks establish this
bounded implementation, not the remaining fetch/body/capability obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
