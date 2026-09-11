# Actual mycpu stack bodies over shared Sv39

Status: all fourteen pure and two native contracts are implemented and
kernel checked. No whole-function or instruction-cycle theorem is declared.
The pinned source is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; generated Sail
model pin is `23dcf8fd923eb8a1958795393d2975632aa940b2`.

## Source and exact programs

I read the existing MycpuMemory definitions, specifications, full prefix/suffix
proofs and native folds; the generated SP-relative compressed redirects,
LOAD/STORE bodies and VmemUtils wrappers; and the source caller/save/restore
and compressed memory leaf contracts.

| Image index | Source location relative to mycpu | Actual body | Virtual address and effect |
|---|---|---|---|
| 1 | +0x02 | C_SDSP(1, x1) → STORE(8, x1, x2, 8) | SP+8 receives RA. |
| 2 | +0x04 | C_SDSP(0, x8) → STORE(0, x8, x2, 8) | SP receives S0. |
| 10 | +0x18 | C_LDSP(1, x1) → LOAD(8, x2, x1, false, 8) | RA receives the SP+8 word. |
| 11 | +0x1a | C_LDSP(0, x8) → LOAD(0, x2, x8, false, 8) | S0 receives the SP word. |

The actual four instructions are C.SDSP/C.LDSP. C.SD/C.LD were read as the
related general register forms; they are not substituted for the image's
SP-relative instructions. `MycpuDecode` already identifies the four bytes and
normalized instructions. `MycpuKptMemory.body` reuses the actual existing
single-ExecuteAs body definitions, not a copied executable surrogate.

Exact generated references are `InstsEnd.lean:16990–16998,17449–17458`,
the redirects at `17657–17665,17731–17739`,
`AddrChecks.lean:217–220`, and `VmemUtils.lean:429–463`. Source contracts are
`WpSconfMem.v:3656–3682,3708–3745`; the caller uses them at
`ProofMycpu.v:105–137,229–254`. The source stack frame comes from the preceding
sixteen-byte push; its two saved addresses are entrySP−8 and entrySP−16.

## Ownership and assumptions

The public input is the existing `MycpuRegimeShell.resources` packet at
`.kpt N root`: the same 50 common keys, full pinned software GPR map, native
mstatus/SIE/SRET ownership, and the separately folded four-cell source KPT
residue. The seven borrowed instruction cells are:

- mstatus, privilege, PMA, HTIF and MENVCFG, exactly `KptMemory`'s five
  auxiliary cells;
- full SP and the selected full RA/S0 cell.

The explicit remainder contains 43 keys. It excludes none of the GPRs merely
because the instruction does not mention them. SATP/TLB/PMPcfg/PMPaddr never
appear in the seven-cell or common-register footprint; their only ownership
is in the native residue. No second packet or paired memory footprint is input.
This agrees with the independently owned KptFetch seven-cell interface:
its PC/MISA replace these SP/data operands, sharing the same five auxiliaries
at successive program boundaries rather than simultaneously duplicating them.

`Config control` states the remaining real owned hardware facts: Supervisor,
PMA boot list, HTIF none, disabled MENVCFG pointer masking and ADUE=1. The
source literal MENVCFG_S supplies the last two facts. MPRV=0, MXR=0 and SXL=2
are derived from the packet's actual native `MsFacts`; they are not added
as public premises. Neither SIE nor TP is supplied as an unbacked pure fact.

The datum is an actual `KernelDatum.word`, with its mapping, tier, positive
canonical address, physical RAM, timestamp/context and alignment resources.
Stores require full word ownership; loads permit arbitrary actual fractions.
There is no physical-word input, no global stack no-wrap hypothesis, no
pristine-old-data requirement and no translation/read-success premise.

## Concrete result and guards

Stores preserve the complete software register map. Loads update exactly
index 1 or 8 with the owned virtual word's value. The same control file is
returned: PC, nextPC, counters and every other control remain physically
owned at their original values. The updated GPR map is constructed by
`HartTp.set`; no unowned projection of a synthetic posttranslation full
register file is used. SP and both slot addresses remain unchanged.

The native postcondition returns the complete packet with that map, the
own-context token, the virtual word (new value for a store), exact reservation
result, all translation receipts, the data-event view receipt and the literal
caller frame. The KPT residue contains the actual refreshed coherent TLB.
Loads preserve the **posttranslation** reservation; it may differ from the
initial reservation after an exclusive A/D reread. Ordinary stores return
none and preserve the posttranslation CPU view as established by KptMemory.

`guards` reproduces the exact KptMemory hit versus three-read-miss nesting and
the branch-specific zero/one/two A/D events. The ordinary data event contributes
the innermost guard. `CompletedFacts` are obtained inside the chosen branch
from native translation, not assumed at entry. The only WP premise is the
genuine continuation after the instruction has returned Retire_Success with
the restored actual resources.

The raw factors quantify arbitrary virtual-memory results. STORE's Ok false
arm really returns Retire_Success in this generated model; the factor retains
that arm, while native ordinary RAM ownership proves the actual Ok true
response. Both LOAD and STORE return Err error verbatim. The underlying
memory/translation exception programs remain in KptMemory's exact factors;
no trap-handler WP or software memory-safety callback is supplied here.

## Two-word convenience contract

`pair` owns both full virtual slots at current SP+8 and SP. `Spec.pair` threads
both through any of the four actual bodies and returns the updated pair:
store replaces only the selected word, load preserves both. A literal extra
frame can carry the untouched `KernelStack.own` remainder, timer capability,
text and other source resources. This rule is proved from the native single-word rule and separation;
no caller-provided preservation callback is required. The preceding/following actual SP instructions and full StackOwn
push/pop composition are outside this bounded layer.

## Completed implementation and remaining composition

Eight modules implement this boundary: Defs, Spec, Pure, Factor, Resources,
Rules, Proofs and Link. `nativePureSpec` constructs all fourteen pure fields;
`nativeSpec` and `registrySpec` construct both native WPs. The same existing
machine, supervisor-bit and KPT capacities are reused without new slots.

The final build passed 1,056 jobs (Proofs 1.5 s, Link 875 ms). A fresh audit of
all 178 declarations by physical module origin traversed complete types,
opaque theorem/definition bodies and inductive constructors. Only propext,
Classical.choice and Quot.sound occur; no unsafe/partial dependency or
exclusion was needed.

The exact raw factors are proved against generated programs by free-tree
induction, preserving every result and event. The native fold opens one
seven-cell packet, applies actual KptMemory translation/data rules, executes
the generated load-target write when required and reconstructs all fifty
register cells plus the original bit resources and evolved KPT residue.
The two-slot rule frames and restores the unselected virtual word.

Actual fetch, dispatch, retirement, full source capability assembly and the
complete mycpu function remain separate tasks. The genuine final
continuation remains a WP premise, as required for compositional body rules.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
