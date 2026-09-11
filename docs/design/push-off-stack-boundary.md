# push_off stack body boundary

The fifteen-module native implementation is frozen and built in1,121 jobs.
The approved PushOffStackDefs/Spec are unchanged: seventeen pure, two
resource and one native contract are all constructed by the final Link. Source is
pinned at xv6iris fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

CodePushOff.v:51–61 supplies three C.SDSP expansions at source indices
1/2/3 (+0x02/+0x04/+0x06); lines 106–116 supply the C.LDSP restorations at
14/15/16 (+0x22/+0x24/+0x26). They use RA/x1 at current SP+24, S0/x8 at
SP+16, and S1/x9 at SP+8. ProofPushOff.v:650–690 executes the three saves,
and 400–480 restores the registers and rebuilds the four-word frame. Its
fourth word is the untouched gap at current SP. The prologue lowers SP by
32, so the saved addresses are exactly entrySP−8, entrySP−16 and entrySP−24.
All addresses use the source modular BitVec64 arithmetic. No global stack
no-wrap premise is added. The actual virtual-word predicate supplies each
word's alignment, mapping claims, positive-address and physical-RAM facts.

This family starts at execute(PushOffCode.normalized(index kind slot)).
The separate PushOffDecode family proves the compressed decoder/ExecuteAs
boundary. The new factors select actual generated execute_STORE/LOAD with
width8, false unsigned flag on LOAD and immediate24/16/8. Stores read the
source register before SP; loads read SP before translation and write the
actual returned word to the selected nonzero GPR. The exact native programs
include transform_effective_address and actual vmem_read_addr/write_addr.
STORE's raw Ok false tail remains Retire_Success and errors remain the
original execution error; native resources establish the actual successful
response internally. LOAD errors likewise remain verbatim.

Reusable native dependencies are KptMemory (full source virtual/context
word to actual transformed Sv39 memory operation), SupervisorAddress
(actual effective-address transformation), SupervisorBareRead/Write
(actual Bare virtual operations), KernelDatumWord (owned virtual to physical
word and a value-polymorphic closing wand), and the existing common
MycpuRegimeShell fifty-cell register/bit/translation packet. The old
MycpuMemory and MycpuKptMemory instruction wrappers fix both the saved
register set and offsets to two mycpu words; their final body rules cannot
be instantiated for S1 or offsets24/16. This new bounded layer supplies
those six concrete factors, the GPR update lemmas, and native packet
partition/restoration without altering either frozen family.

Seven common cells are borrowed: mstatus, privilege, PMA, HTIF, MENVCFG,
SP and the selected saved register. The other43 cells and native bit/x0
resources remain framed. In KPT, the exact existing residue owns SATP,
TLB and both PMP vectors, and is folded back after translation. In Bare,
the actual existential SATP and two PMP-vector cells are opened from the
owned Bare slot, patched into the symbolic file only at those three keys,
and borrowed together with the seven common cells. Thus Bare uses10 cells
plus43 framed cells. No original unowned SATP/PMP projection becomes a
hardware assumption, and no TLB ownership is fabricated.

The input is the same packet at its actual Regime, an original-tier full
virtual/context word, running context, exact reservation, generation
certificate and literal caller frame. Admits is the existing source
restriction: Bare accepts identity tier, while KPT accepts either tier.
The common Config reuses MycpuKptMemory's Supervisor/boot-PMA/HTIF-none/
PMM-disabled/ADUE1 source facts. Actual msOwn supplies MPRV/MXR/SXL; actual
Bare ownership supplies SATP mode0 and TOR RAM configuration. ADUE1 is a
source-applicable sufficient fact also on Bare, where the proof does not
invent an ADUE read. Identity virtual-word ownership derives the aligned
RAM window and returns a closing wand retaining its original mapping
claims. This wand accepts any actually returned physical word and its
updated timestamps; it is proved internally, not supplied by the caller.

Bare contributes exactly one data-event guard, preserving incoming rr for
loads and returning none after successful ordinary stores. Its transform
and memory prefixes retain the actual22 load or29 store register reads.
KPT retains the full native hit/miss and A/D branch guards, CompletedFacts
inside the observed branch, its actual translation-dependent reservation,
and all translation receipts, followed by one data-event guard. Both
regimes return the selected-view receipt, actual updated virtual word,
running context, same original packet/control/regime, updated GPR map and
literal frame. Native event rules cover blocked retry and permitted read
views internally. No success, translation WP or memory WP oracle is a
public input; only the genuine final execution-result continuation is.

The resource checkpoint also gives the source four-word stack equivalence:
KernelStack.own at entrySP depth4 is three existential saved words plus
one existential gap at paStk(entrySP,4). It is reversible and accepts the
new saved contents, so all original-tier mapping/context ownership funds
restoration. An arbitrary deeper remainder can stay in the literal frame.
The one-slot body rule leaves the other two saves and gap there. StackReady
only relates current SP to the fixed entrySP−32 anchor; loads preserve SP
and therefore every save address. A future cycle/function layer must keep
this anchor across scalar SP changes rather than silently reindexing it.

There are seventeen pure contracts, two native resource contracts and
one native body contract. The current common packet is disabled-SIE:
this boundary does not prove the enabled-SIE prologue, migration, full
source capability restoration, fetch/decode/cycle execution, a complete
push_off function, or source entry/boot inhabitation. Those remain separate
integration obligations. No new cameras or existing-family/umbrella edits.

The implementation's pure/body factor, common packet resources, KPT guard
fold, source word/stack algebra and Bare owned-slot adapter are separate
modules. Native KPT helpers also support fractional load words internally;
the approved public rule specializes to full saved words. The final
original-regime dispatcher supplies both actual native proofs without a
component WP argument.

Validation passed: strict audit of all284 physical-origin declarations in
all15 modules, explicitly including private-name lookup, all declaration
types, opaque bodies and constructors. Only propext, Classical.choice and
Quot.sound occur, with zero unsafe/partial dependencies and zero exclusions.
Twenty-four checks cover all six generated-body equations, actual store
factors, all three arbitrary modular anchored addresses, numeric wrap cases,
S1 destination/non-destination/SP behavior, actual false/error residuals,
Bare reservation results and the ten-cell count. Evidence and frozen hashes
are recorded in PushOffStackSTATUS.md; no full source input inhabitation
claim follows from this validation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
