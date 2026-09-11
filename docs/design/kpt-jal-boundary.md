# Actual shared-Sv39 JAL caller cycle

This is the implemented and audited native KptJal boundary. All approved
contracts are proved; the final native Link has no component-WP input. The purpose is the actual
JAL x1 instruction needed before the source callable mycpu theorem, with
an arbitrary virtual PC and arbitrary 21-bit immediate. It does not assume
or call the old Machine-mode JAL x0,0 loop certificate.

Source pin: xv6iris arxiv-v1
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. Read WpSconfCtl.v237–281,
ProofMycpu.v's complete final JAL-callable wrapper, and all of SpecMycpu.v.
Read the actual generated execute_JAL, jump_to, encdec_forwards JAL arm,
encdec_backwards prefix/JAL arm, ext_decode, register access functions and
existing full generated fetch/cycle plans. Existing KptFetch and the newly
implemented MycpuKptCycle supply the source packet/translation conventions.

## Code and immediate boundary

The instruction is JAL (imm, Regidx 1). Its encoder explicitly concatenates
bits [20], [10:1], [11], [19:12], rd=1 and opcode=0x6f in the actual generated
encoder's order. All concatenations use BitVec.append with explicit widths.
`code` is the existing native KptFetch.instrBytes at P for F_Base encoding.
It owns the complete four-byte virtual RX/pristine window and contains the
source two-alignment requirement. It is not an input decoder certificate,
physical read value or successful fetch assertion.

An odd immediate is not encodable as that exact JAL. The native active/cycle
rules do not add an independent immediate restriction: they receive the
source target-even premise, and derive immediate bit zero from it together
with P's two-alignment obtained from code ownership. The pure decoder and
encoder laws explicitly require this derived Encodable condition. Thus
encoding does not silently replace an odd requested immediate by a different
decoded instruction. The body-only rule describes actual execution and needs
only its actual even-target precondition, not fetch encodability.

P is general. At a four-aligned PC the actual fetch uses its full word. At a
merely two-aligned PC it makes two halfword fetches. In particular page offset
4094 can use two independent PPNs. All KptFetch.guardChunks path witnesses,
miss/A-D branch facts, event guards, view receipts and exact reservation
updates remain in place. No single-page, identity-PPN, cached-word or
translation-success premise is introduced.

## Exact state and resource effects

Capacity, shares and the fifty-cell packet are the existing
MycpuRegimeShell definitions. SATP/TLB/PMP vectors remain solely inside its
separate folded shared-KPT residue. Config is the existing source-valued
MycpuKptCycle.Config, including actual pmaBoot, Supervisor, active hart,
ELP zero, literal MISA/MENVCFG, delegated interrupts and HTIF-none. Native
msOwn/off supplies SIE=0 and the relevant MsFacts. There is no new camera.

Actual JAL first reads nextPC as the link address, then PC, runs jump_to,
checks its result and writes x1 only on success. The body contract therefore
requires the actual prewritten nextPC=P+4. It returns RA=P+4 and
nextPC=P+sign_extend imm. The pure raw factor keeps the unsuccessful jump
branch intact. The body resource proof preserves the eager MISA read in
jump_to and uses the actual generated program, not a mathematical assignment
substitute. Actual active decode/landing/setNextPC establishes the body's
link-address premise internally.

All other GPRs, including actual SP and TP, are unchanged; the arbitrary
caller frame can hold the fixed stack pair, full kernel_text or other native
resources. The same running context is explicitly retained. The active
boundary returns updated packet, coherent residue, original JAL code,
fetch-derived reservation, all receipts and frame. The cycle boundary adds
actual retirement, optional clocks for arbitrary input tick, and the genuine
restart to reservation none. Its Completed relation allows every accepted
clock successor. Its only final WP input is the guarded next actual cycle.

## Completed contract inventory and validation

Seventeen pure contracts cover encoder/non-RVC/immediate geometry, actual
owned decoder/prepare/body plans, raw execution factor, prepared-entry and
write-composition equalities, exact RA and other-register effects, zero,
configuration preservation and completed PC. Three resource contracts cover
code persistence, owned alignment extraction and construction from a real
virtual four-byte window. Four native contracts cover full fetch, body,
active and cycle. The exported final native Spec internally supplies each
program proof; no fetch/body/decoder WP or success oracle is a caller input.

The ten modules prove generic bitfield/decoder facts, exact fifty-cell
register plans and native resource folds, the general full-fetch packet
wrapper, and active/shell-cycle composition. The final Link build passed
1,122 jobs. Strict audit covered all 166 physical declarations, private/generated
included, through types, opaque values and datatype constructors: standard
three axioms only, zero exclusions and no unsafe/partial/Initial dependency.
Fifteen kernel boundary checks cover negative and odd immediates, explicit
encodings, halfword alignment, page crossing and unchanged SP/TP. The generic
decoder's clean certificate build took 1,062 seconds (about 157 MiB olean);
subsequent preparation/active/cycle/Link proofs each took 1–2 seconds.
Evidence and exact frozen hashes are listed in KptJalSTATUS.md.

The parent owns eventual composition with the complete mycpu function.
That wrapper must establish target=actual mycpu entry and combine the JAL's
RA update with the callee result/callee-saved contract. This checkpoint does
not claim that wrapper, source capability/entry allocation, source boot
reachability or whole-system closure. No existing frozen family or umbrella
is edited. The ten owned modules are enumerated in KptJalSTATUS.md; separate source
capability adapters belong to the coordinator and other agent.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
