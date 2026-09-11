# All fourteen mycpu bodies with a fixed save area

This checkpoint combines the completed native MycpuKptRegister and
MycpuKptMemory boundaries. It starts at actual decoded execution and keeps
fetch, retirement, cycle composition and the complete source function
separate. The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; the
generated model pin is `23dcf8fd923eb8a1958795393d2975632aa940b2`.

## Exact dispatch and state transformations

`body i` is the generated `execute (MycpuDecode.decoded i)` followed by the
actual single ExecuteAs selection. `route` exhausts all fourteen indices:
register bodies at 0/3/4/5/6/7/8/9/12/13; stores at 1/2 and loads at 10/11.
The pure contract proves routeIndex(route i)=i and exact body equality with
the corresponding already-proved program. No decode/fetch certificate or
successful body WP is supplied as an input.

Each index computes its exact successor from arbitrary incoming software
GPR values, current control file and the two owned virtual-word contents.
Register cases reuse the typed scalar update or return-only nextPC update;
memory cases preserve controls and update only the loaded GPR, or the
selected stored-word payload. Physical PC remains unchanged during the
body. nextPC remains unchanged except for the actual low-bit-cleared RA
return. AUIPC uses the actual owned PC; the eventual fetch/cycle layer must
establish the intended indexed PC rather than replacing it in this rule.

## Fixed anchor and source frame geometry

The immutable anchor is `entrySP−16`. The pair always owns real virtual
context words at anchor+8 and anchor, equivalently entrySP−8 and entrySP−16.
All arithmetic is modular 64-bit arithmetic; word ownership retains the
source positive/alignment/RAM and mapping resources. No invented global
no-wrap premise is added.

`StackReady` requires current SP=anchor only for the four memory indices.
Register cases accept arbitrary SP and preserve the same anchored word
resources as a literal frame, including across push and pop. This matches
`ProofMycpu.v:90–137,229–282`: the source names the two new save cells after
pushing and joins those same cells after restoring them. It never moves
physical ownership merely by changing the SP value.

Separate pure functions state the source SP schedule: entrySP before index 0,
anchor before indices 1–12, entrySP before index 13. `phaseStep` proves the
actual scalar/memory map update preserves the expected next SP under that
input phase fact. The body WP only needs the weaker memory-specific equality.
No whole-function phase invariant, assumed saved-word equality or fixed
initial callee-register values is introduced.

## Native resources and modal boundary

Every branch owns the same fifty-cell source cycle/GPR packet plus its
folded native KPT residue, running context, the fixed virtual-word pair,
actual reservation fragment and an arbitrary frame. Config is route-specific:
scalar cases need none; return needs the frozen actual return configuration;
memory cases need the frozen actual Supervisor/PMA/HTIF/MENVCFG configuration.
Source mstatus and TP facts remain backed by packet ownership.

`Outcome` is indexed by the selected route, so an impossible register/memory
outcome combination has no inhabitant. Register outcomes preserve rr and
produce no new receipt. Memory outcomes retain the actual shared-translation
outcome and final data-event view, with the exact posttranslation reservation
for loads and cleared reservation for ordinary stores. The full evolved KPT
residue and all translation/data receipts are returned.

`finish` is a genuine returned-body continuation. Register-only bodies use
the existing native register fold's internal event guards. Memory bodies
preserve the full hit/miss and zero/one/two-event A/D nesting, followed by
exactly the ordinary data-event guard. CompletedFacts occur inside their
native branch, not as entry premises. Raw STORE Ok false and LOAD/STORE Err
factors stay explicit; actual native memory ownership derives success.

## Checkpoint scope

Actual Defs/Spec contain thirteen pure and one native contract. The completed
implementation exhausts the route, frames the fixed pair/context/rr through
MycpuKptRegister, or proves the SP-based pair equal to the fixed pair and
invokes MycpuKptMemory. It then rebuilds the common indexed postcondition.
No camera, frozen dependency or registry change is required. The five modules
(Defs, Spec, Pure, Proofs, Link) supply actual `nativePureSpec`, `nativeSpec`
and `registrySpec` constructors. The Link build passed 1,066 jobs; the pure
module checked in 1.6 s and native body fold in 1.4 s. The STATUS records the
full physical declaration audit.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
