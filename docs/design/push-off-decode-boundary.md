# Actual push_off decoder and compressed expansion certificates

The completed PushOffDecode prefix ties the frozen24 PushOffCode rows to
actual ext_decode_compressed/ext_decode calls, then proves actual execute
returns ExecuteAs of the source normalized AST for all nineteen compressed
rows. For the five base rows it proves decoded=normalized, without executing
that instruction body. No fetch, CSR execution, memory event or function
WP is part of this component.

The six Spec fields are footprint uniqueness, source-constant configuration,
actual finite decoder plan, compressed execute equality, its finite pure
plan, and base normalization equality. The decoded and normalized tables
are imported unchanged. The program dispatches on the same compressed
classification as the existing source byte family.

The row-dependent owned footprint is one arbitrary fractional misa cell
for compressed rows, and fractional cur_privilege/menvcfg for base rows.
Config specializes misa to the actual source HardwareConfig.misaC
0x800000000014112d; the supervisor branch uses actual privilege Supervisor
and source Sconf.menvcfgS=0xa000000000000000. All unrelated fields remain
arbitrary. The compressed source kd lemmas often require only misa.C=1;
this first component explicitly uses the stronger already-source-owned
hardware value, as MycpuDecode does. It does not claim that weaker C-only
parameter theorem has been reproduced. Base rows do not acquire an
unnecessary misa input merely because the source decode bridge uses one.

The native plan retains every actual read, including repeated eager
extension checks. The footprint is a set of owned cells, not a proposed
read trace. Generated PlatformConfig.currentlyEnabled Ext_Zca reads misa
through Ext_C; base decode checks preceding Zihintpause and Zicfilp arms,
with actual Supervisor get_xLPE reading menvcfg. Source MENVCFG leaves
LPE false while preserving its nonzero STCE/PBMTE bits. No Machine or zero
configuration substitutes for it.

Implemented proof organization (all six approved contracts unchanged):

- Reuse KptJal.decode_factor for the three JAL-x1 words, with their existing
  exact encoder equalities and even immediates. Prove the resulting small
  two-register extension prefix at this footprint, avoiding the much
  stronger unrelated full-cycle KptJal.Config.
- Reuse the existing identical MycpuDecode C.JR certificate and reuse the
  repeated C.LW row. For remaining finite words, make individually named
  ordinary kernel conversion certificates with snapshotPlanRun and a
  read oracle that always returns none. Existing MycpuActive snapshot
  soundness is private; a local structural proof can transfer these
  certificates to RegisterPlan without broadening its API. Missing snapshot
  registers, writes, errors and all memory events are rejected by the
  evaluator. Public decode has no evaluator-success or Covers premise.
- Prove compressed expansion by the actual generated execute branch and
  exact immediate arithmetic, preserving one ExecuteAs redirection.
  Do not execute the normalized body to fabricate a successful result.

The source is CodePushOff.v in full and its referenced KernelDecode shards;
notably KernelDecode00:60–69 (C.LW/ExecuteAs), KernelDecode17:365–368 (CSR),
KernelDecode22:240 (SRLI). Generated DecodeExt:204–208 is the actual wrapper;
InstsEnd encdec_compressed_backwards and encdec_backwards are the selected
semantics. Source pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

No existing owner module, AST table or umbrella is edited. The complete six-module build passes1,128 jobs. The strict owner audit
covers all83 physical declarations and their full types, opaque bodies
and constructor dependencies: standard three axioms only, no unsafe/partial
dependency, zero exclusions. Final independent coordinator review pending.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
