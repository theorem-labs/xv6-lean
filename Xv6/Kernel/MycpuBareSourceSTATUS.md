# Source identity/Bare mycpu branch

FROZEN: all six pure, six resource and one native function contract are
proved in seven modules: Defs, Spec, Pure, Resources, Entry, Proofs and
Link. `nativePureSpec`, `nativeResourceSpec`, `nativeSpec` and `registrySpec`
are actual constructors; no component-interface premise remains.

Input is the actual identity-tier Bare arm yielded by source packet
opening, plus identity kernel text and an explicit same-hart boot-PMA
cell. Identity alone does not force Bare. The future dispatcher must also
handle identity-tier KPT.

The adapter obtains three actual owned SATP/PMP cells from the
Bare slot and joins them to the fifty-cell source packet. It derives the
existing MycpuOff configuration, physical code span and physical save
words internally. Mapping closing wands restore virtual/context stack
words with their changed values/timestamps and the full original stack
count. All source pending/stvec, timer, tier, hardware, bit ties, off
token, GPR and literal frame resources are retained. No TLB cell, caller
physical-word premise, body WP or execution-success oracle is introduced.

The only public WP premise is the actual returned-cycle continuation.
Implementation reuses the already proved fourteen-cycle Bare function.
Source/general-PMA/boot-entry inhabitation and the complete tier dispatcher
remain separate.

Design/source mapping: `docs/design/mycpu-bare-source-boundary.md`.
Final native build passed 1,031 jobs. Entry proof 1.7 s, function proof
1.4 s, Link 1.1 s. Fresh strict audit: all 120 declarations in seven
physical modules, full type/opaque-body/constructor cones, standard three
axioms only, no unsafe/partial dependency and zero exclusions.
Logs under `/tmp/xv6-lean-research`: `mycpu-bare-source-native4.log`,
`mycpu-bare-source-audit.log`; audit script `MycpuBareSourceAudit.lean`.
The text-offset binder was corrected to explicit Nat during implementation;
the certified window remains exactly the intended 34 actual source bytes.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
