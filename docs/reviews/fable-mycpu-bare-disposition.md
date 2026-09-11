# Disposition of Fable seventh review

Fable approves the complete Bare mycpu CPS with no soundness blocker. Its
review was tools-disabled and covered81 frozen source files. Independent
peer and coordinator reviews additionally checked the native composition,
source contracts and the complete dependency cones; their build/audit records
are separate from Fable's review.

The two requirements before claiming a closed Bare gate are tracked explicitly:

- Operational fourteen-cycle witness: in progress in separate
  MycpuBareWitness modules, from an explicit concrete supervisor EntryConfig
  and the actual pinned image. It must include actual memory stores/reloads,
  clock/restart transitions and the final register/stack result. A pure RF
  calculation is insufficient. No boot-path or Iris-resource inhabitation is
  implied by such a configured-machine witness.
- Scope wording: completed in MycpuBareSTATUS. No current allocation theorem
  produces the running context and supervisor EntryConfig register clients.
  The existing shared boot allocator extracts the34-byte code span and retains
  other clients; it does not itself extract the two stack words. The rule is
  image-parametric under resources, with Xv6.Machine.bootImage the intended
  source instantiation. It need not be meaningless for another image satisfying
  those resources. The actual boot setup remains a separate obligation.

The requested pure result check is implemented in MycpuBareResultProofs:
reference_result supplies the self Phase at14 to phase_result. Phase at0
alone would not prove that result. This is separately labeled bookkeeping.

Two recommendations are retained with source corrections. Regime-parametric
cycle/function composition will reuse the chain once actual shared KPT
fetch/data boundaries exist; current Bare files remain stable while that
contract is designed. HartTp is being implemented as the source's full owned
31 physical GPRs plus the x0 fact, pinned at the actual x4 cell. A freely
persistent TP fact cannot replace that ownership or justify migration; the
source does not allocate a separate persistent TP ghost. The off execution
rule and eventual nonduplicating footprint adapter preserve those distinctions.

The preceding JAL call wrapper remains a later composition item. The physical
Bare function is not a full implementation of the source tier/SIE/free-stack
module contract. MENVCFG bit61 is enabled in the source configuration; actual
PTE A/D composition has now been proved and independently audited. All six
whole-xv6 roots and cross-prover semantic correspondence remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
