# Native direct-slot supervisor A/D update

Frozen eight modules: SupervisorPteADDefs/Spec/FactorDefs/Plan/Pure/Slots/
Proofs/Link. The complete Spec.update is implemented by wp_update and
exported as nativeSpec. Coordinator source/signature review approved the
branch-indexed contract before implementation. No new camera or registry
slot is used.

Source: xv6iris fa7f0a01c4b40489fac8ad303f079c2dfc7a1476,
PtTreeAdue.v:1650–1818,1852–2045 and HartSKpt.v:730–910; actual generated
Vmem.update_and_write_pte:325–360 and the pinned Svadu/Svade definitions.
The public program is update_and_write_pte 39 at level 0, Supervisor, over a
concrete KptLeaf RX/RW leaf. PPN and physical/cached A/D bits are arbitrary;
Supported/Allows are the exact four source access cases. No ADUE = true,
pre-set A/D, successful-response, callee-WP or state-preservation premise is
accepted. Actual checked RAM/PMA/TOR/HTIF configuration is explicit.

The five owned fractional cells are PMA, PMP config/address, HTIF and
menvcfg. Every cell is restored. The separate actual KptLeaf validator
retains its seven universally quantified eager register reads, with no
additional cells or fixed hardware values. Its native PlanSpec is supplied
internally by the independently reviewed implementation.

The exact branches are all implemented:

- Cached update = None is pure Ok (None, unit), with no free event, unchanged
  physical slot and incoming reservation. cached_program exposes this law.
- Cached update = Some and ADUE = false perform the real gate register read,
  then return NeedsUpdate with the same slot and reservation.
- ADUE = true exclusively rereads the real physical leaf, checks it with the
  actual generated validator, and recomputes update_PTE_Bits. update = None
  returns that physical leaf and retains its exact installed snapshot and
  read view receipt.
- update = Some performs the actual conditional PTE write, clears the local
  reservation on success, and returns the new full slot plus a positive
  authored timestamp, exact logElem(time−1) and matching view receipt.

BranchFacts are derived from actual pure update equations and the actual
ADUE result, not assumed as a transition oracle. The genuine final
continuation receives zero, one or two memory guards according to the
branch; native register subevents are folded separately. Blocked exclusive
rereads retain the native clear-and-retry behavior; blocked writes retain
the same state/snapshot and retry. No eventual completion is claimed.

program_eq factors the actual tree before native rules are applied and
retains all reread/check/write error responses. In particular write Ok false
is the original internal_error, not a walk retry; write_false exposes the
exact residual. Actual native owned-resource proofs discharge the success
responses rather than deleting those source branches.

collect_floors/slot_open expose the original eight per-byte floors and
publication anchors by finite separating existential collection. The full
pinned write updates the existing heap metadata/TSO resources through its
proved native layer. slot_close reattaches exactly the original bounds and
anchors to the written window. update_canonical/canonical_members derive
membership in the unchanged family. No new publication credential,
physical fraction, floor bound, global no-wrap premise or readonly
conversion is introduced.

Validation: full Link build passed 658 jobs (Proofs 1.3 s, Link 803 ms). Fresh
physical-origin audit checked all 396 declarations in all eight modules,
including private helpers, declaration types, opaque proof bodies and
constructors. Only propext, Classical.choice and Quot.sound occur; zero
exclusions and no unsafe/partial logical dependencies. No sorry, custom
axiom, native_decide or bv_decide is used. Evidence is
/tmp/xv6-lean-research/SupervisorPteADAudit.lean,
supervisor-pte-ad-build.log and supervisor-pte-ad-audit.log.

The Sail audit subagent independently resolved the three proof-mode
normalization sites in scratch: ieval(change ...) with an explicitly typed
fixed-44 callback preserves Iris metadata while Lean checks definitional
equality to the generated conditional bit width. The initial failed
elaboration attempts are not validation evidence; the final build and
full audit passed after this correction. No generated model, installed
library or prior frozen module was changed.

This is direct full physical slot ownership throughout the composed
program. It is not the source predicate-indexed shared KPT accessor, which
must close its invariant between the reread, validation and write events.
Three-level walking, TLB behavior and the full supervisor function regime
remain separate. The general cross-prover model correspondence and whole
xv6 theorem roots remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
