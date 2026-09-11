# Full shared-KPT mycpu function boundary

The native rule composes the fourteen actual MycpuKptCycle rules on
one source fifty-cell packet, folded KPT residue, running context, code and
fixed virtual save area. It starts at the linked entry PC with arbitrary
original GPR values, initial scratch-word contents, reservation and clock
values. The only continuation WP is the actual cycle after the return.

Source mapping uses the pinned `SpecMycpu.v:26–52` disabled-interrupt body
contract and `ProofMycpu.v:62–318`: the eleven source software-map updates,
actual TP read, stores at indices 1/2, loads at 10/11, and final SP restore
and compressed return. The existing generated fourteen-cycle rule preserves
its actual fetch, decoder, execute, retirement, clock and restart effects.
The source/model correspondence limitation remains unchanged.

## Pure phase and result contract

`Phase` is internal pure bookkeeping. Its zero constructor retains the
initial packet values and arbitrary old words. Its successor constructor
uses the actual indexed `bodyControl`, `bodyValues`, `bodyWords` and existing
`Completed` relation. This admits every permitted clock successor, including
counter overflow and all hardware-read branches. It is not an input to the
public function WP and does not assert independent machine reachability.

The twelve pure contracts establish the phase bound, stable configuration,
owned non-clock controls, indexed PC, memory-only StackReady, saved-word
schedule, final source register-sequence projection and final result. The
saved RA word becomes known after index 1; the saved S0 word after index 2.
Those exact words are then supplied to the native load rules. The save anchor
always remains entrySP−16; scalar SP changes do not move either word resource.

The final result restores SP, RA, S0 and all original software GPR keys except
a0/a5, proves the exact thirteen-register callee-saved predicate, and obtains
`a0 = mycpuRet(hartWord cpu)` and numeric address `0x800123e8 + 128*cpu.val`.
The actual low-bit-cleared RA is both PC and nextPC. Only owned non-clock
control columns are exported as stable; SATP, PMP and TLB remain folded in
the residue. A separate pure result consumer restores the entry adapter's
`SieOffPacket.Boundary` at the real return target.

Arithmetic may reuse the earlier MycpuBare reference theorems only after a
proved full register-file projection links this new phase to that reference
or to MycpuRegisterSequence. No Bare hardware configuration, physical stack
predicate, Bare native WP or fixed clock snapshot enters this interface.
The synthetic control file represents its owned columns; no equality with
unowned physical GPR/control cells is claimed.

## Native composition and receipts

The input `resources` owns packet, code, running context, the two full virtual
words, actual reservation and arbitrary literal frame. The frame can carry
the entry adapter's untouched stack tail, timer, hardware, publication shot,
tier receipt and explicit same-hart PMA resource. No SATP/PMP/TLB cell is
owned twice and no new camera is introduced.

The native induction must derive the actual indexed PC and StackReady, then
invoke the constructed Cycle rule. It traverses that rule's exact
`guardChunks` and dependent body guards, including shared-translation A/D
branches and the data-event guard. The internal Completed premise is
received from the actual rule; the final restart guard retains arbitrary
nextTick and clears the real reservation. No per-step success or component
WP premise survives in the public function contract.

Every cycle contributes an indexed receipt record containing its actual
fetch trace and dependent body outcome. The final continuation receives all
fourteen receipt bundles in index order, along with the restored packet,
code, running context, folded residue, saved original RA/S0 words, none
reservation and original frame. These receipts do not choose a memory view
or constrain an event branch. The pure `Ordered` fact records exactly the
indices 0 through 13.

## Checkpoint and remaining scope

All twelve pure contracts and the native function contract are implemented
in seven modules: Defs, Spec, State, Pure, Guards, Proofs and Link. Actual
`nativePureSpec`, `nativeSpec` and `registrySpec` constructors supply the
approved signatures without component assumptions. The complete Link build
passed 1,155 jobs (State 8.7 s, Pure 2.0 s, Guards 1.3 s, Proofs 1.3 s,
Link 1.1 s). STATUS records the final physical declaration audit.

The full-entry equality `body_entry`, `completed_entry` and simultaneous
`phase_reference`/word-schedule induction justify every use of prior reference
arithmetic. The native `chain` builds this phase and the ascending receipt
list after each actual Cycle rule. The only definitional additions after
review are the logical reservation schedule and making recursive receipt
ownership noncomputable; no contract is strengthened.

The resource rule remains separate from the full source capability wrapper.
MycpuKptEntry supplies the source stack/capability opening and restoration;
its explicit extra PMA equality remains visible. The source JAL-call wrapper,
interrupt-enabled migration/handler contract and operational resource
allocation/reachability are not claimed by this checkpoint.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
