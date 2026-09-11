# Source full-tier mycpu entry and restoration

The actual MycpuKptEntryDefs/Spec checkpoint has four pure and four native
contracts. The approved signatures and complete native implementation
compile in966 jobs. All53 physical declarations passed a strict full
type/opaque/constructor audit with standard axioms and zero exclusions. This is a resource adapter to the native KPT cycle/body
packet; it is not a whole-function WP, execution witness or boot allocation.

I read the complete pinned ProofMycpu.v and the relevant StackOwn.v source
split/append/two-word definitions, with native KernelStack, SieOffPacket,
MycpuKptBody and MycpuKptCycle interfaces. Source pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. ProofMycpu's real prologue allocates
two slots by moving SP, saves RA/S0, later loads them, and returns the free
stack through the epilogue. This component prepares and restores that exact
resource partition while leaving all actual instructions to the existing
body/cycle proofs and subsequent function chain.

The input is exact SieOffPacket.input at the literal first mycpu instruction,
full tier, with two separately supplied persistent resources: an actual
same-hart pma_regions↦discard pmaBoot cell and actual MycpuKptFetch.code.
Code production from kernel_text stays in the coordinator's KernelTextImage
component. No raw byte/default lookup, decoder success or translation result
is substituted for native code ownership.

open_entry requires available≥2. Native SieOffPacket.open derives Ambient
and Admits; at full tier Bare is impossible because the retained source
receipt conflicts with pending. Thus the actual existential root belongs
to the original source kptN. The optional native PMA agreement rule relates
the owned packet cell to the separately supplied boot table fragment. From
Ambient plus this agreement, config derives the actual Cycle.Config:
Supervisor privilege, active hart, full MISA literal, source MENVCFG literal,
interrupt delegation, PMA boot equality and absent HTIF. ELP is one bit, so
its actual not-LP_EXPECTED fact implies zero. No additional mstatus constant
is imposed; the native msOwn/off resources continue to pay status facts.

save_area is the exact native KernelStack.frame_two equivalence rephrased
as the body's two-slot function. The arbitrary initial word at entrySP−8
becomes the RA slot; the arbitrary word at entrySP−16 becomes the S0 slot.
Neither is assumed to hold the caller's saved register value before the
actual store. The tail is literally stack_own(entrySP−16, available−2).
All addresses use the existing modular paStk; no global stack bounds,
alignment or disjoint-page premise is added.

The returned resources are the actual50-cell packet at source shares,
code at full tier, the same running context, the two native virtual words
anchored to immutable entrySP, the existential exact reservation fragment,
and an explicit frame. The frame contains the tail, timer, full-tier receipt,
whole hardware config, linear shot and persistent boot-PMA fragment. It
contains no restoration callback and does not hide the running context.
Source resvAny is opened into its actual existential; it is not forced empty.

close_entry takes the real returned packet/pair/frame and permits arbitrary
new save-area contents, GPR file, clock/status cells and coherent TLB residue.
It requires the actual returned SP to equal immutable entrySP and the same
owned-projection Boundary(returnPC) as SieOffPacket.close_packet. Native
stack reassembly existentially accepts the returned words and restores the
full original available count. It then returns the complete source input at
returnPC and the same code/boot-PMA resources. No function result, callee-save
fact, clock trace or word value is assumed; the function proof must establish
its own result and SP restoration before using this closing law.

The certificate accessor exposes the existing actual generation certificate
and preserves the entire resources bundle. No fresh name, camera or resource
allocation is introduced. Full source Sconf retains general PmaClass; this
adapter's literal-PMA specialization remains explicit and cannot establish
its extra register fragment from source hardware alone. Native boot/resource
inhabitation and the fourteen-cycle full function remain separate obligations.

Validation: PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build
Xv6.Kernel.MycpuKptEntrySpec. Log:
/tmp/xv6-lean-research/mycpu-kpt-entry-signatures.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
