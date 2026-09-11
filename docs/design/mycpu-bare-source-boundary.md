# Disabled source mycpu: identity-tier Bare arm

This checkpoint connects the actual opened Bare arm of the disabled source
capability to the already proved fourteen-cycle `MycpuOff` function. It
implements resource contracts without replacing the instruction engine.
All six pure, six resource and one native contract are proved. The final
Link supplies the actual `MycpuOff.nativeSpec` implementation internally.

Source mapping at the pinned xv6iris revision:

- `SpecMycpu.v:31–49` requires disabled SIE, at least two scratch words,
  kernel text and entry `pc_is`; it returns the same capability and stack
  count, thirteen callee-saved registers and a0 computed from the entry TP.
  The preceding comment explains why enabled interrupts would require a
  different migration-sensitive contract.
- `SRegime.v:823–856` makes the Bare slot own an existential full SATP
  cell with mode zero and the actual two-register PMP configuration. It
  explicitly excludes a TLB cell. Identity address claims justify the
  physical access; no page table or TLB successor is fabricated.
- `TsoCtx.v:628–641,845–860` specifies virtual context bytes with mapping,
  tier, physical byte and timestamp ownership and a clean/dirty alternative;
  words add actual eight-byte alignment and eight modular byte offsets.
- `StackOwn.v:136–169,271–303` specifies existential scratch contents and
  the exact two-slot split/join at `pa_stk sp 1` and `pa_stk sp 2`.

`SieOffPacket.open_packet` yields a regime and actual resources. Identity
tier admits **both** Bare and KPT; it does not determine the branch. The
public `MycpuBareSource.input` is precisely the Bare arm: an existential
control file, its already-derived `Ambient` facts, and the actual opened
identity-tier Bare packet. Source identity kernel text, the same-hart
discarded `pmaBoot` cell and a literal caller frame accompany it. The later
source dispatcher must route the KPT arm separately. No caller supplies
`MycpuOff.EntryConfig`, physical words, an execution witness or a body WP.

The resource partition extracts SATP and both PMP vectors from the actual
existential Bare slot. `patch control satp pmp` changes only those three
projections. The native `packet` equivalence then assembles the existing
53-cell `MycpuOff.resources` from the source fifty cells and these three
cells. The real full status, SIE/SRET ties, off token and all 31 GPR cells
are retained once. SATP/PMP values in the original synthetic control file
are never asserted to describe physical state. There is no TLB ownership.

The six pure contracts derive the patched configuration and ambient facts,
source result, restored SP and source return boundary, and certify the
entire 34-byte Bare fetch span in the source text. The last includes the
two genuine lookahead bytes after mycpu. It uses the existing sparse
source-map lookup and physical span definition without changing generated
bytes. Native text extraction preserves the original persistent text and
derives the actual discarded physical byte window and pristine timestamps.

The six resource contracts cover identity word access, code extraction,
the register partition, entry opening, entry closing and certificate
access. Identity word access derives the actual physical address from the
owned mapping claim and keeps a value-polymorphic closing wand. The
scratch stack splits into arbitrary RA/S0 word contents and an untouched
tail anchored at entrySP−16. Both closing wands retain all original mapping
claims and accept newly stored physical/context words with their actual
updated timestamps. The frame also retains the source timer, identity
tier witness, complete hardware assertion, pending token, stvec, text,
boot-PMA cell and caller frame. No pristine condition is imposed on stack
data, no context reindexing is performed, and no global no-wrap bound is
introduced.

The native function contract instantiates `MycpuOff.nativeSpec` with
the constructed 53-cell resources, derived configuration/certificate,
physical save pair and code. Its actual returned `Result` supplies restored
SP, stable Bare translation controls, source boundary and GPR conclusions.
The two mapping wands rebuild virtual saved words, and the exact stack join
restores the original count with changed scratch contents. All source
resources close through `SieOffPacket.close_packet`. The only WP input is
the genuine final returned-cycle continuation, universally quantified over
the next actual clock choice. The existing native function already handles
all fourteen actual cycles, blocking and clock/counter behavior.

Seven frozen Lean modules: `MycpuBareSourceDefs`, `Spec`, `Pure`,
`Resources`, `Entry`, `Proofs` and `Link`, plus STATUS and this design.
`nativePureSpec`, `nativeResourceSpec`, `nativeSpec` and `registrySpec`
are all actual constructors with no remaining component-interface input.
No new camera, registry slot, frozen family or umbrella edit is needed.
This is not yet the tier-generic source dispatcher, native source-entry
inhabitation, boot reachability, enabled-SIE function or general-PMA theorem.

Validation: the final native Link passed 1,031 jobs; entry proof 1.7 s,
function proof 1.4 s and Link 1.1 s. A fresh audit checked all 120
declarations from seven physical modules, following all types, opaque
bodies and constructors. Only `propext`, `Classical.choice` and `Quot.sound`
occur; there are no unsafe/partial dependencies and zero exclusions.
Logs: `/tmp/xv6-lean-research/mycpu-bare-source-native4.log` and
`mycpu-bare-source-audit.log`; audit script `MycpuBareSourceAudit.lean`
in the same directory. Implementation made the text-offset binder explicitly
`Nat`, correcting the checkpoint's unintended inference as `Int`; the
contract now expresses exactly the intended 34-byte window.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
