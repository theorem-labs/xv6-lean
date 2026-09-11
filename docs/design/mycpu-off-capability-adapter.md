# Nonduplicating disabled Bare mycpu resource adapter

Implemented prefix: `Xv6/Kernel/MycpuOff{Defs,Spec,Pure,Resources,Proofs,Link}.lean`,
with STATUS. The reviewed Defs/Spec contract is unchanged. All six modules
build and the full implementation audit passes; independent peer review
is the remaining publication gate. Existing MycpuBare, HartTp and
SupervisorBits files remain unchanged.

The source target is the disabled resource boundary used by
`SpecMycpu.v:31–47`, `ProofMycpu.v:59–318`, `IntrDefs.v:649–653,2672–2699,3224–3229`
and `HartTp.v` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This adapter supplies the
native SIE/TP ownership part of that boundary. Full tier-polymorphic
`sie_cap_gpr`, KPT/virtual free-stack ownership, timer/handler capabilities
and the preceding JAL callable wrapper remain separate.

## Inputs and derived facts

The native capacity consists of the existing `MachineInterp.Capacity`
and the one-bit GhostVar capacity. The SupervisorBits register capacity
is constructed from the **same** machine register capacity; there is no
second register authority or unchecked equality assumption.

The register input has exactly these resources:

- A control footprint of 21 actual cells, obtained by filtering mstatus
  and all GPRs out of the existing mycpu cycle footprint.
- One `SupervisorBits.msOwnAt` at the actual control-file mstatus value:
  the full physical cell, live SIE half, SPP/SPIE tied halves and the
  complete source status fact set.
- The same era/hart's off-token eighth.
- One full `HartTp.pinnedFile` for all 31 actual GPRs and x0's zero fact.

That is 53 physical keys. The six GPR cells in the 28-cell cycle bundle
and the eleven callee-saved frame cells are taken from the single full
GPR bundle. Fourteen other physical GPR cells are retained as an exact
remainder, together with the x0 fact. The 21 controls plus mstatus fund
the other 22 cycle cells. There is no input containing the original
28-cell assertion alongside these resources.

Read-only control shares stay explicit. GPR shares and mstatus are full,
as the source bundles require; their values are not ignored caller share
parameters. Internal `cycleShares` inserts those full fractions exactly
once. Its remaining share fields correspond to actual owned controls.

`EntryConfig control` retains the other concrete Bare hardware conditions:
Supervisor privilege, active hart, elp zero, source MISA/MENVCFG,
delegated MIE, decoded Bare SATP, source TOR grant, disabled HTIF, actual
board PMA and entry PC. It has no SIE, TP, MPRV, MXR or SXL field. SIE=0
is obtained by agreement of the real mstatus tie with the off-token;
MPRV=0, MXR=0 and SXL=2 follow from `msOwn`'s exact facts. TP=cpu is
obtained by splitting actual pinned x4 ownership.

The proof uses a typed symbolic entry file `entry control cpu values`:
GPR constructors read the source pin of the software map, and every
other register reads the supplied control file. Each constructor is
spelled out with its actual generated dependent type. This is a
representation of the owned cells, not an assertion that a pure update
has changed the machine. The resource split must establish the exact
cycle/file assertions at this symbolic file; the native WP rules then
tie those assertions to physical reads. No separate incoming pure TP
equality is accepted.

Generation certificate, actual running context, discarded 34-byte text
span, two full context stack words at modular SP−8/SP−16 and arbitrary
initial reservation are the remaining inputs. All-view memory behavior,
instruction choices and clock branches come from the existing native
function theorem. No new read-success or execution premise is supplied.

## Returning the whole source map

The existing MycpuBare result deliberately says nothing about unowned
GPR fields in its returned **symbolic** register file. It would therefore
be invalid to choose `HartTp.ofRegisters after` as the entire source map
and try to frame old tokens against arbitrary new unowned values.

Instead define `returnedMap before after` by updating only software x10
and x15 from their actual owned returned values. All other entries stay
at the original software-map values. Returned RA, SP and S0 are known
restored by the function theorem. The eleven saved frame cells and the
fourteen untouched cells restore the remaining physical keys. The
software map's TP slot may remain arbitrary: `pinnedFile` still owns
physical x4 at this hart's ID. No TP preservation is added to the source
ABI predicate.

The result includes the existing actual `MycpuBare.HartResult`, all
thirteen source callee-saved software values, unchanged software RA,
A0=`mycpuRet(hartWord cpu)` and its CPU-address arithmetic corollary.
It retains the actual returned x15 value without imposing a new formula.

The final native resource is again exactly `resources`, now indexed by
the returned control file and `returnedMap`. The physical mstatus value
is unchanged by the existing stable-register result, so the same SIE
half, SRET tied halves and off-token are restored without ghost updates.
All bit names are the same era/hart names. The running context and text
are returned, as are both stack words containing the saved entry RA/S0.
The actual restart returns reservation none.

## Native proof and review gates

The proof constructor consumes the independently stated MycpuBare.Spec
and SupervisorBits.Spec; Link supplies their actual implementations.
The HartTp representation is unfolded directly in the proved `gpr_eq`
and native separation equivalence, so no extra accessor specification is
assumed. `footprint_counts` and `footprint_unique` check all 53 keys.
`partition` proves both directions of the concrete 53-to-39-plus-14
resource split, and `reassemble` restores the full file from exactly the
exported function result and held remainder. Pure consequences retain
resource ownership; no full cell is duplicated. No stronger whole-file
preservation premise is added to the existing function contract.

The public native Spec contains one function-CPS theorem. Its only WP
premise is the genuine final continuation, receiving the complete returned
resources and proving the next actual cycle for every next tick. The
adapter invokes the complete existing fourteen-cycle theorem, with its
real fetches, stores/loads, retirement, clock and restart events.
No atomic instruction collapse, selected schedule or handler callback is
introduced. Actual generation-death behavior remains inherited from the
existing native WPs. An old-era token is not reinterpreted as a new-era
capability, and no resource is moved between harts.

This closes a useful source ownership boundary in the Bare function
proof while leaving the other named source capabilities explicit. It is
not a new closed whole-kernel safety or interrupt-enabled theorem.
Validation: all 892 jobs passed. A fresh audit checked all 202 physical
declarations across the six modules, recursively traversing types, opaque
implementation bodies and inductive constructors. Only the three standard
foundational axioms occur; there are no unsafe/partial dependencies and
no exclusions. Independent proof review remains requested.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
