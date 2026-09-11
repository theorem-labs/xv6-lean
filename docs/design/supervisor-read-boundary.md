# Supervisor eight-byte physical read boundary

Proposal only; implementation awaits agreement. Baseline is xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` and the actual generated
`models/riscv/LeanPaperStock` definitions. This follows the completed
SupervisorPhysical partial-register plans and the native TsoContextReadWP rule.

The proposed result is a native WP for actual `checked_mem_read` at explicit
Supervisor privilege, PBMT_PMA, width eight, and all four flags false, for
`Load Data` and `Load PageTableEntry`. A real registered-context word assertion
pays the RAM read. There is no returned-word/readability hypothesis, state
preservation callback, or caller-supplied access implementation in the public
rule.

## Actual path and read sequence

`Mem.lean:404–458` first runs `check_pma_with_pmp_priority`. The completed
SupervisorPhysical proof supplies `Ok (CannotSplit, 0)` from the actual matched
PMA region and its needed permission field. On success this priority wrapper
does not read PMP. `split_misaligned` (`SplitAccessUtils.lean:255–267`) then
returns `(1,8)`: CannotSplit alone selects that branch. Alignment is needed to
obtain CannotSplit from PMA, and is already present in the owned context word.
The pinned increasing order gives `(first,last,step)=(0,0,1)`.

`read_kind_of_flags false false false` (`Mem.lean:221–237`) returns Read_plain.
The one-fuel loop retains its pure dummy assertion, performs exactly one
iteration at offset zero, checks PMP, checks MMIO, and emits the read. The full
register sequence is:

1. `pma_regions` once.
2. `pmpcfg_n` once in `pmpCheck`, followed by `pmpcfg_n` and `pmpaddr_n` in
   `pmpReadAddrReg`.
3. `htif_tohost_base` once in the eager MMIO expression.
4. The actual `.readMem 8` event.

The RAM range, existing positive TOR entry-zero grant, and disabled HTIF value
discharge access/MMIO failure alternatives before that event. No mstatus,
current-privilege, satp or TLB read occurs: privilege is an explicit parameter
of this particular API. The loop writes the returned word into all 64 bits of
its initially zero accumulator, marks itself finished, and returns
`Ok (word, ())`. The full-width update and zero-offset address normalization
will be proved for arbitrary words and addresses, not evaluated at a particular
boot image.

Both access classes emit the same request from `PhysMemInterface.lean:335–376`:
`AK_explicit` with plain variety and normal strength, VA `none`, actual PA,
unit translation metadata, size eight, and tag flag false. It is not an
`AK_ttw` request for PTE reads. The V1 successful response includes optional
tag metadata; `read_ram` ignores that field here. Its `.Err ()` continuation
throws `Error.Exit`. The decomposition must retain that continuation even
though the native owned-RAM rule proves the actual response is
`.Ok (word, none)`.

## Small proof-only prefix interface

Own new `MachCSL/Logic/SupervisorRead{Defs,Spec,Plan,Proofs,Link}.lean` and STATUS,
with no changes to the existing owners' modules or registry. A two-constructor
inductive proposition is sufficient to connect the existing finite register
plans to one real memory boundary:

```lean
-- Interface sketch; dependent types and binder syntax are implementation work.
inductive Boundary (fp : RegisterFootprint.Footprint) (rs : RegisterFile)
    (req : ReadRequest 8) : SailM α → (ReadResult 8 → SailM α) → Prop
  | event : Boundary fp rs req (.impure (.readMem 8 req) k) k
  | prefix
      (before : RegisterPlan.Returns fp rs segment value rs)
      (rest : Boundary fp rs req (next value) k) :
      Boundary fp rs req (segment >>= next) k
```

This is an inductive decomposition of the actual free program, using an already
proved native register-plan judgment. It has no evaluator, alternative machine
relation, resource callback, or assumption that a memory successor is valid.
Bind transport exposes the exact residual after a subsequent continuation.
The native fold is proved by induction: the prefix case uses RegisterPlan.fold;
the event case uses the already implemented TsoContextReadWP rule. This local
interface avoids the unrelated full-register footprint and protocol callback
requirements of the broader instruction EventPlan machinery.

The pure `checked_boundary` theorem constructs that proof for actual
`checked_mem_read ... 8 false false false false`, from these explicit facts:

- Four named fractional register cells in `fp`: PMA table, PMP configuration
  vector, PMP address vector, and HTIF base.
- Existing `SupervisorPmp.TorRam rs`, mathematical `RamRange address 8`, and
  `rs .htif_tohost_base = none`.
- `kind` is data or page-table load, actual `matching_pma_region` equality,
  the respective `readable`/`supports_pte_read` grant under PBMT_PMA, and actual
  eight-byte alignment.

Its conclusion names the concrete request and full residual function, not a
particular returned word. For every response word and optional tag, a separate
residual equality proves reduction to `pure (Ok (word, ()))`; the error
response still reduces to the actual generated exit behavior. The public
native rule invokes this constructed proof itself. It does not ask its caller
to supply Boundary or an arbitrary continuation-preservation certificate.

## Native WP signature and preserved resources

The fixed footprint has four distinct registers and four independently supplied
fractions. Let `cells rs shares` abbreviate existing RegisterFootprint.cells for
that footprint. Let `running`, `wordPointsto` and `viewLB` be the existing
TsoContextReadWP/Tso.Views assertions, with the same capacity, era and names.
The intended `wp_checked_read` shape is:

```text
generationCertificate fixed gen era
  -∗ cells rs shares
  -∗ running era cpu ξ
  -∗ wordPointsto era ξ address dq word
  -∗ ▷ (∀ view,
        cells rs shares
        -∗ running era cpu ξ
        -∗ wordPointsto era ξ address dq word
        -∗ viewLB era cpu view
        -∗ WP (hart gen cpu (continuation (Ok (word, ())))) post)
  -∗ WP (hart gen cpu
      (checked_mem_read access PBMT_PMA Supervisor (Physaddr address)
          8 false false false false >>= continuation)) post
```

TOR, RAM interval, disabled HTIF, actual region match and permission are pure
parameters of this theorem. Alignment is extracted non-destructively from
the word assertion using `TsoContextWord.aligned`, then bridged to generated
`is_aligned_paddr`; it need not be an extra user precondition. The guarded
continuation is the real residual program's continuation, with the same fixed
trace and generation. The generation certificate also handles power changes
through the already proved dead-generation rules.

The final RAM rule opens/restores the complete live era and derives the returned
word at every allowed actual read view from context ownership. It pays the
actual view advancement, returns a receipt for that chosen view, and preserves
the same context and fractional word assertion. It assumes neither an empty
log nor a top/global view. The register cells are framed through that event.
All register-prefix operations and the plain read preserve reservations.
An optional corollary frames and returns the same explicit reservation fragment
for any incoming reservation, using the existing plain-read reservation rule;
no exclusive snapshot creation or clearing rule is invoked.

`Spec` records this public resource contract. `Proofs` constructs the real
prefix and consumes existing native proofs; `Link` supplies the actual Spec
without an unproved subordinate implementation. No new camera is needed.
The structural prefix interface can also be reused for later memory-width
proofs, but this implementation remains exactly eight bytes.

## Source scope and exclusions

The physical read path is the generated counterpart of
`SmodePte.v:336–420` (ordinary physical PTE read) and the aligned read portion
of the supervisor memory pipeline. `SmodeCorePt.v:1321–1530` demonstrates the
source register-prefix/RAM-event staging for fetch, but its two/four-byte
fetch resource is not the resource proved here. The new data read wrapper
will use the concrete registered-context eight-byte rule already implemented
in TsoContextReadWP, rather than retaining the source's generic read callback.

The PTE access-class specialization here still requires an exact registered-
context word assertion. It does not yet consume the canonical A/D-set pin
and publication credentials of `kpt_slot_pin`/`cv_boot_cred`. Those resources
allow PTE A/D variations and require their own native walker proof. Calling
the new prefix on `Load PageTableEntry` does not close that resource gap or
prove Sv39 translation.

`mem_read_priv_meta` and `mem_read_priv` add pure callback/metadata handling;
they are optional separately proved corollaries only if the bounded proof is
already complete. `mem_read` adds mstatus/current-privilege/effective-privilege
reads and is outside this first contract. Pointer masking, virtual translation,
exclusive PTE updates, acquire/release flags, misaligned splitting, MMIO reads,
fetch widths two/four, instruction execution and whole-kernel correctness
remain separate.

Validation will compile all new modules, check the exact emitted request and
singleton-loop arithmetic with ordinary kernel proofs, and audit all physical
declarations plus opaque/type/constructor dependency cones under the existing
three-axiom allowlist. No native_decide/bv_decide or generated-model edits.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
