# Supervisor two- and four-byte fetch-read boundary

Proposal only; implementation awaits agreement. Baseline is xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` and actual generated LeanPaperStock.
The next bounded result should generalize the native registered-context read
payer to a byte window, then discharge the actual checked physical instruction
fetch for widths two and four. It should not generalize the aligned eight-byte
word assertion or treat a boot-image read certificate as a live-memory fact.

## Resource and native RAM event

Own new `MachCSL/Logic/TsoContextBytes{Defs,Spec,Proofs,Link}.lean` plus STATUS.
Use the same TsoContext.Capacity/Names and existing `physPointsto`, with no new
camera or alteration of TsoContextWord:

```lean
-- Proposed interfaces; final elaborated binder syntax is implementation work.
def window capacity names ξ a n dq (word : BitVec (8*n)) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    TsoContext.physPointsto capacity names ξ
      (addressAdd a j) dq (nthByte word j))

def Readback g cpu a n word : Prop :=
  ∀ view, g.views cpu ≤ view →
    ReadsBytes g.image g.log (hartAgent cpu) view a n word ∧
    readBytes (read g.image g.log (hartAgent cpu) view) a n = some word
```

The window has no alignment assertion. It owns exactly n bytes at the actual
modular addresses. The generic aggregation lemma may cover every Nat n,
including zero, since the byte-read theorem and assembler already do; the
physical checked-fetch API below remains restricted to two/four. No cardinality
or no-wrap premise is needed to aggregate reads. Such premises are needed
when extracting exclusive clients from a finite map and remain there.

Each byte owns the existing fractional physical heap cell, the matching
fractional timestamp `(time,payNone)`, and either the context floor receipt or
its dirty membership. The all-view fact is derived by applying the actual
`TsoContext.load_fact` to each owned byte at the same arbitrary view, then
`readBytes_of_bytes`. Both clean and authored-dirty arms remain valid. There
is no immutable-image premise, supplied readability function or state update
oracle. Return the unchanged complete heap, timestamp/log interpretation,
running context and window along with the derived fact, following the current
TsoContextWord load proof. Provide ordinary timelessness, byte/word agreement,
window slicing/reassembly and a forward fractional split where needed.

Use `TsoContextBytesReadWP{Defs,Spec,Proofs,Link}.lean` plus STATUS for the real
memory event, reusing the exact capacity/name conversions already exported by
TsoContextReadWP. Its proposed `wp_read` is:

```text
-- req : ReadRequest n; word : BitVec (8*n)
-- Pure guards: deviceAddress req.pa = false;
--              accessExclusive req.access_kind = false.
generationCertificate fixed gen era
  -∗ running era cpu ξ
  -∗ window era ξ req.pa n dq word
  -∗ ▷ (∀ view,
       running era cpu ξ -∗ window era ξ req.pa n dq word
       -∗ viewLB era cpu view
       -∗ WP (hart gen cpu (k (Ok (word, none)))) post)
  -∗ WP (hart gen cpu (impure (readMem n req) k)) post
```

The generic event preserves all request metadata and its dependent width; it
does not reinterpret a fetch as a different read kind. Open and restore the
actual full live era, derive the all-view fact from those resources, then
construct `MemoryReadWP.wp_ram_read_plain_ex`'s callback internally with
`P actual := actual = word`. That existing rule pays the real view advancement
and mints the chosen-view receipt. Its callback is an implementation detail,
never a public premise. The same fixed trace/generation and all unrelated
resources remain framed. Provide exact live-step inversion and an optional
reservation-framing corollary: plain reads preserve any incoming reservation.
No top-view or empty-log assumption and no liveness claim are added.

## Actual checked physical fetch

Own new `SupervisorFetchRead{Defs,Spec,Plan,Proofs,Link}.lean` plus STATUS.
Use a small width selector with `half → 2` and `word → 4`, or equivalent exact
`n=2 ∨ n=4` proof. Define the actual program:

```lean
checked_mem_read (.InstructionFetch ()) .PBMT_PMA .Supervisor
  (.Physaddr address) n false false false false
```

The emitted request is still **Read_plain**: `read_kind_of_flags` sees only
three false flags. The V1 access is explicit plain/normal, VA none, PA actual,
unit translation, size n and tag false. Do not replace it with Read_ifetch or
an invented instruction-only event. The pure result is `Ok (word, ())`.

Reuse SupervisorPhysical's already proved `fetch2`/`fetch4` supported cases,
actual matched region and its executable grant, aligned PMA priority plan,
positive supervisor TOR plan, mathematical RAM interval and disabled HTIF.
The four independent register fractions remain PMA table, PMP configuration,
PMP addresses and HTIF base. The actual sequence is PMA once, PMP cfg/cfg/addr,
then eager HTIF: five reads from four cells. Successful PMA priority performs
no extra PMP check. The pure prefix proves CannotSplit, singleton offset zero,
full 16/32-bit accumulator update and both V1 tails. Every successful optional
tag is ignored as generated; the error response still exits with Error.Exit.

The local Boundary is the same proof-only two-constructor shape as
SupervisorRead.Boundary, but indexed by arbitrary event width. Leave the frozen
eight-byte modules unchanged. Inductively fold register prefixes using native
RegisterPlan and the new concrete context-window event rule. The public rule
constructs the whole Boundary from the generated program.

The public contract takes exact physical alignment at the chosen width:
`is_aligned_paddr (Physaddr address) n = true`. This is source fetch geometry,
not `address % 8 = 0`. It also takes the actual region match/executable grant,
TorRam configuration, RAM interval and HTIF-none premises. It owns four cells,
a running context and the fractional n-byte window, and returns those same
resources plus the selected view receipt through the guarded continuation of
`Ok (word, ())`. No eight-byte word or enclosing aligned eight-byte allocation
is required. Two concrete corollaries expose BitVec16 and BitVec32 without
awkward dependent casts.

This matches the physical staging of `SmodeCorePt.v:1321–1530` and the rest of
`swp_checked_mem_read_ifetch2_S`: source proofs currently take an all-view
`fobl_ram` resource callback. The proposed native API discharges that callback
from its explicit context window. It does not claim the complete source text
resource or virtual-fetch theorem merely because the physical class is fetch.

## Text ownership, boot extraction and overlap

Source `RiscvPtsto.v:1515–1522` text ownership is richer than the proposed
physical window: it includes a KP_rx virtual-page mapping, positive canonical
virtual address, text physical address, tier pin, fractional byte ownership
and a discarded timestamp-zero pristine fragment. `InstrBytes.v:52ff` then
uses persistent discarded text windows with instruction geometry. Source
`SmodeCorePt.s_fetch_chunk` additionally relates the virtual window to the
particular translated physical page. These are separate future bridges.

A fractional context byte requires the same fraction on its byte and timestamp
cells. Therefore a fractional byte plus a **discarded** pristine timestamp
cannot silently be promoted to a fractional context byte. Two honest bridges
are available:

- A real stored window at timestamp zero, with both full byte and full
  timestamp clients, yields a full context window using `floor_zero`.
  Fractions can then be split consistently before any persistence conversion.
- A discarded byte window plus discarded pristine timestamps yields a
  discarded context window for any context, again using `floor_zero`.
  Such a discarded window is persistent. If converting owned bytes/timestamps
  to discarded clients, use the real native persistence updates and record
  the loss of mutable ownership. No fractional timestamp may be recreated.

The generic timestamp-zero bridge is a useful bounded supporting theorem in
TsoContextBytes. Initial full clients must still come from actual Era boot
allocation and extraction from the same finite byte/timestamp maps. Existing
BootWindow.extract_stored supplies the needed shape while retaining the exact
map remainder. The concrete mycpu allocation/link can follow after this API;
it must neither allocate replacement memory authority nor assert initial
bytes remain current without ownership.

MycpuFetchBytes already certifies all 34 initial RAM bytes and each exact
fetch-width word, not ghost ownership. Its 14 instruction windows overlap:
one four-byte fetch can include bytes also used by a neighboring two-byte
instruction. Therefore it would be unsound to demand or derive fourteen full
separately owned windows by repeated full-map extraction. Extract the unique
34-byte span once, retain the exact remainder, then either open/reassemble
selected fractional subwindows on demand or persist the code bytes/timestamps
and duplicate discarded windows. This is the same source reason for persistent
kernel_text. The proposed first native physical rule works with either
legitimately obtained fraction; it assumes no initial allocation shortcut.

## Mycpu and the remaining fetch chain

Actual Fetch.lean:216–280 translates each fetch granule and then invokes
mem_read, including its own effective-privilege register prefix. Those stages
are not bypassed by the new checked-read rule. Existing SupervisorBare handles
the Bare translateAddr branch; KPT still requires its real TLB/walker and
mapping resources, canonical A/D pin credentials and tier relation. A physical
address is not equated with a virtual PC for the KPT branch.

With four-byte PC alignment **and currentlyEnabled Ext_Ziccif=true**, the
actual fetch reads four bytes even when the decoded instruction is compressed.
MycpuFetchBytes.ziccif_enabled proves the pinned platform branch. Otherwise it
starts with two bytes; a noncompressed low half needs a separately translated
second half. Existing mycpu certificates establish that every noncompressed
instruction in this body is four-byte aligned, so this body avoids the latter
straddling case under the pinned Ziccif configuration. The general rule must
not infer that fact for unrelated code.

The function begins at 0x800018ba, is 32 bytes long, and its actual fetch union
is 34 bytes. The last four-byte fetch is `0x11018082`; its upper two bytes are
past the function body. MycpuFetchBytes proves exact initial ELF/RAM bytes,
widths, low halves and full base words. Those certificates can discharge
future concrete slicing and alignment obligations, but they are neither an
immutable-memory oracle nor a native instruction/resource proof.

This bounded implementation adds no slot, changes no generated code and
leaves current owners' modules untouched. First freeze/audit the generic byte
aggregation and real event WP, then freeze/audit the two physical prefixes.
Check every physical declaration and all type/opaque-body/constructor cones
against the three foundational axioms. Full fetch, decode/execute composition,
KPT translation, kernel_text allocation and the complete mycpu specification
remain explicit subsequent tasks.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
