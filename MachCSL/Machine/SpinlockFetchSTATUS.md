# Universal fetch for the seventeen-word integration image

`SpinlockFetch{Defs,Proofs}` proves the actual generated `fetch ()` returns
`F_Base (SpinlockImage.word index)` for every `index : Fin 17`, using native
`EventWP.Returns`. The register file is arbitrary subject to the existing
`BootUniversal.StaticBoot` fields at that instruction address and
`BootPmp.Off`. PMP address registers and all unrelated configuration bits
remain arbitrary; the proof uses the actual universal all-OFF PMP plan.

The proof composes actual generated PC reads, extension checks, virtual
translation, PMA/PMP checks, MMIO classification, and the `read_ram`
`Read_plain` request. The only allowed memory result is the exact four-byte
word at the indexed code address, expressed by `CodeRead`. `codeRead_image`
proves this predicate is satisfied by the actual initial `loadedRam image`
bytes using `SpinlockImage.instruction_bytes`. Later resource-level uses
must retain or reacquire those byte resources; no equality between all
future RAM and the initial image is assumed here.

The PMA, translation, MMIO, Zca and Ziccif snapshot certificates cover only
explicit fields whose equality is proved by `accessSnapshot_covers`.
They do not supply a full register file, arbitrary memory oracle, or omitted
PMP address values. The final fetch proof handles arbitrary indices directly,
using checked zero address bits 0/1, four-byte alignment, and false `isRVC`
for each word's low half. All those finite facts are ordinary kernel-checked
reflexivity certificates. Every actual event remains in the sequential plan.

`checked_mem_read_plan` retains an explicit PMP subplan interface; the
exported `mem_read_plan` discharges it using `BootPmp.check_off_plan`.
`universal_fetch_plan` has only the static/OFF register hypotheses and exact
read predicate; there is no undischarged evaluator-success or
successor-preservation premise. It leaves the register file unchanged.

This is a fetch-plan layer for a new integration image, not a proof of xv6
kernel execution, an AMO rule, or spinlock safety. Its static predicate
includes PC and nextPC at the selected instruction address; it does not
claim every arbitrary runtime register state satisfies that predicate.
Decode certificates live separately in `SpinlockDecode`. Native instruction
WPs must still compose the fetch/decoder/execution plans with real ownership
and preserve the required state between events.

Validation: `python3 tools/lake.py build MachCSL.Machine.SpinlockFetchProofs`
passes 413 jobs. The recorded final proof build takes 7.2 seconds; the
command takes 8.25 seconds with approximately 2.02 GB peak RSS. The full
physical-origin/type-and-body-cone audit is
`/tmp/xv6-lean-research/SpinlockFetchAudit.lean`. All 69 physically originating
logical declarations, including private/generated helpers, pass. Only the
standard three foundational axioms occur, with no unsafe/partial semantic
dependencies and zero excluded runtime companions.

The root agent implemented the initial fetch decomposition. The
artifact-audit agent completed the alignment/compressed-result seams,
removed repetition from the final symbolic proof, and added the actual
image-byte bridge. This record is implementation validation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
