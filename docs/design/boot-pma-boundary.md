# Actual boot PMA resource producer

BootPmaDefs, BootPmaSpec, BootPmaProofs and BootPmaLink implement the five
pure and eight native contracts approved by the coordinator. The complete
component builds in 872 jobs. Its strict owner audit covers all 63 physical
declarations and their types, opaque bodies and constructor dependencies:
only the standard three axioms, no unsafe/partial dependency, zero exclusions.

The source board_regs writes its explicit PMA parameter before the actual
generated initialization (iris/ArchReset.v:245–276). Lean BootFacts records
that real boot run from arbitrary initial register files. The existing
BootUniversal.bootFacts_static projection establishes pmaBoot on each of
the eight resulting files. This producer uses that theorem, rather than an
assumed equality or a separate register allocator.

For each hart, partition its actual Registers.initialCells finite map into
the full pma_regions cell and the exact PartialMap.delete remainder. The
remaining generated-register enumeration has 179 keys; each dependent
payload is unchanged. Split the Fin 8 conjunction once, persist the eight
extracted full cells, and expose persistent same-hart discarded cells.
No full PMA ownership remains in the output or in a restoration wand.

The base producer retains the complete TSO clients and all metadata,
device, durable-disk and reservation columns. The text producer consumes
the register column of KernelTextBoot.retained; it preserves the existing
exact sparse byte/timestamp deletion remainder and log-length receipt.
Thus the combined producer spends neither overlapping text bytes nor PMA
cells twice. Its allocator invokes the existing actual Era/text allocation
once and returns Era.interp, era.image equality and AuxiliarySame as well
as both persistent outputs and all remaining clients. encodeAll is a
symbolic finite-map witness, never an evaluated enumeration.

Every whole-result update in the Spec is explicitly parenthesized. This
layer installs no source supervisor capability, physical KPT, translation
resource or whole-function entry state. It allocates no camera slot.

Reproduce: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.BootPmaLink`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
