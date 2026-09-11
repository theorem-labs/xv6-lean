Width-generic ordinary data PMA checks

SupervisorDataPma supplies finite RegisterPlan proofs for the actual
pmaCheck and check_pma_with_pmp_priority calls, for ordinary nonreserved
Load.Data and Store.Data and an arbitrary natural byte width. Inputs name
the actual matching region, its consumed readable/writable attribute and
actual physical alignment. The program reads the owned pma_regions cell
and preserves the entire register file.

The proof follows the generated exception/control flow and alignment path;
the successful priority wrapper performs no PMP read. It produces only
aligned permission information. It does not perform translation, PMP,
RAM access or any data event, nor infer a successful word or write result.
The four-byte memory rules consume this finite prefix with their separate
actual PMP/RAM checks and owned data windows.

This generalizes the existing eight-byte ordinary-data PMA proof argument
without editing the generated model or its bounded SupportedRead family.
The native Link supplies both implementations, with no component-law or
execution-success premise. Width zero or other unusual widths are not
silently treated as supported memory operations: only the exact PMA call
is covered, under its explicit matching/alignment premises.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
