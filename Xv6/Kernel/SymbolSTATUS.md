# Kernel symbol-table occurrence certificates

All 222 imported KernelSyms names and values are checked against the actual
pinned ELF. all_imported exposes an actual parsed row for every member of the
imported symbol list, preserving the original ELF name rather than its sanitized
Rocq alias. The selected table is section 18; its actual sh_link identifies
string table 19. Certificates inspect all raw name bytes and a terminating NUL
inside that string table, the exact st_value, and a nonzero st_shndx.

The selected ELF64 reader follows the [gABI symbol layout](https://gabi.xinuos.com/elf/05-symtab.html)
and [section links and entry sizes](https://gabi.xinuos.com/elf/03-sheader.html).
It checks the format bytes, selected section types, 24-byte entries, table and
string payload bounds, row bounds, name bounds and termination. Compressed
symbol/string sections are explicitly rejected. Names remain raw byte lists;
no host Unicode decoder contributes to a Lean proof.

mycpu_symbol checks the complete row at index 141: ELF name mycpu, global
function info, text section, address 0x800018ba and size 32. cpus_symbol checks
row 219: global object, section 7, address 0x800123e8 and size 1024.
executable_elf additionally checks the actual ET_EXEC field. These facts now
connect the named addresses used by the decode/fetch certificates to the ELF.

The reproducible untrusted tools/symbol_certificates.py importer verifies the
source revision, both tracked source files and the kernel byte hash. It derives
one unique matching row witness for each source name/value, retaining source
order and aliases. Its output is checked by ordinary Lean decide; no native
execution axiom is used. The full 222-row certificate took 14 seconds locally.
The final SymbolImageProofs target passed 465 build jobs.

Reproduce with python3 tools/symbol_certificates.py .upstream/xv6iris --check
and python3 tools/lake.py build Xv6.Kernel.SymbolImageProofs.

This is occurrence, not equality to nm output: the source dumper runs nm,
filters lines and keeps the first duplicate name. The proof neither recreates
that external algorithm nor claims there are no additional ELF symbols. The
reader is not a global ELF validator; it reads selected ordinary table indices,
retains extended symbol indices raw, and does not implement extended table
counts or dynamic symbol tables. Actual code ownership, translation, instruction
execution and complete function verification remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
