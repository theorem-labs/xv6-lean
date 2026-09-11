# Independent boot-window extraction review

Codex independently reviewed the root agent's frozen `BootWindowDefs.lean`
and `BootWindowProofs.lean`, including the imported `extract_keys` proof and
actual `TsoRead.byteWindow`/`TsoStore.storedWindow` definitions. No correction
was required. This is new generic extraction glue for the port's existing
source-backed ownership assertions; it is not advertised as a new upstream
Rocq theorem or a boot-allocation theorem.

The physical carrier is the actual modular 64-bit address type. `keys_nodup`
uses the proved below-modulus address-add injection and permits size exactly
2^64. Byte extraction needs the full requested lookup and per-byte RAM fact;
zero-size windows introduce no lookup obligations. Timestamp extraction
preserves the exact `(t, payNone)` payload and full fraction. `storedWindow_split`
uses native separating-list distribution; it neither creates nor weakens either
resource component.

For multiple words, the complete concatenated byte-key list must be duplicate
free. Its append disjointness supplies each later word's lookup after deleting
the current word. The proof performs each native map deletion on the actual
map, recursively retains both full residual maps, and identifies the final
result with deletion of the complete key list. `lookup_deleteKeys` independently
proves that every unselected key retains its original lookup. The chosen value
function's default byte is used only under the proved membership lookup; it
cannot supply missing RAM. There is no allocation, fancy update, authority
replacement, preferred finite-map representation or full-memory hypothesis.

I independently ran `python3 tools/lake.py build MachCSL.Logic.BootWindowProofs`
(all 418 dependency jobs passed) and a fresh physical-origin audit covering
all 35 declarations in the two modules, including generated helpers. The audit
traversed the entire type/body dependency cone, accepted only `propext`,
`Classical.choice` and `Quot.sound`, rejected unsafe/partial logical dependencies,
and excluded zero declarations. The audit driver and output are
`/tmp/xv6-lean-research/BootWindowIndependentAudit.lean` and
`/tmp/xv6-lean-research/boot-window-independent-audit.log`.

The concrete boot decoder equality, image membership, all instruction/data
lookups and joint non-overlap remain obligations of the specialization.
This reviewer authored some previously reviewed imported memory/ghost libraries;
the two reviewed modules and generic deletion helper were root-authored.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
