Four-byte source data ownership

The noff and intena fields used by push_off and pop_off are four-byte
source context words. KernelDatumWord4 owns exactly four virtual bytes,
each with its actual mapping, positive address, RAM range, tier pin and
physical context ownership, together with virtual four-byte alignment.
This agrees definitionally with CpuOwn.word4 at identity tier.

Four-byte alignment prevents wrapping or crossing a 4 KiB page within
the four owned bytes. The proof chooses the head byte's actual PPN and
uses native map agreement to identify every other byte's PPN. It returns
all four persistent claims and the aligned physical context window,
plus a replacement-value wand funded by those retained claims. Replacing
the physical bytes reconstructs exactly the original virtual word and tier.
No mapping, physical bytes, or replacement wand is supplied as an oracle.

The implementation specializes the existing native eight-byte geometry
and resource-access argument to four bytes and 32-bit values. It does not
assert an actual load, store, translation, CPU count update or function WP.
Those must use the actual four-byte Sail memory events and preserve the
translation/data guards and returned views.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
