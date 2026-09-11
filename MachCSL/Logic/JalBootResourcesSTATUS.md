# JAL boot resource partition

The six JalBootResources modules split the actual boot allocator's resources.
`registers_split` separates the 178 per-hart owned register cells from the two
PLIC pin cells on each of eight harts. `reservations_split` preserves the exact
all-hart reservation map. `boot_code_lookup` derives four instruction-byte
lookups from arbitrary actual BootFacts and the allocator's decoding equation.

`extract_keys` retains the full map remainder. `boot_code` converts only the four
code timestamps to persistent pristine receipts, splits each code byte into
eight positive one-eighth shares, and retains the remaining full byte and timestamp
maps and initial log receipt. The resulting ownership handles all legal TSO views.
No preferred register witness or runtime evaluation of the full RAM map is used.

Validation: the component build passed 464 jobs; the complete handler integration
passed 509 jobs. Independent review audited 49 declarations and their logical
cones using only propext, Classical.choice and Quot.sound. One compiler-generated
total-recursion runtime companion was excluded only as an audit root, not from
logical dependency checks. See docs/reviews/jal-boot-resources-review.md.

The caller still owes the actual eleven boot-thread WPs. These helpers alone do
not establish a closed machine theorem or any xv6 kernel theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
