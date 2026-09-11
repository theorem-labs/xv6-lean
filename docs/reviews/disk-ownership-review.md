# Independent review: disk-image ownership

Reviewer: Codex coordinator. Read all443 lines of the pinned `DiskImg.v`,
the independent Lean specification and the complete implementation.

The port retains the total signed-offset disk function and its finite-map
view. Range updates preserve lengths and report both new lookups and the
unchanged outside map. Minting requires absent keys; the domain-reporting
variant retains the source's vacuous old-map premise. Allocation returns
every full byte fragment it creates.

The sized write rule requires the whole `[0,n)` fragment and bounds every
authority key to that interval. It can consequently replace the represented
total disk with an arbitrary target, without constraining unowned offsets.
This matches the source, including empty ranges and signed offsets. The
per-era and durable authorities remain separate runtime names.

Independent build and all138 declaration-cone checks passed with only
`propext`, `Classical.choice` and `Quot.sound`. No unsafe, partial, sorry or
custom-axiom implementation was found. Review: PASS for this resource layer;
disk-driver lifting, crash invariants and adequacy remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
