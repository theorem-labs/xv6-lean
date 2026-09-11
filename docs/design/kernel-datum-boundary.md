# Virtual context data and kernel tiers

The source is the complete Ktier.v, RiscvPtsto.v 1147–1262 and TsoCtx.v
608–640, at paper pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
KernelDatum ports the data resource itself. It has no instruction or
translation WP contract. The independently approved Defs/Spec are now fully
implemented: four-module build 653 jobs, separate complete 96-declaration
audits and independent implementation review pass.

The two explicit tiers are identity and full. Their order excludes only
full-to-identity weakening. An identity-tier datum has the actual physical
PPN/offset address equal to its virtual address. Full-tier data may use any
mapping. A pure equality can establish either pin, while weakening retains
all other resources. This uses explicit tier arguments rather than a global
implicit default, avoiding accidental elaboration choices at call sites.

Each virtual byte contains the native persistent RW mapping claim at the
actual era name, the source positive-half bound VA < 2^38, physical RAM
membership and its tier pin. Its remaining assertion is exactly the existing
physical context byte: heap byte and mirrored timestamp fraction plus the
context clean/dirty evidence. It allocates no ghost state. Context and map
capacities are obtained from the same machine/ownership bundle.

The access contract exposes the existing physical byte and a closing wand
for any new byte. Only the persistent claim is retained by that wand; no
linear byte is duplicated. Agreement first equates the existential physical
pages using native mapping agreement, then compares the actual byte camera.
Identity access rewrites the physical address with the owned pin. A word
retains virtual alignment and all eight individual virtual byte resources.
The initial word law only weakens tiers; a physical word bridge still needs
explicit same-page and offset arithmetic.

The five pure and seven native contracts do not assert translation success,
boot installation, text/RX ownership, virtual free slots or a supervisor
capability. Those remain required layers before the full source mycpu
contract can close. The source's positive virtual half is preserved here,
even though the operational address wrapper also handles negative canonical
addresses and rejects noncanonical addresses.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
