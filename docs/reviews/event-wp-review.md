# Native event-plan fold review

Codex coordinator review: PASS for the stated finite-plan rule. Reviewed all four
`EventWP` modules and the component status against the actual register/RAM WP
interfaces and typed register ownership definitions.

The initial split deletes precisely two map keys and returns both full pin cells;
every other register remains in CPU ownership. Dependent typed writes rebuild the
same map with the exact updated value. Each pin read branches independently over
all typed results, so a plan does not freeze asynchronously driven pins. Plan post
register files describe the owned table; the two ignored pin entries are not
claims about physical hardware.

The induction calls a proved native WP for every event. RAM requests require
nondevice/nonexclusive checks and actual byte/pristine timestamp resources with
restoration, not an assumed execution or successor-preservation contract. The
linked rule handles all TSO views. Bind composition remains at the event-tree
level. The final continuation is explicitly a WP of the actual pure hart node,
whose operational meaning is cycle restart; it is never mistaken for a language
value or discarded to manufacture an infinite-loop theorem.

The concrete registry link supplies both callee implementations. The component
build and 69-declaration physical-module audit passed with standard foundational
axioms only and no unsafe/partial dependency. Integration additionally checks the
full implementation and statement dependency cones. Actual cycle-plan closure,
concrete code-resource access, restart preservation, and global adequacy remain
separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
