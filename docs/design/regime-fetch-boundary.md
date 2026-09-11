# Fetch on the actual source register packet

RegimeFetch links generic instruction fetch to the exact disabled source
register packet at MycpuRegimeShell.sourceShares. Config is the existing
source-specialized KptJal.Config; the input code is actual same-tier
KptFetch.instrBytes. It can describe either base or compressed successful
classification. No new primitive, model change or slot-selection oracle
is introduced.

BareJal.partition already opens the existential owned SATP and PMP cells,
patches only their synthetic register-file projections, and partitions9
fetch cells plus44 remaining cells. Its native fetch_config combines the
actual slot facts and packet MsFacts. The new BareFetch executes all
classification paths and returns its9 cells. Reversing the same partition
restores the original common50 packet and actual Bare slot; the synthetic
patch never becomes a claim about unowned control-file projections.

The KPT arm borrows7 common cells plus its separately folded4-cell residue
using MycpuKptFetch.packet_partition. Existing configuration projection and
actual KptFetch.wp_fetch execute all hit/miss/A-D/read branches. Exact
traceReservation and receipts remain; running and the other43 cells are
framed. The public Trace type differs by actual regime, so no Bare trace is
silently interpreted as an Sv39 outcome. Each arm retains the original
code tier, literal frame and complete packet values. Admits excludes the
unsupported Bare/full pairing.

The guard monotonicity contract uses the existing linear fold map in each
arm. Every view/outcome retains its scope inside actual guards; it is not
assumed globally. The only WP input to native fetch is its genuine final
continuation. The rule does not yet decode or execute instructions or
establish source boot reachability.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
