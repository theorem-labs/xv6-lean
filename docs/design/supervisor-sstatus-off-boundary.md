# Source-generic disabled sstatus normalization

The completed component proves the actual `legalize_sstatus` stage of
`CSRRCI sstatus,2,x15`. The surrounding CSR checks, register reads/writes,
destination assignment and instruction WP remain the coordinator's separate
component. All eleven approved contracts are discharged by nativeSpec. The six-module
implementation builds successfully in 351 jobs. The strict physical-origin
audit checks 606 declarations, including generated helper declarations and
complete type/opaque-body/constructor cones, with zero exclusions.

The actual pinned `hartSupports Ext_Zicfilp` is **true**
(`PlatformConfig.lean:2114`), and `legalize_mstatus` uses this support query
directly (`SysRegs.lean:1027–1034`). It does not query current MENVCFG.LPE.
Both MPELP and SPELP therefore survive legalization; the initial suggestion
that this stage clears them does not describe this model. The source
`WpGprCsrwCommon.v:247–288` symbolic `mstatus_legalized` likewise preserves
both fields. No zero-ELP hypothesis belongs in this contract.

`legalized old value` reproduces that source pure function: nominal MPP
or User fallback; source-supported S/U and virtual-memory fields; exact
FS/VS legalization, XS=Off, and dirty-derived SD. `writeValue ms` is the
actual lower_mstatus masked by complement of the 64-bit value 2. The
separately named `result ms` first lifts this S-view into ms, then applies
the pure legalized function. The proved finite RegisterPlan connects the actual generated monadic
legalizer to that pure value; no evaluation-success premise supplies the
correspondence.

The nine pure contracts are supported Zicfilp, lower-view SIE projection,
clear-already-off identity, lift/lower identity under source MsFacts,
legalized-self under those facts, composed result identity, MsFacts
preservation, SIE/SPP/SPIE/SPELP/MPELP preservation, and lower-view SIE=0.
The identity is the same source normalization argument as
`WpGprCsrwC.v:1362–1429,1675–1702`. Source `WpSieFlipBits.v:289–345`
provides the broader fact-preservation context; this first component is
explicitly the already-disabled arm.

Two finite-plan contracts retain the actual Sail free program. The generic
legalize_plan requires an arbitrary fractional misa cell in an arbitrary
footprint, the source hardware MISA value 0x800000000014112d, and arbitrary
old/new status words. It returns the pure legalized value and unchanged
register file. The off_plan additionally takes source MsFacts and SIE=0
and returns exactly the original status word. No mstatus register cell is
needed by this isolated helper because ms is already a function argument;
the top CSR component must own and perform its actual status read/write.
No privilege, MENVCFG, memory, reservation, namespace or new camera enters
this legalizer footprint.

Repeated reads remain intact. The generated sequence queries S for
TSR, U for TW, S for TVM, S for MXR, then all four eager virtual-memory
extension alternatives (each querying S), U for MPRV, nominal MPP (with
its value-dependent S/U read or User-fallback read), and S separately for
SPP, SPIE and SIE. In particular unsupported Sv32/Sv57 support tests do
not erase their eager MISA subevents. The owned footprint is one reusable
cell, not one read occurrence. The native finite plan proves the full generated trace without a supplied
evaluation-success premise.

Only new SupervisorSstatusOff files are owned here. No frozen family,
generated semantics or umbrella is modified. Implementation uses ordinary checked bit-extensional and register-plan
proofs; no custom axioms, native_decide or bv_decide. A generic
update-extracted-slice identity supplies all field update identities. The
plan splits all four MPP encodings and constructs a read node for every
actual eager query. Concrete regression certificates retain nonzero saved
ELP, SUM, SPP/SPIE, MIE/MPIE, UXL=3 and a reserved high bit, covering all
four MPP outcomes including invalid encoding 2 falling back to User.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
