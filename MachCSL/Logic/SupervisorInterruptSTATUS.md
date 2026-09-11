# Native supervisor interrupt suppression

The four Logic/SupervisorInterrupt modules own precisely the four source fractional cells needed for dispatch: misa, mstatus, mie and mideleg. Shares are independent. The predicate registers combines those cells with the source S-bit/delegation/SIE facts; it is not a replacement for the full sconf, SIE ghost or translation capability.

The generated mip read and both external pins use universal readAny branches and need no ownership. The pending value remains arbitrary. All ten actual reads are retained, including the two status reads in the eager Lean tree. The partial plan and native wp_dispatch restore the same fractional cells and configuration to the actual same-generation continuation. Unowned symbolic table fields carry no assertion about physical register or pin stability.

Source SmodeCore.v:1197–1224 supplies the exact four-cell resource boundary; the checked generated behavior is detailed in the Machine/SupervisorInterrupt status and review. The plan does not hide the known Rocq/Lean short-circuit event difference or establish full cross-backend correspondence. It does not enter a trap handler or prove a complete supervisor cycle/function.

Validation: 436 build jobs passed. Independent source review and full opaque/type/constructor audit pass all 45 logical declarations, with standard three axioms and zero exclusions. See docs/reviews/supervisor-interrupt-native-peer-review.md. The implementation introduces no new camera or allocation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
