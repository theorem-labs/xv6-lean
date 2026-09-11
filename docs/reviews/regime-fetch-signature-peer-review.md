# RegimeFetch signature review

PASS for the root-authored two-file checkpoint. Codex `artifact_audit` read RegimeFetchDefs/Spec and checked feasibility against BareJal's actual resource partition/config projection and MycpuKptFetch's actual packet partition/configuration, plus the full native BareFetch/KptFetch signatures.

The two contracts preserve exact source shares, original tier, actual regime, literal frame and typed receipts. Bare/full is excluded by Admits; the Bare branch uses owned existential SATP/PMP cells and restores them through the existing partition. The KPT branch retains the actual coherent residue, with reservation evolution determined by the real trace. The running context is used by Bare fetch and framed through KPT fetch. Both implementations can obtain the necessary MS facts from the actual packet; no caller-supplied execution success, hardware-config oracle or duplicated register resource is needed.

The guard-monotonicity contract maps genuine continuations through the existing exact per-regime guard folds. The proposed fetch contract is implementable using the existing native rules without strengthening the signature. This report approves the interface only; implementation and its audit are separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
