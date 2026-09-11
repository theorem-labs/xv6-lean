# Virtual word access to the physical context word

This implements the word-level resource bridge required by TsoCtx.v
845–940 and the aligned memory leaves. KernelDatum retains the exact source
virtual word definition: virtual eight-byte alignment and eight individually
mapped context bytes. Defs/Spec were independently approved; all five modules now compile
(658 jobs), with a full 45-declaration audit. Complete independent implementation review also passes.

Four pure contracts prove an aligned eight-byte window stays in its page,
all eight virtual addresses have the same VPN, PPN/offset reconstruction
commutes with each byte offset, and the physical word is aligned. These
facts quantify over all 64-bit virtual addresses; eight-byte alignment
prevents this window from wrapping at 2^64. No identity pin or actual
translation result is a premise.

The native access theorem derives one physical PPN using the eight
persistent claims and map agreement. It returns those exact claims and the
actual existing physical context word, together with a closing wand for
any replacement word. The closing wand keeps only persistent claims;
physical bytes and mirrored timestamp fractions are neither duplicated nor
reallocated. A separate close contract and head-claim projection expose
those useful interfaces. The mapping, context, era and tier are unchanged.

This is resource access. KptAddress and the future actual memory wrappers
still pay operational translation and physical memory events, including
hardware A/D updates. Virtual free stack slots and text RX resources are
separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
