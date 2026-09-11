# Full push_off instruction-resource family

The complete CodePushOff.v source listing has 24 instructions at offsets
00,02,04,06,08,0a,0e,10,14,16,18,1c,1e,20,22,24,26,28,2a,2c,30,34,36,38.
Five are four-byte base instructions (CSRRCI, three JALs and SRLI); nineteen
are compressed. The body is exactly58 bytes at imported push_off0x80000b80.
Defs records every raw encoding, decoded compressed/base constructor and
source normalized constructor. In particular C.LW is signed, C.ADDIW
wraps32, and the final C.J immediate is -32, returning to the +0x18 suffix.

The old two-call producer had the explicit limited scope +0x10/+0x18. Its
Fin3 extension retains both entries and adds +0x2c: immediate3342, encoding
0x50f000ef. The full source zero-depth branch takes BEQZ from+0x16 to+0x2c,
saves the old SIE bit to intena, and jumps back to the shared suffix.
ProofPushOff.v:284–405 and617–910 supply this control/resource context;
stale prose immediates in that file are superseded by actual theorem terms.

The byte-resource family preserves the input text's original tier. It
returns actual KptFetch.instrBytes at each indexed PC and exact F_Base or
F_RVC result. No default source lookup, decoder success, physical-memory
value, translation correctness or execution WP is a premise. Source
InstrBytes.v:33–65 requires a four-byte window for four-aligned compressed
instructions, despite their two-byte result. Base instructions always own
four bytes, including the two-half-fetch CSR at+0x0a.

Consequently the complete fetch ownership extends through offset59.
The final C.J at+0x38 is four-aligned and its full fetch word is0x1101b7c5:
the high half is acquire's first actual0x1101 instruction at0x80000bba.
The explicit60-byte literal and successful source-map lookup contracts
include these two lookahead bytes. They do not add them to push_off's
58-byte instruction body. Overlapping fetch windows use persistent text;
no linear overlapping ownership is spent twice.

All twelve approved pure contracts and the native code-resource contract
are implemented in five modules (871 jobs). The strict owner audit checks
all72 physical declarations and full type/opaque/constructor cones, with
standard three axioms, no unsafe/partial dependencies and zero exclusions. Pure contracts cover the exact body
partition, width/alignment/opcode classification,60-byte fetch bound,
lookahead, literal source bytes, full fetch-word bytes, low-half agreement,
base encoding and all three call-site connections. The normalized/decoded
syntax tables remain a source inventory: actual
ext_decode/ext_decode_compressed certificates and ExecuteAs normalization
will be a separately reviewed later proof, with explicit register read
requirements. No huge generic decoder is executed here.

Whole push_off correctness, the fused SIE CSR operation, four-byte
loads/stores, context movement and enabled-arm transitions remain open.
The only existing modules changed are the authorized call-site family
Defs/Spec and its scope documentation; existing proof bodies are unchanged.
No umbrella, source/generated semantics or other owner module is edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
