import Xv6.Kernel.KernelTextDatumDefs

namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  text_ram : ∀ pa, AddrIsText pa → Tso.AddrIsRAM pa
  text_end_symbol : (textEnd : Int) = Xv6.Generated.KernelMaps.Symbols.etext
  trampoline_text : ∀ j : Nat, j < 4096 →
    AddrIsText (BitVec.ofInt 64 (Xv6.Generated.KernelMaps.Symbols.trampoline + j))
  page_two : ∀ va, va.toNat % 2 = 0 → SamePage va 2
  page_four : ∀ va, va.toNat % 4 = 0 → SamePage va 4
  vpn_offset : ∀ va n j, SamePage va n → j < n → vpn (addressAdd va j) = vpn va
  physical_offset : ∀ va ppn n j, SamePage va n → j < n →
    physical ppn (addressAdd va j) = addressAdd (physical ppn va) j
  low_bytes : ∀ word j, j < 2 → nthByte (lowHalf word) j = nthByte word j
  high_bytes : ∀ word j, j < 2 → nthByte (highHalf word) j = nthByte word (2 + j)

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  pristine_persistent : ∀ era pa, Persistent (pristine capacity era pa)
  pristine_timeless : ∀ era pa, Timeless (pristine capacity era pa)
  claim_persistent : ∀ era tier va ppn, Persistent (claim capacity era tier va ppn)
  claim_timeless : ∀ era tier va ppn, Timeless (claim capacity era tier va ppn)
  byte_persistent : ∀ era tier va value, Persistent (byte capacity era tier va .discard value)
  byte_timeless : ∀ era tier va dq value, Timeless (byte capacity era tier va dq value)
  window_persistent : ∀ era tier va n word, Persistent (window capacity era tier va n .discard word)
  window_timeless : ∀ era tier va n dq word, Timeless (window capacity era tier va n dq word)
  claim_agree : ∀ era tier tier' va ppn ppn',
    iprop(⊢ claim capacity era tier va ppn -∗ claim capacity era tier' va ppn' -∗ ⌜ppn = ppn'⌝)
  access : ∀ era tier va dq value,
    iprop(byte capacity era tier va dq value ⊢ ∃ ppn,
      claim capacity era tier va ppn ∗ rawByte capacity era (physical ppn va) dq value ∗
      pristine capacity era (physical ppn va) ∗
      (rawByte capacity era (physical ppn va) dq value -∗ byte capacity era tier va dq value))
  close : ∀ era tier va ppn dq value,
    iprop(⊢ claim capacity era tier va ppn -∗ rawByte capacity era (physical ppn va) dq value -∗
      pristine capacity era (physical ppn va) -∗ byte capacity era tier va dq value)
  pin_access : ∀ era tier va ppn dq value,
    iprop(⊢ KptGhost.mapAt capacity.ghost era.kernelMap (vpn va) ppn .rx -∗
      byte capacity era tier va dq value -∗
      claim capacity era tier va ppn ∗ rawByte capacity era (physical ppn va) dq value ∗
      pristine capacity era (physical ppn va) ∗
      (rawByte capacity era (physical ppn va) dq value -∗ byte capacity era tier va dq value))
  canonical : ∀ era tier va dq value,
    iprop(byte capacity era tier va dq value ⊢ ⌜KernelDatum.Positive va⌝)
  code_text : ∀ era tier va dq value,
    iprop(byte capacity era tier va dq value ⊢ ∃ ppn, claim capacity era tier va ppn)
  valid : ∀ era tier g va dq value,
    iprop(⊢ heapAt capacity era g -∗ byte capacity era tier va dq value -∗
      ∃ ppn, claim capacity era tier va ppn ∗ ⌜g.memory (physical ppn va) = some value⌝)
  agree : ∀ era tier tier' va dq dq' value value',
    iprop(⊢ byte capacity era tier va dq value -∗ byte capacity era tier' va dq' value' -∗
      ⌜value = value'⌝)
  mono : ∀ era tier tier' va dq value, KernelDatum.Tier.Le tier tier' →
    iprop(byte capacity era tier va dq value ⊢ byte capacity era tier' va dq value)
  persist : ∀ era tier va dq value,
    iprop(byte capacity era tier va dq value ⊢ |==> byte capacity era tier va .discard value)

/-- Same-page extraction is conditional; the virtual window itself may cross
pages. Two- and four-byte aligned windows discharge this guard geometrically.
The split keeps a page-crossing base instruction's two physical reads separate. -/
structure WindowSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  access : ∀ era tier va n dq word, 0 < n → SamePage va n →
    iprop(window capacity era tier va n dq word ⊢ ∃ ppn,
      claims capacity era tier va n ppn ∗ physicalWindow capacity era (physical ppn va) n dq word ∗
      pristineWindow capacity era (physical ppn va) n ∗
      (physicalWindow capacity era (physical ppn va) n dq word -∗ window capacity era tier va n dq word))
  close : ∀ era tier va n ppn dq word, SamePage va n →
    iprop(⊢ claims capacity era tier va n ppn -∗ physicalWindow capacity era (physical ppn va) n dq word -∗
      pristineWindow capacity era (physical ppn va) n -∗ window capacity era tier va n dq word)
  head : ∀ era tier va n ppn, 0 < n →
    iprop(claims capacity era tier va n ppn ⊢ claim capacity era tier va ppn)
  identity_access : ∀ era va n dq word,
    iprop(window capacity era .identity va n dq word ⊢
      physicalWindow capacity era va n dq word ∗ pristineWindow capacity era va n ∗
      (physicalWindow capacity era va n dq word -∗ window capacity era .identity va n dq word))
  split_four : ∀ era tier va dq (word : BitVec 32),
    iprop(window capacity era tier va 4 dq word ⊣⊢
      window capacity era tier va 2 dq (lowHalf word) ∗
      window capacity era tier (addressAdd va 2) 2 dq (highHalf word))
  context_identity : ∀ era ξ va n word,
    iprop(window capacity era .identity va n .discard word ⊢ contextWindow capacity era ξ va n word)
  context_full : ∀ era tier ξ va n word, 0 < n → SamePage va n →
    iprop(window capacity era tier va n .discard word ⊢ ∃ ppn,
      claims capacity era tier va n ppn ∗ contextWindow capacity era ξ (physical ppn va) n word)
  read_identity : ∀ era g va n dq word,
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗ window capacity era .identity va n dq word -∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ window capacity era .identity va n dq word ∗
      ⌜∀ agent view, ReadsBytes g.image g.log agent view va n word⌝)
  read_full : ∀ era tier g va n dq word, 0 < n → SamePage va n →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗ window capacity era tier va n dq word -∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ window capacity era tier va n dq word ∗
      ∃ ppn, claims capacity era tier va n ppn ∗
        ⌜∀ agent view, ReadsBytes g.image g.log agent view (physical ppn va) n word⌝)

end Xv6.Kernel.KernelTextDatum
