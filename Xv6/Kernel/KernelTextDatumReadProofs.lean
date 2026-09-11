import Xv6.Kernel.KernelTextDatumWindowProofs

namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- This is the source pristine read using just its heap and TSO legs. -/
theorem pristine_byte_read era g a dq value :
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap a dq value -∗
      pristine capacity era a -∗ ⌜∀ agent view, read g.image g.log agent view a = some value⌝) := by
  unfold heapAt Era.heapInterpAt
  iintro ⟨%memory,Hheap,%rep⟩ Htso ⟨Hb,_⟩ Hpristine
  have heapValid := MachCSL.Logic.Heap.valid capacity.machine.era.heap ⟨era.heap,era.metadata⟩ memory a dq value
  rw [MachCSL.Logic.Heap.pointsto_eq_byteElem] at heapValid
  ihave %lookup := heapValid $$ Hheap Hb
  have timestampValid : iprop(⊢ tsoAt capacity era g -∗ pristine capacity era a -∗
      ⌜Tso.TimestampOK g.image g.memory g.log a (0, Tso.payNone)⌝) := by
    exact Tso.Interp.tsoInterpAt_timestamp_valid capacity.machine.era.tso era.tsoNames era.imageBytes g a .discard (0,Tso.payNone)
  ihave %valid := timestampValid $$ Htso Hpristine
  obtain ⟨actual,hm,latest⟩ := Tso.timestampOK_latest valid
  have equal : actual = value := by
    have hb : g.memory a = some value := by rw [← rep]; exact lookup
    exact Option.some.inj (hm.symm.trans hb)
  subst actual
  ipureintro
  intro agent view
  exact read_of_latest g.image g.log agent view a 0 value latest (visible_zero _ _ _)

theorem pristine_window_read era g a n dq word :
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗ physicalWindow capacity era a n dq word -∗
      pristineWindow capacity era a n -∗ ⌜∀ agent view, ReadsBytes g.image g.log agent view a n word⌝) := by
  unfold physicalWindow pristineWindow TsoRead.byteWindow TsoRead.pristineWindow
  iintro Hheap Htso Hbytes Hpristine
  iapply pure_forall.mpr
  iintro %agent
  iapply pure_forall.mpr
  iintro %view
  unfold ReadsBytes
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %bound
  have present : (List.range n)[j]? = some j := by simp [bound]
  ihave Hb := BigSepL.bigSepL_lookup present $$ Hbytes
  ihave Hp := BigSepL.bigSepL_lookup present $$ Hpristine
  ihave %reads := pristine_byte_read capacity era g (addressAdd a j) dq (nthByte word j) $$ Hheap Htso Hb Hp
  ipureintro
  exact reads agent view

theorem read_identity era g va n dq word :
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗ window capacity era .identity va n dq word -∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ window capacity era .identity va n dq word ∗
      ⌜∀ agent view, ReadsBytes g.image g.log agent view va n word⌝) := by
  iintro Hheap Htso Hword
  ihave ⟨Hbytes,Hpristine,Hclose⟩ := identity_access capacity era va n dq word $$ Hword
  ihave %reads := pristine_window_read capacity era g va n dq word $$ Hheap Htso Hbytes Hpristine
  ihave Hword := Hclose $$ Hbytes
  iframe Hheap Htso Hword
  ipureintro; exact reads

theorem read_full era tier g va n dq word (positive : 0 < n) (page : SamePage va n) :
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗ window capacity era tier va n dq word -∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ window capacity era tier va n dq word ∗
      ∃ ppn, claims capacity era tier va n ppn ∗
        ⌜∀ agent view, ReadsBytes g.image g.log agent view (physical ppn va) n word⌝) := by
  iintro Hheap Htso Hword
  ihave ⟨%ppn,Hclaims,Hbytes,Hpristine,Hclose⟩ := window_access capacity era tier va n dq word positive page $$ Hword
  ihave %reads := pristine_window_read capacity era g (physical ppn va) n dq word $$ Hheap Htso Hbytes Hpristine
  ihave Hword := Hclose $$ Hbytes
  iframe Hheap Htso Hword
  iexists ppn
  iframe Hclaims
  ipureintro; exact reads

theorem actualWindow : WindowSpec capacity :=
  ⟨window_access capacity,window_close capacity,window_head capacity,identity_access capacity,
    split_four capacity,context_identity capacity,context_full capacity,read_identity capacity,read_full capacity⟩

end Xv6.Kernel.KernelTextDatum
