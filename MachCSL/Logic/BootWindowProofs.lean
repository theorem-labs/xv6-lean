import MachCSL.Logic.BootWindowDefs

namespace MachCSL.Logic.BootWindow
open Iris Iris.Std Iris.BI MachCSL.Memory
open Iris.Std.PartialMap

theorem keys_nodup (a : PhysicalAddress) (n : Nat) (bound : n ≤ 2 ^ 64) : (keys a n).Nodup := by
  unfold keys
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := n))
  intro i j hi hj ne same
  exact ne (TsoStore.addressAdd_injective_below a i j
    (Nat.lt_of_lt_of_le (List.mem_range.mp hi) bound)
    (Nat.lt_of_lt_of_le (List.mem_range.mp hj) bound) same)

theorem extract_bytes {GF : BundledGFunctors} (capacity : Tso.Capacity GF) (γ : GName)
    (m : Tso.AddressMap Byte) (a : PhysicalAddress) (n : Nat) (word : BitVec (8 * n))
    (bound : n ≤ 2 ^ 64)
    (ram : ∀ j, j < n → Tso.AddrIsRAM (addressAdd a j))
    (lookup : ∀ j, j < n → get? m (addressAdd a j) = some (nthByte word j)) :
    mapBytes capacity γ m ⊢
      TsoRead.byteWindow capacity γ a n (.own 1) word ∗
        mapBytes capacity γ (JalBootResources.deleteKeys m (keys a n)) := by
  let value : PhysicalAddress → Byte := fun key => (get? m key).getD 0#8
  have value_nth j (hj : j < n) : value (addressAdd a j) = nthByte word j := by
    simp only [value, lookup j hj, Option.getD_some]
  have found key (hk : key ∈ keys a n) : get? m key = some (value key) := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have hj := List.mem_range.mp hj
    rw [value_nth j hj]
    exact lookup j hj
  iintro H
  iunfold mapBytes at H
  ihave ⟨Hbytes, Hrest⟩ := JalBootResources.extract_keys
    (fun key v => Tso.byteElem capacity γ (.own 1) key v)
    (keys a n) (keys_nodup a n bound) value m found $$ H
  unfold mapBytes
  iframe Hrest
  unfold TsoRead.byteWindow
  isimp only [keys, BigSepL.bigSepL_map] at Hbytes
  iapply BigSepL.bigSepL_mono $$ Hbytes
  intro j k present
  have hk : k < n := List.mem_range.mp (List.mem_of_getElem? present)
  iintro H
  isimp only [value_nth k hk] at H
  unfold Tso.physBytePointsto
  iframe H
  ipureintro
  exact ram k hk

theorem extract_times {GF : BundledGFunctors} (capacity : Tso.Capacity GF) (γ : GName)
    (m : Tso.AddressMap Tso.TimestampElem) (a : PhysicalAddress) (n t : Nat)
    (bound : n ≤ 2 ^ 64)
    (lookup : ∀ j, j < n → get? m (addressAdd a j) = some (t, Tso.payNone)) :
    mapTimes capacity γ m ⊢ timeWindow capacity γ a n t ∗
      mapTimes capacity γ (JalBootResources.deleteKeys m (keys a n)) := by
  have found key (hk : key ∈ keys a n) : get? m key = some (t, Tso.payNone) := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    exact lookup j (List.mem_range.mp hj)
  iintro H
  iunfold mapTimes at H
  ihave ⟨Htimes, Hrest⟩ := JalBootResources.extract_keys
    (fun key v => Tso.timestampElem capacity γ (.own 1) key v)
    (keys a n) (keys_nodup a n bound) (fun _ => (t, Tso.payNone)) m found $$ H
  unfold mapTimes timeWindow
  iframe Hrest
  isimp only [keys, BigSepL.bigSepL_map] at Htimes
  iexact Htimes

/-- The removed window changes no lookup outside its modular address list. -/
theorem lookup_deleteKeys {V : Type} (m : Tso.AddressMap V) (selected : List PhysicalAddress)
    (a : PhysicalAddress) (outside : a ∉ selected) :
    get? (JalBootResources.deleteKeys m selected) a = get? m a := by
  induction selected generalizing m with
  | nil => rfl
  | cons key rest ih =>
    have different : key ≠ a := by intro eq; subst key; exact outside (by simp)
    have absent : a ∉ rest := by intro member; exact outside (by simp [member])
    rw [JalBootResources.deleteKeys, ih _ absent,
      Iris.Std.LawfulPartialMap.get?_delete_ne different]

theorem storedWindow_split {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF)
    (names : TsoStore.Names) (a : PhysicalAddress) (n : Nat) (word : BitVec (8 * n)) (t : Nat) :
    TsoStore.storedWindow capacity names a n word t ⊣⊢
      TsoRead.byteWindow capacity.heap.ledger names.tso.ledger.bytes a n (.own 1) word ∗
      timeWindow capacity.heap.ledger names.tso.ledger.timestamps a n t := by
  unfold TsoStore.storedWindow TsoStore.storedByte TsoRead.byteWindow timeWindow
  exact BigSepL.bigSepL_sep_eqv

theorem deleteKeys_append {V : Type} (m : Tso.AddressMap V) (xs ys : List PhysicalAddress) :
    JalBootResources.deleteKeys m (xs ++ ys) =
      JalBootResources.deleteKeys (JalBootResources.deleteKeys m xs) ys := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih (Iris.Std.PartialMap.delete m x)

theorem extract_stored {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF)
    (names : TsoStore.Names) (m : Tso.AddressMap Byte) (tm : Tso.AddressMap Tso.TimestampElem)
    (w : Word) (t : Nat) (bound : w.size ≤ 2 ^ 64)
    (ram : ∀ j, j < w.size → Tso.AddrIsRAM (addressAdd w.address j))
    (lookup : ∀ j, j < w.size → get? m (addressAdd w.address j) = some (nthByte w.value j))
    (times : ∀ j, j < w.size → get? tm (addressAdd w.address j) = some (t, Tso.payNone)) :
    iprop(mapBytes capacity.heap.ledger names.tso.ledger.bytes m ∗
      mapTimes capacity.heap.ledger names.tso.ledger.timestamps tm ⊢
      TsoStore.storedWindow capacity names w.address w.size w.value t ∗
      (mapBytes capacity.heap.ledger names.tso.ledger.bytes
        (JalBootResources.deleteKeys m (keys w.address w.size)) ∗
       mapTimes capacity.heap.ledger names.tso.ledger.timestamps
        (JalBootResources.deleteKeys tm (keys w.address w.size)))) := by
  iintro ⟨Hb, Ht⟩
  ihave ⟨Hword, Hb⟩ := extract_bytes capacity.heap.ledger names.tso.ledger.bytes m
    w.address w.size w.value bound ram lookup $$ Hb
  ihave ⟨Htime, Ht⟩ := extract_times capacity.heap.ledger names.tso.ledger.timestamps tm
    w.address w.size t bound times $$ Ht
  iframe Hb Ht
  iapply (storedWindow_split capacity names w.address w.size w.value t).mpr
  iframe

theorem extract_words {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF)
    (names : TsoStore.Names) (words : List Word) (t : Nat)
    (unique : (wordKeys words).Nodup)
    (bounds : ∀ w, w ∈ words → w.size ≤ 2 ^ 64)
    (ram : ∀ w, w ∈ words → ∀ j, j < w.size → Tso.AddrIsRAM (addressAdd w.address j))
    (m : Tso.AddressMap Byte) (tm : Tso.AddressMap Tso.TimestampElem)
    (lookup : ∀ w, w ∈ words → ∀ j, j < w.size →
      get? m (addressAdd w.address j) = some (nthByte w.value j))
    (times : ∀ w, w ∈ words → ∀ j, j < w.size →
      get? tm (addressAdd w.address j) = some (t, Tso.payNone)) :
    iprop(mapBytes capacity.heap.ledger names.tso.ledger.bytes m ∗
      mapTimes capacity.heap.ledger names.tso.ledger.timestamps tm ⊢
      ([∗list] w ∈ words, TsoStore.storedWindow capacity names w.address w.size w.value t) ∗
      (mapBytes capacity.heap.ledger names.tso.ledger.bytes
        (JalBootResources.deleteKeys m (wordKeys words)) ∗
       mapTimes capacity.heap.ledger names.tso.ledger.timestamps
        (JalBootResources.deleteKeys tm (wordKeys words)))) := by
  induction words generalizing m tm with
  | nil =>
    iintro H
    isplitl []
    · iapply BigSepL.bigSepL_nil.mpr; itrivial
    · exact .refl _
  | cons w ws ih =>
    have parts : (keys w.address w.size ++ wordKeys ws).Nodup := unique
    have nodup := List.nodup_append.mp parts
    have outside v (hv : v ∈ ws) j (hj : j < v.size) :
        addressAdd v.address j ∉ keys w.address w.size := by
      intro member
      have tailMember : addressAdd v.address j ∈ wordKeys ws :=
        List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
      exact nodup.2.2 _ member _ tailMember rfl
    have tailBound v hv := bounds v (List.mem_cons_of_mem _ hv)
    have tailRam v hv := ram v (List.mem_cons_of_mem _ hv)
    have tailLookup (v : Word) (hv : v ∈ ws) (j : Nat) (hj : j < v.size) :
        get? (JalBootResources.deleteKeys m (keys w.address w.size)) (addressAdd v.address j) =
          some (nthByte v.value j) := by
      rw [lookup_deleteKeys _ _ _ (outside v hv j hj)]
      exact lookup v (List.mem_cons_of_mem _ hv) j hj
    have tailTimes (v : Word) (hv : v ∈ ws) (j : Nat) (hj : j < v.size) :
        get? (JalBootResources.deleteKeys tm (keys w.address w.size)) (addressAdd v.address j) =
          some (t, Tso.payNone) := by
      rw [lookup_deleteKeys _ _ _ (outside v hv j hj)]
      exact times v (List.mem_cons_of_mem _ hv) j hj
    iintro H
    ihave ⟨Hw, Hrest⟩ := extract_stored capacity names m tm w t (bounds w (by simp))
      (ram w (by simp)) (lookup w (by simp)) (times w (by simp)) $$ H
    ihave ⟨Hws, Hrest⟩ := ih nodup.2.1 tailBound tailRam _ _ tailLookup tailTimes $$ Hrest
    simp only [wordKeys, List.flatMap_cons, deleteKeys_append]
    iframe Hrest
    iapply BigSepL.bigSepL_cons.mpr
    iframe

end MachCSL.Logic.BootWindow
