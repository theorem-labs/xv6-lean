import MachCSL.Logic.DiskSpec
import MachCSL.Devices.Virtio.Proofs

namespace MachCSL.Logic.Disk
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Devices.Virtio
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

theorem diskRead_cons (disk : Devices.Virtio.Disk) (offset : Int) (n : Nat) :
    disk_read disk offset (n + 1) = disk offset :: disk_read disk (offset + 1) n := by
  simp only [disk_read, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 1
    omega

theorem diskRead_lookup (disk : Devices.Virtio.Disk) (offset : Int) (n j : Nat)
    (bound : j < n) : (disk_read disk offset n)[j]? = some (disk (offset + j)) := by
  simp [disk_read, List.getElem?_range bound]

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance imageByte_timeless γ offset byte : Timeless (imageByte capacity γ offset byte) := by
  letI := capacity.image
  unfold imageByte
  infer_instance
instance imageBytes_timeless γ offset bytes : Timeless (imageBytes capacity γ offset bytes) := by
  unfold imageBytes
  infer_instance
instance mapAuth_timeless γ map : Timeless (mapAuth capacity γ map) := by
  letI := capacity.image
  unfold mapAuth
  infer_instance
instance imageAuthSized_timeless γ size disk : Timeless (imageAuthSized capacity γ size disk) := by
  unfold imageAuthSized
  infer_instance

theorem imageBytes_nil (γ : GName) (offset : Int) : imageBytes capacity γ offset [] ⊣⊢ emp :=
  by unfold imageBytes; exact .rfl

theorem imageBytes_cons (γ : GName) (offset : Int) (byte : Byte) (bytes : List Byte) :
    imageBytes capacity γ offset (byte :: bytes) ⊣⊢
      imageByte capacity γ offset byte ∗ imageBytes capacity γ (offset + 1) bytes := by
  unfold imageBytes
  rw [BigSepL.bigSepL_cons.to_eq]
  have zero : offset + ((0 : Nat) : Int) = offset := by omega
  rw [zero]
  have same : (fun (j : Nat) (byte : Byte) => imageByte capacity γ (offset + ((j + 1 : Nat) : Int)) byte) =
      (fun (j : Nat) (byte : Byte) => imageByte capacity γ (offset + 1 + (j : Int)) byte) := by
    funext j byte
    congr 1
    omega
  rw [same]
  exact .rfl

theorem imageByte_lookup (γ : GName) (map : ImageMap Byte) (offset : Int) (byte : Byte) :
    iprop(⊢ mapAuth capacity γ map -∗ imageByte capacity γ offset byte -∗
      ⌜map[offset]? = some byte⌝) := by
  letI := capacity.image
  exact ghost_map_lookup

theorem imageBytes_read (γ : GName) (map : ImageMap Byte) (disk : Devices.Virtio.Disk)
    (offset : Int) (bytes : List Byte) (view : disk_view map disk) :
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes -∗
      ⌜disk_read disk offset bytes.length = bytes⌝) := by
  induction bytes generalizing offset with
  | nil =>
    iintro _ _
    ipureintro
    rfl
  | cons byte bytes ih =>
    iintro Ha Hbytes
    icases (imageBytes_cons capacity γ offset byte bytes).mp $$ Hbytes with ⟨Hb, Hbs⟩
    ihave %head := imageByte_lookup capacity γ map offset byte $$ Ha Hb
    ihave %tail := ih (offset + 1) $$ Ha Hbs
    ipureintro
    simp only [List.length_cons, diskRead_cons, view offset byte head, tail]

theorem imageByte_update (γ : GName) (map : ImageMap Byte) (offset : Int) (byte byte' : Byte) :
    iprop(⊢ mapAuth capacity γ map -∗ imageByte capacity γ offset byte ==∗
      mapAuth capacity γ (insert map offset byte') ∗ imageByte capacity γ offset byte') := by
  letI := capacity.image
  exact ghost_map_update byte'

theorem imageByte_insert (γ : GName) (map : ImageMap Byte) (offset : Int) (byte : Byte)
    (fresh : map[offset]? = none) :
    iprop(⊢ mapAuth capacity γ map ==∗
      mapAuth capacity γ (insert map offset byte) ∗ imageByte capacity γ offset byte) := by
  letI := capacity.image
  exact ghost_map_insert offset byte fresh

theorem imageBytes_update_gen (γ : GName) (map : ImageMap Byte)
    (offset : Int) (bytes bytes' : List Byte) (lengths : bytes'.length = bytes.length) :
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗ imageBytes capacity γ offset bytes' ∗
      ⌜∀ (j : Nat) byte, bytes'[j]? = some byte → map'[offset + (j : Int)]? = some byte⌝ ∗
      ⌜∀ x : Int, (∀ j : Nat, j < bytes'.length → x ≠ offset + (j : Int)) →
        map'[x]? = map[x]?⌝) := by
  letI := capacity.image
  induction bytes' generalizing offset bytes map with
  | nil =>
    iintro Ha _
    imodintro
    iexists map
    iframe Ha
    rw [(imageBytes_nil capacity γ offset).to_eq]
    ipureintro
    exact ⟨True.intro, ⟨by simp, fun _ _ => rfl⟩⟩
  | cons byte' bytes' ih =>
    cases bytes with
    | nil => simp at lengths
    | cons byte bytes =>
      iintro Ha Hbytes
      icases (imageBytes_cons capacity γ offset byte bytes).mp $$ Hbytes with ⟨Hb, Hbs⟩
      imod imageByte_update capacity γ map offset byte byte' $$ Ha Hb with ⟨Ha, Hb⟩
      imod ih (insert map offset byte') (offset + 1) bytes (by simpa using lengths)
        $$ Ha Hbs with ⟨%map', Ha, Hbs, %inside, %outside⟩
      imodintro
      iexists map'
      iframe Ha
      rw [(imageBytes_cons capacity γ offset byte' bytes').to_eq]
      iframe Hb Hbs
      ipureintro
      constructor
      · intro j b present
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at present
          subst b
          simp only [Int.natCast_zero, Int.add_zero]
          rw [outside offset (by intro k hk; omega)]
          exact get?_insert_eq (m := map) (k := offset) (v := byte') rfl
        | succ j =>
          have shift : offset + ((j + 1 : Nat) : Int) = offset + 1 + (j : Int) := by omega
          rw [shift]
          exact inside j b present
      · intro x hx
        rw [outside x (by intro k hk; have := hx (k + 1) (by simpa using hk); omega)]
        exact get?_insert_ne (m := map) (k := offset) (k' := x) (v := byte')
          (by have := hx 0 (by simp); omega)

/-- The two source range-update clauses imply the actual total-disk write view. -/
theorem diskView_write_of_range (map map' : ImageMap Byte) (offset : Int) (bytes : List Byte)
    (inside : ∀ (j : Nat) byte, bytes[j]? = some byte → map'[offset + (j : Int)]? = some byte)
    (outside : ∀ x : Int, (∀ j : Nat, j < bytes.length → x ≠ offset + (j : Int)) →
      map'[x]? = map[x]?) (disk : Devices.Virtio.Disk) (view : disk_view map disk) :
    disk_view map' (disk_write disk offset bytes) := by
  intro x byte present
  by_cases lower : offset ≤ x
  · cases found : bytes[(x - offset).toNat]? with
    | some value =>
      have hit := inside _ _ found
      have address : offset + ((x - offset).toNat : Int) = x := by omega
      rw [address] at hit
      have eq := Option.some.inj (hit.symm.trans present)
      exact (disk_write_in disk offset bytes x value lower found).trans eq
    | none =>
      have out : ∀ j : Nat, j < bytes.length → x ≠ offset + (j : Int) := by
        intro j bound equal
        have idx : (x - offset).toNat = j := by omega
        rw [idx] at found
        have tooLarge := List.getElem?_eq_none_iff.mp found
        omega
      rw [outside x out] at present
      simpa [disk_write, lower, found] using view x byte present
  · rw [outside x (by intro j _; omega)] at present
    simpa [disk_write, lower] using view x byte present

theorem imageBytes_update (γ : GName) (map : ImageMap Byte)
    (offset : Int) (bytes bytes' : List Byte) (lengths : bytes'.length = bytes.length) :
    iprop(⊢ mapAuth capacity γ map -∗ imageBytes capacity γ offset bytes ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗ imageBytes capacity γ offset bytes' ∗
      ⌜∀ disk : Devices.Virtio.Disk, disk_view map disk →
        disk_view map' (disk_write disk offset bytes')⌝) := by
  iintro Ha Hbytes
  imod imageBytes_update_gen capacity γ map offset bytes bytes' lengths $$ Ha Hbytes
    with ⟨%map', Ha, Hbytes, %inside, %outside⟩
  imodintro
  iexists map'
  iframe Ha Hbytes
  ipureintro
  exact diskView_write_of_range map map' offset bytes' inside outside

theorem diskView_insert (map : ImageMap Byte) (disk : Devices.Virtio.Disk)
    (view : disk_view map disk) (offset : Int) : disk_view (insert map offset (disk offset)) disk := by
  intro x byte present
  change get? (insert map offset (disk offset)) x = some byte at present
  by_cases eq : offset = x
  · rw [get?_insert_eq eq] at present
    exact eq ▸ Option.some.inj present
  · rw [get?_insert_ne eq] at present
    exact view x byte present

theorem imageBytes_mint_dom (γ : GName) (map : ImageMap Byte) (disk : Devices.Virtio.Disk)
    (offset : Int) (n : Nat) (view : disk_view map disk)
    (fresh : ∀ j : Nat, j < n → map[offset + (j : Int)]? = none)
    (_sourcePremise : ∀ (x : Int) (byte : Byte), map[x]? = some byte → True) :
    iprop(⊢ mapAuth capacity γ map ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗
      imageBytes capacity γ offset (disk_read disk offset n) ∗ ⌜disk_view map' disk⌝ ∗
      ⌜∀ (x : Int) (byte : Byte), map'[x]? = some byte →
        map[x]? = some byte ∨ (offset ≤ x ∧ x < offset + (n : Int))⌝) := by
  induction n generalizing offset map with
  | zero =>
    iintro Ha
    imodintro
    iexists map
    iframe Ha
    simp only [disk_read, List.range_zero, List.map_nil]
    rw [(imageBytes_nil capacity γ offset).to_eq]
    ipureintro
    exact ⟨True.intro, view, fun _ _ h => .inl h⟩
  | succ n ih =>
    have headFresh : map[offset]? = none := by simpa using fresh 0 (by omega)
    have tailFresh : ∀ j : Nat, j < n →
        (insert map offset (disk offset))[offset + 1 + (j : Int)]? = none := by
      intro j bound
      change get? (insert map offset (disk offset)) _ = none
      rw [get?_insert_ne (by omega : offset ≠ offset + 1 + (j : Int))]
      have h := fresh (j + 1) (by omega)
      have shift : offset + ((j + 1 : Nat) : Int) = offset + 1 + (j : Int) := by omega
      change map[offset + 1 + (j : Int)]? = none
      simpa only [shift] using h
    iintro Ha
    imod imageByte_insert capacity γ map offset (disk offset) headFresh $$ Ha with ⟨Ha, Hb⟩
    imod ih (insert map offset (disk offset)) (offset + 1)
      (diskView_insert map disk view offset) tailFresh (by intros; trivial)
      $$ Ha with ⟨%map', Ha, Hbytes, %newView, %domain⟩
    imodintro
    iexists map'
    iframe Ha
    rw [diskRead_cons, (imageBytes_cons capacity γ offset (disk offset) _).to_eq]
    iframe Hb Hbytes
    ipureintro
    refine ⟨newView, ?_⟩
    intro x byte present
    rcases domain x byte present with old | range
    · by_cases eq : offset = x
      · right; omega
      · left
        change get? (insert map offset (disk offset)) x = some byte at old
        rwa [get?_insert_ne eq] at old
    · right; omega

theorem imageBytes_mint (γ : GName) (map : ImageMap Byte) (disk : Devices.Virtio.Disk)
    (offset : Int) (n : Nat) (view : disk_view map disk)
    (fresh : ∀ j : Nat, j < n → map[offset + (j : Int)]? = none) :
    iprop(⊢ mapAuth capacity γ map ==∗
      ∃ map' : ImageMap Byte, mapAuth capacity γ map' ∗
      imageBytes capacity γ offset (disk_read disk offset n) ∗ ⌜disk_view map' disk⌝) := by
  iintro Ha
  imod imageBytes_mint_dom capacity γ map disk offset n view fresh (by intros; trivial)
    $$ Ha with ⟨%map', Ha, Hbytes, %newView, _⟩
  imodintro
  iexists map'
  iframe Ha Hbytes
  ipureintro
  exact newView

theorem mapAuth_alloc_empty : iprop(⊢ |==> ∃ γ, mapAuth capacity γ (∅ : ImageMap Byte)) := by
  letI := capacity.image
  exact ghost_map_alloc_empty

theorem diskView_empty (disk : Devices.Virtio.Disk) : disk_view (∅ : ImageMap Byte) disk := by
  intro offset byte present
  have empty : (∅ : ImageMap Byte)[offset]? = none := get?_empty (M := ImageMap) (V := Byte) offset
  rw [empty] at present
  contradiction

theorem imageAuth_alloc (disk : Devices.Virtio.Disk) (n : Nat) :
    iprop(⊢ |==> ∃ γ, imageAuth capacity γ disk ∗
      imageBytes capacity γ 0 (disk_read disk 0 n)) := by
  imod mapAuth_alloc_empty capacity with ⟨%γ, Ha⟩
  imod imageBytes_mint capacity γ ∅ disk 0 n (diskView_empty disk)
    (by intro j _; exact get?_empty (M := ImageMap) (V := Byte) _) $$ Ha with ⟨%map, Ha, Hbytes, %view⟩
  imodintro
  iexists γ
  iframe Hbytes
  unfold imageAuth
  iexists map
  iframe Ha
  ipureintro
  exact view

theorem diskRead_agree (disk disk' : Devices.Virtio.Disk) (n : Nat)
    (equal : disk_read disk 0 n = disk_read disk' 0 n) (x : Int)
    (bound : 0 ≤ x ∧ x < (n : Int)) : disk x = disk' x := by
  have h1 := diskRead_lookup disk 0 n x.toNat (by omega)
  have h2 := diskRead_lookup disk' 0 n x.toNat (by omega)
  rw [equal] at h1
  have eq := Option.some.inj (h1.symm.trans h2)
  have cast : 0 + (x.toNat : Int) = x := by omega
  simpa only [cast] using eq

theorem imageAuthSized_alloc (disk : Devices.Virtio.Disk) (n : Nat) :
    iprop(⊢ |==> ∃ γ, imageAuthSized capacity γ n disk ∗
      imageBytes capacity γ 0 (disk_read disk 0 n)) := by
  imod mapAuth_alloc_empty capacity with ⟨%γ, Ha⟩
  imod imageBytes_mint_dom capacity γ ∅ disk 0 n (diskView_empty disk)
    (by intro j _; exact get?_empty (M := ImageMap) (V := Byte) _) (by intros; trivial)
    $$ Ha with ⟨%map, Ha, Hbytes, %view, %domain⟩
  imodintro
  iexists γ
  iframe Hbytes
  unfold imageAuthSized
  iexists map
  iframe Ha
  ipureintro
  refine ⟨view, ?_⟩
  intro offset byte present
  rcases domain offset byte present with empty | bound
  · have absent : (∅ : ImageMap Byte)[offset]? = none := get?_empty (M := ImageMap) (V := Byte) offset
    rw [absent] at empty
    contradiction
  · simpa only [Int.zero_add] using bound

theorem imageAuthSized_read (γ : GName) (n : Nat) (disk : Devices.Virtio.Disk)
    (offset : Int) (bytes : List Byte) :
    iprop(⊢ imageAuthSized capacity γ n disk -∗ imageBytes capacity γ offset bytes -∗
      ⌜disk_read disk offset bytes.length = bytes⌝) := by
  unfold imageAuthSized
  iintro ⟨%map, Ha, %view, _⟩ Hbytes
  iapply imageBytes_read capacity γ map disk offset bytes view $$ Ha Hbytes

/-- Whole-range ownership and the authority's domain bound permit any target total image. -/
theorem imageAuthSized_write (γ : GName) (n : Nat) (disk disk' : Devices.Virtio.Disk) :
    iprop(⊢ imageAuthSized capacity γ n disk -∗
      imageBytes capacity γ 0 (disk_read disk 0 n) ==∗
      imageAuthSized capacity γ n disk' ∗ imageBytes capacity γ 0 (disk_read disk' 0 n)) := by
  unfold imageAuthSized
  iintro ⟨%map, Ha, %_view, %domain⟩ Hbytes
  imod imageBytes_update_gen capacity γ map 0 (disk_read disk 0 n) (disk_read disk' 0 n)
    (by simp) $$ Ha Hbytes with ⟨%map', Ha, Hbytes, %inside, %outside⟩
  have newDomain : ∀ (x : Int) (byte : Byte), map'[x]? = some byte →
      0 ≤ x ∧ x < (n : Int) := by
    intro x byte present
    by_cases bound : 0 ≤ x ∧ x < (n : Int)
    · exact bound
    · have out : ∀ j : Nat, j < (disk_read disk' 0 n).length → x ≠ 0 + (j : Int) := by
        intro j hj
        simp only [disk_read_length] at hj
        omega
      rw [outside x out] at present
      exact domain x byte present
  imodintro
  iframe Hbytes
  iexists map'
  iframe Ha
  ipureintro
  refine ⟨?_, newDomain⟩
  intro x byte present
  have bound := newDomain x byte present
  have read := diskRead_lookup disk' 0 n x.toNat (by omega)
  have cast : 0 + (x.toNat : Int) = x := by omega
  rw [cast] at read
  have hit := inside x.toNat (disk' x) read
  rw [cast] at hit
  exact Option.some.inj (hit.symm.trans present)

/-- The full pinned disk-image contract, proved using the explicit native capacity. -/
theorem diskSpec : DiskSpec capacity where
  readCons := diskRead_cons
  readLength := disk_read_length
  readLookup := diskRead_lookup
  readAgree := diskRead_agree
  bytesCons := imageBytes_cons capacity
  bytesRead := imageBytes_read capacity
  bytesUpdateGen := imageBytes_update_gen capacity
  bytesUpdate := imageBytes_update capacity
  bytesMint := imageBytes_mint capacity
  bytesMintDom := imageBytes_mint_dom capacity
  alloc := imageAuth_alloc capacity
  sizedAlloc := imageAuthSized_alloc capacity
  sizedRead := imageAuthSized_read capacity
  sizedWrite := imageAuthSized_write capacity

end MachCSL.Logic.Disk
