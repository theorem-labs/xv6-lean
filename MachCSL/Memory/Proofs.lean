import MachCSL.Memory.Defs

/-! First proof slice of the paper's production TSO model. The source mapping
and remaining obligations are in `MachCSL/Memory/STATUS.md`. -/
namespace MachCSL.Memory

variable {width : Nat}

@[simp] theorem visible_zero (h view : Nat) (log : WriteLog width) :
    visible h view log 0 = true := by simp [visible]

theorem visible_below (h view : Nat) (log : WriteLog width) (t : Nat)
    (ht : t ≤ view) : visible h view log t = true := by simp [visible, ht]

theorem visible_own (h view : Nat) (log : WriteLog width) (i : Nat)
    (m : Message width) (hm : log[i]? = some m) (ha : m.author = h) :
    visible h view log (i + 1) = true := by simp [visible, hm, ha]

theorem visible_mono (h view view' : Nat) (log : WriteLog width) (t : Nat)
    (hle : view ≤ view') (hv : visible h view log t = true) :
    visible h view' log t = true := by
  unfold visible at hv ⊢
  cases t with
  | zero => simp
  | succ i =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hv ⊢
    rcases hv with ht | ho
    · exact Or.inl (Nat.le_trans ht hle)
    · exact Or.inr ho

@[simp] theorem logByte_zero (img : ByteMap width) (log : WriteLog width) (a) :
    logByte img log 0 a = img a := rfl

@[simp] theorem readDown_zero (img : ByteMap width) (log : WriteLog width) (h view a) :
    readDown img log h view a 0 = img a := by simp [readDown]

theorem logByte_append_below (img : ByteMap width) (log : WriteLog width)
    (m : Message width) (t a) (ht : t ≤ log.length) :
    logByte img (log ++ [m]) t a = logByte img log t a := by
  cases t with
  | zero => rfl
  | succ i => simp only [logByte, List.getElem?_append_left (by omega : i < log.length)]

@[simp] theorem logByte_top (img : ByteMap width) (log : WriteLog width)
    (m : Message width) (a) :
    logByte img (log ++ [m]) (log.length + 1) a = msgByte m a := by
  simp [logByte]

theorem logByte_beyond (img : ByteMap width) (log : WriteLog width) (t a)
    (ht : log.length < t) : logByte img log t a = none := by
  cases t with
  | zero => omega
  | succ i => simp [logByte, List.getElem?_eq_none (by omega : log.length ≤ i)]

theorem readDown_total (img : ByteMap width) (log : WriteLog width) (h view a b n)
    (hi : img a = some b) : ∃ v, readDown img log h view a n = some v := by
  induction n with
  | zero => exact ⟨b, by simpa using hi⟩
  | succ n ih =>
    simp only [readDown]
    split
    · rename_i v he
      exact ⟨v, rfl⟩
    · exact ih

theorem read_total (img : ByteMap width) (log : WriteLog width) (h view a b)
    (hi : img a = some b) : ∃ v, read img log h view a = some v :=
  readDown_total img log h view a b log.length hi

/-- Forwarding is compulsory, not merely an allowed alternative. -/
theorem read_own_top (img : ByteMap width) (log : WriteLog width)
    (h a) (m : Message width) (v) (ha : m.author = h)
    (hb : msgByte m a = some v) (view) :
    read img (log ++ [m]) h view a = some v := by
  have hv : visible h view (log ++ [m]) (log.length + 1) = true :=
    visible_own h view (log ++ [m]) log.length m (by simp) ha
  simp [read, readDown, hv, hb]

@[simp] theorem flat_nil (img : ByteMap width) : flat img [] = img := rfl

@[simp] theorem flat_append (img : ByteMap width) (log : WriteLog width)
    (m : Message width) : flat img (log ++ [m]) = overlay m.bytes (flat img log) := by
  simp [flat, List.foldl_append]

theorem readDown_append_below (img : ByteMap width) (log : WriteLog width)
    (m : Message width) (h view view' a t)
    (hlen : t ≤ log.length) (hv : t ≤ view) (hv' : t ≤ view') :
    readDown img (log ++ [m]) h view' a t = readDown img log h view a t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hv1 := visible_below h view log (t + 1) hv
    have hv2 := visible_below h view' (log ++ [m]) (t + 1) hv'
    simp only [readDown, hv1, hv2, ↓reduceIte,
      logByte_append_below img log m (t + 1) a hlen]
    split
    · rfl
    · exact ih (by omega) (by omega) (by omega)

private theorem reverseInduction {α : Type} {P : List α → Prop}
    (nil : P []) (snoc : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  have aux : ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil => exact nil
    | cons y ys ih => simpa using snoc ys.reverse y ih
  simpa using aux xs.reverse

/-- At the top view all agents read the globally published byte map. -/
theorem read_top_flat (img : ByteMap width) (log : WriteLog width) (h a) :
    read img log h log.length a = flat img log a := by
  induction log using reverseInduction with
  | nil => simp [read]
  | snoc log m ih =>
    have hv := visible_below h (log.length + 1) (log ++ [m]) (log.length + 1)
      (Nat.le_refl _)
    simp only [read, List.length_append, List.length_singleton, readDown, hv,
      ↓reduceIte, logByte_top, flat_append, overlay]
    cases hm : msgByte m a with
    | some v => simp [msgByte] at hm; simp [hm]
    | none =>
      simp only [msgByte] at hm
      simp only [hm, Option.or]
      rw [readDown_append_below img log m h log.length (log.length + 1)
        a log.length (Nat.le_refl _) (Nat.le_refl _) (by omega)]
      exact ih

theorem fencePost_mono (h) (log : WriteLog width) (drain view) :
    view ≤ fencePost h log drain view := by
  cases drain <;> simp [fencePost, Nat.le_max_left]

theorem latest_append_new (img : ByteMap width) (log : WriteLog width)
    (m : Message width) (a v) (hb : msgByte m a = some v) :
    Latest img (log ++ [m]) a (log.length + 1) v := by
  refine ⟨by simpa using hb, ?_⟩
  intro t ht
  apply logByte_beyond
  simpa using ht

private theorem foldMax_le (xs : List Nat) (n : Nat) (h : ∀ x ∈ xs, x ≤ n) :
    xs.foldr Nat.max 0 ≤ n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

theorem ownPub_le (h) (log : WriteLog width) : ownPub h log ≤ log.length := by
  apply foldMax_le
  intro n hn
  obtain ⟨⟨m, i⟩, hi, rfl⟩ := List.mem_map.mp hn
  have hbound := List.snd_lt_of_mem_zipIdx hi
  dsimp at hbound ⊢
  split <;> omega

theorem fencePost_le_length (h) (log : WriteLog width) (drain view)
    (hv : view ≤ log.length) : fencePost h log drain view ≤ log.length := by
  have hp := ownPub_le h log
  cases drain <;> simp [fencePost] <;> omega

theorem visible_append (h view) (log : WriteLog width) (m : Message width) (t)
    (ht : t ≤ log.length) : visible h view (log ++ [m]) t = visible h view log t := by
  cases t with
  | zero => simp
  | succ i => simp only [visible, List.getElem?_append_left (by omega : i < log.length)]

theorem logByte_some_le (img : ByteMap width) (log : WriteLog width) (t a v)
    (hb : logByte img log t a = some v) : t ≤ log.length := by
  by_cases hn : t ≤ log.length
  · exact hn
  have hz := logByte_beyond img log t a (by omega)
  rw [hz] at hb
  contradiction

theorem latest_append_frame (img : ByteMap width) (log : WriteLog width)
    (m : Message width) (a t v) (hm : msgByte m a = none)
    (hl : Latest img log a t v) : Latest img (log ++ [m]) a t v := by
  refine ⟨?_, ?_⟩
  · rw [logByte_append_below img log m t a (logByte_some_le img log t a v hl.1)]
    exact hl.1
  · intro t' ht'
    by_cases hle : t' ≤ log.length
    · rw [logByte_append_below img log m t' a hle]
      exact hl.2 t' ht'
    · by_cases he : t' = log.length + 1
      · subst t'
        simpa using hm
      · apply logByte_beyond
        simp only [List.length_append, List.length_singleton]
        omega

theorem allOwn_nil (h) : AllOwn h ([] : WriteLog width) := by simp [AllOwn]

theorem allOwn_append (h) (log : WriteLog width) (m : Message width)
    (hl : AllOwn h log) (hm : m.author = h) : AllOwn h (log ++ [m]) := by
  intro m' hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact hl m' hmem
  · exact hm

theorem allOwn_visible (h view) (log : WriteLog width) (t)
    (hl : AllOwn h log) (ht : t ≤ log.length) : visible h view log t = true := by
  cases t with
  | zero => simp
  | succ i =>
    have hi : i < log.length := by omega
    apply visible_own h view log i log[i] (by simp)
    exact hl log[i] (List.getElem_mem hi)

theorem readDown_visibility_irrel (img : ByteMap width) (log : WriteLog width)
    (h view view' a n)
    (hv : ∀ t, t ≤ n → visible h view log t = true)
    (hv' : ∀ t, t ≤ n → visible h view' log t = true) :
    readDown img log h view a n = readDown img log h view' a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [readDown, hv (n + 1) (Nat.le_refl _), hv' (n + 1) (Nat.le_refl _),
      ↓reduceIte]
    split
    · rfl
    · exact ih (fun t ht => hv t (by omega)) (fun t ht => hv' t (by omega))

theorem read_allOwn (img : ByteMap width) (log : WriteLog width) (h view a)
    (hl : AllOwn h log) : read img log h view a = flat img log a := by
  rw [← read_top_flat img log h a]
  apply readDown_visibility_irrel
  · exact fun t ht => allOwn_visible h view log t hl ht
  · exact fun t ht => visible_below h log.length log t ht

theorem readDown_of_latest (img : ByteMap width) (log : WriteLog width)
    (h view a t v n) (hl : Latest img log a t v)
    (hv : visible h view log t = true) (ht : t ≤ n) :
    readDown img log h view a n = some v := by
  induction n with
  | zero =>
    have he : t = 0 := by omega
    subst t
    simpa using hl.1
  | succ n ih =>
    by_cases he : t = n + 1
    · subst t
      simp [readDown, hv, hl.1]
    · have hn : t < n + 1 := by omega
      have hb := hl.2 (n + 1) hn
      simpa [readDown, hb] using ih (by omega)

theorem read_of_latest (img : ByteMap width) (log : WriteLog width)
    (h view a t v) (hl : Latest img log a t v)
    (hv : visible h view log t = true) : read img log h view a = some v :=
  readDown_of_latest img log h view a t v log.length hl hv
    (logByte_some_le img log t a v hl.1)

theorem latest_flat (img : ByteMap width) (log : WriteLog width)
    (a t v) (hl : Latest img log a t v) : flat img log a = some v := by
  rw [← read_top_flat img log 0 a]
  exact read_of_latest img log 0 log.length a t v hl
    (visible_below 0 log.length log t (logByte_some_le img log t a v hl.1))

/-- Source `flat_latest`: every published byte has a latest timestamp witness. -/
theorem flat_latest (img : ByteMap width) (log : WriteLog width) (a v)
    (present : flat img log a = some v) : ∃ t, Latest img log a t v := by
  induction log using reverseInduction with
  | nil =>
    refine ⟨0, present, ?_⟩
    intro t positive
    exact logByte_beyond img [] t a positive
  | snoc log message ih =>
    rw [flat_append] at present
    cases hm : message.bytes a with
    | none =>
      have old : flat img log a = some v := by simpa [overlay, hm] using present
      obtain ⟨t, latest⟩ := ih old
      exact ⟨t, latest_append_frame img log message a t v hm latest⟩
    | some byte =>
      have eq : byte = v := by simpa [overlay, hm] using present
      subst byte
      exact ⟨log.length + 1, latest_append_new img log message a v hm⟩

theorem read_above_top_flat (img : ByteMap width) (log : WriteLog width)
    (h view a) (hv : log.length ≤ view) : read img log h view a = flat img log a := by
  rw [← read_top_flat img log h a]
  apply readDown_visibility_irrel
  · exact fun t ht => visible_below h view log t (Nat.le_trans ht hv)
  · exact fun t ht => visible_below h log.length log t ht

end MachCSL.Memory
