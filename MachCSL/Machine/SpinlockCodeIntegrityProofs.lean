import MachCSL.Machine.SpinlockCodeIntegrityDefs

namespace MachCSL.Machine.SpinlockCodeIntegrity
open MachCSL.Memory

theorem untouched_logByte (img : ByteMap width) (log : WriteLog width) (a : Address width)
    (untouched : ∀ m, m ∈ log → m.bytes a = none) (n : Nat) :
    logByte img log (n + 1) a = none := by
  change (log[n]?).bind (fun m => msgByte m a) = none
  cases found : log[n]? with
  | none => rfl
  | some m => exact untouched m (List.mem_of_getElem? found)

theorem untouched_readDown (img : ByteMap width) (log : WriteLog width) (a : Address width)
    (untouched : ∀ m, m ∈ log → m.bytes a = none) (author view n : Nat) :
    readDown img log author view a n = img a := by
  induction n with
  | zero => exact readDown_zero img log author view a
  | succ n ih =>
    rw [readDown, untouched_logByte img log a untouched n]
    cases visible author view log (n + 1) <;> exact ih

theorem untouched_read (img : ByteMap width) (log : WriteLog width) (a : Address width)
    (untouched : ∀ m, m ∈ log → m.bytes a = none) (author view : Nat) :
    read img log author view a = img a :=
  untouched_readDown img log a untouched author view log.length

theorem nil : CodeUnwritten [] := by intro message member; cases member

theorem append_data (log : WriteLog 64) (unwritten : CodeUnwritten log)
    (address : PhysicalAddress) (data : address = SpinlockImage.lockAddress ∨ address = SpinlockImage.counterAddress)
    (word : BitVec 32) (author : Agent) : CodeUnwritten (log ++ [⟨snapshot address 4 word, author⟩]) := by
  intro message member i j bound
  rcases List.mem_append.mp member with old | fresh
  · exact unwritten message old i j bound
  · obtain rfl := List.mem_singleton.mp fresh
    have code : Footprint (SpinlockImage.instructionAddress i) 4
        (addressAdd (SpinlockImage.instructionAddress i) j) := ⟨j, bound, rfl⟩
    have outside : ¬ Footprint address 4 (addressAdd (SpinlockImage.instructionAddress i) j) := by
      rcases data with rfl | rfl
      · exact fun other => SpinlockImage.code_lock_separate i _ code other
      · exact fun other => SpinlockImage.code_counter_separate i _ code other
    exact writeBytes_outside empty address _ 4 word outside

theorem read_code (log : WriteLog 64) (unwritten : CodeUnwritten log)
    (author view : Nat) (i : Fin 17) :
    ReadsBytes (loadedRam SpinlockImage.image) log author view
      (SpinlockImage.instructionAddress i) 4 (SpinlockImage.word i) := by
  intro j bound
  rw [untouched_read _ log _ (fun message member => unwritten message member i j bound)]
  exact readBytes_spec _ _ _ _ (SpinlockImage.instruction_bytes i) j bound

theorem flat_code (log : WriteLog 64) (unwritten : CodeUnwritten log) (i : Fin 17) :
    readBytes (flat (loadedRam SpinlockImage.image) log) (SpinlockImage.instructionAddress i) 4 =
      some (SpinlockImage.word i) := by
  apply (readBytes_eq_some_iff _ _ _ _).mpr
  intro j bound
  rw [← read_top_flat (loadedRam SpinlockImage.image) log 0]
  exact read_code log unwritten 0 log.length i j bound

end MachCSL.Machine.SpinlockCodeIntegrity
