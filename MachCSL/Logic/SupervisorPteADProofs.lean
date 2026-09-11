import MachCSL.Logic.SupervisorPteADSpec
import MachCSL.Logic.SupervisorPteADPlan
import MachCSL.Logic.SupervisorPteADSlots
import MachCSL.Logic.SupervisorPteADPure
import MachCSL.Logic.SupervisorPteReadLink
import MachCSL.Logic.SupervisorPteWriteLink
import Xv6.Kernel.KptLeafLink

namespace MachCSL.Logic.SupervisorPteAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open Xv6.Kernel
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

omit [Platform] in
theorem cells_split (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) :
    iprop(cells capacity era cpu rs shares ⊣⊢
      SupervisorPteRead.cells capacity era cpu rs shares.memory ∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs
        [(.menvcfg, shares.environment)]) :=
  RegisterFootprint.cells_append capacity.era.registers _ rs _ _

/-- All five register cells are returned after the real exclusive reread.
The environment cell is framed across the four-cell memory wrapper. -/
theorem wp_slot_read (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    image fixed whole gen era cpu (physical : BitVec 64) bound sets rr
    (continuation : SupervisorPteRead.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte physical) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte physical) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (snapshot address 8 physical)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok physical))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (read_pte_exclusive (.Physaddr address) 8 >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hregs Hslot Hresv Hfinish
  ihave ⟨Hregs, Henv⟩ := (cells_split capacity era cpu rs shares).mp $$ Hregs
  iapply SupervisorPteRead.wp_exclusive capacity shares.memory rs address region config.read
    image fixed whole gen era cpu (.own 1) physical bound sets rr continuation post
    $$ Hcert Hregs Hslot Hresv
  iintro !> %view Hregs Hslot Hresv Hview
  ihave Hregs := (cells_split capacity era cpu rs shares).mpr $$ [Hregs Henv]
  · iframe Hregs Henv
  iapply Hfinish $$ %view Hregs Hslot Hresv Hview

/-- The complete slot is reconstructed after the exact conditional PTE write;
its original publication anchors are framed, not reallocated. -/
theorem wp_slot_write (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    image fixed whole gen era cpu (physical new : BitVec 64) bound sets
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j)
    (continuation : SupervisorPteWrite.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte physical) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot address 8 physical)) -∗
      ▷ (∀ time, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte new) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.History.logElem capacity.era.history era.logEntries (time - 1)
          ⟨snapshot address 8 new, hartAgent cpu⟩ -∗ ⌜0 < time⌝ -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (write_pte_conditional (.Physaddr address) 8 new >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hregs Hslot Hresv Hfinish
  ihave ⟨Hregs, Henv⟩ := (cells_split capacity era cpu rs shares).mp $$ Hregs
  ihave ⟨%floors, Hpin, Hanchors⟩ := slot_open capacity era address physical bound sets $$ Hslot
  have gate := SupervisorPteWrite.wp_write capacity (writeShares shares) rs address region config.write
    image fixed whole gen era cpu physical physical new floors sets continuation post members
  simp only [show SupervisorPteWrite.cells capacity era cpu rs (writeShares shares) =
    SupervisorPteRead.cells capacity era cpu rs shares.memory from rfl] at gate
  iapply gate $$ Hcert Hregs Hresv Hpin
  iintro !> %time Hregs Hpin Hmessage %positive Hresv Hview
  ihave Hregs := (cells_split capacity era cpu rs shares).mpr $$ [Hregs Henv]
  · iframe Hregs Henv
  ihave Hslot := slot_close capacity era address new time bound floors sets $$ [Hpin Hanchors]
  · iframe Hpin Hanchors
  iapply Hfinish $$ %time Hregs Hslot Hresv Hmessage [] Hview
  ipureintro; exact positive

private theorem fold_leaf (plans : KptLeaf.PlanSpec) (rs : RegisterFile)
    (ppn : BitVec 44) (permission : KptLeaf.Permission) (a d : Bool) vpn address access
    (supported : KptLeaf.Supported access) (allows : KptLeaf.Allows permission access) mxr doSum
    image fixed whole gen era cpu
    (continuation : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (continuation (.Ok (ppn, .PBMT_PMA, ())))) post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (KptLeaf.program ppn permission a d vpn address access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  iintro #Hcert Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity [] (by simp [RegisterFootprint.Unique]) image fixed whole gen era cpu rs
    (KptLeaf.program ppn permission a d vpn address access mxr doSum)
    (fun value after => value = .Ok (ppn, .PBMT_PMA, ()) ∧ after = rs)
    continuation post (plans.check rs ppn permission a d vpn address access supported allows mxr doSum)
    $$ Hcert []
  · iunfold RegisterFootprint.cells
    itrivial
  iintro %value %after %same _
  rcases same with ⟨rfl, rfl⟩
  iunfold MemoryWriteWP.threadWP at Hfinish
  iunfold RegisterWP.threadWP
  ieval (change _ ⊢ DeadThread.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok (ppn, .PBMT_PMA, ())))) post)
  iexact Hfinish


private theorem wp_enabled (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    (ppn : BitVec 44) (permission : KptLeaf.Permission) (a d : Bool)
    (cached : BitVec 64) vpn access (supported : KptLeaf.Supported access)
    (allows : KptLeaf.Allows permission access) mxr doSum
    (needs : (update_PTE_Bits cached access).isSome = true) (adue : enabled rs = true)
    image fixed whole gen era cpu bound rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte (KptLeaf.word ppn permission a d))
        bound (PteCanonical.slotSet (KptLeaf.word ppn permission false false)) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares address cached (KptLeaf.word ppn permission a d)
        (KptLeaf.word ppn permission false false) bound rr access continuation post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (afterGate vpn address access mxr doSum true >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  simp only [afterGate, ↓reduceIte, BootPmp.sail_bind_assoc]
  unfold finish
  cases updated : update_PTE_Bits (KptLeaf.word ppn permission a d) access with
  | none =>
    iintro #Hcert Hregs Hslot Hresv Hfinish
    ihave Hfinal := Hfinish $$ %Branch.reread []
    · ipureintro; exact ⟨needs, adue, updated⟩
    iunfold guarded at Hfinal
    iunfold result at Hfinal
    iapply wp_slot_read capacity shares rs address region config image fixed whole gen era cpu
      (KptLeaf.word ppn permission a d) bound _ rr
      (fun response => afterRead vpn address access mxr doSum response >>= continuation) post
      $$ Hcert Hregs Hslot Hresv
    iintro !> %view Hregs Hslot Hresv Hview
    simp only [afterRead, BootPmp.sail_bind_assoc]
    have checked := fold_leaf (hlc := hlc) capacity KptLeaf.nativePlanSpec rs ppn permission a d vpn (.Physaddr address)
      access supported allows mxr doSum image fixed whole gen era cpu
      (fun response => afterCheck address (KptLeaf.word ppn permission a d) access response >>= continuation) post
    ieval (
      change _ ⊢ MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (KptLeaf.program ppn permission a d vpn (.Physaddr address) access mxr doSum >>=
          fun (response : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) =>
            afterCheck address (KptLeaf.word ppn permission a d) access response >>= continuation)) post)
    iapply checked $$ Hcert
    simp only [afterCheck, updated, BootPmp.sail_pure_bind]
    iapply Hfinal
    iunfold clientResources
    simp only [afterWord, afterReservation, receipt]
    iframe Hregs Hslot Hresv
    isplitl [Hview]
    · iexists view; iexact Hview
    · ipureintro; exact KptLeaf.word_canonical ppn permission a d
  | some new =>
    have canonical := update_canonical ppn permission a d access new updated
    have members := canonical_members ppn permission new canonical
    iintro #Hcert Hregs Hslot Hresv Hfinish
    ihave Hfinal := Hfinish $$ %(Branch.written new) []
    · ipureintro; exact ⟨needs, adue, updated⟩
    iunfold guarded at Hfinal
    iunfold result at Hfinal
    iapply wp_slot_read capacity shares rs address region config image fixed whole gen era cpu
      (KptLeaf.word ppn permission a d) bound _ rr
      (fun response => afterRead vpn address access mxr doSum response >>= continuation) post
      $$ Hcert Hregs Hslot Hresv
    iintro !> %view Hregs Hslot Hresv Hview
    simp only [afterRead, BootPmp.sail_bind_assoc]
    have checked := fold_leaf (hlc := hlc) capacity KptLeaf.nativePlanSpec rs ppn permission a d vpn (.Physaddr address)
      access supported allows mxr doSum image fixed whole gen era cpu
      (fun response => afterCheck address (KptLeaf.word ppn permission a d) access response >>= continuation) post
    ieval (
      change _ ⊢ MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (KptLeaf.program ppn permission a d vpn (.Physaddr address) access mxr doSum >>=
          fun (response : _root_.Sail.Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit)) =>
            afterCheck address (KptLeaf.word ppn permission a d) access response >>= continuation)) post)
    iapply checked $$ Hcert
    simp only [afterCheck, updated, BootPmp.sail_bind_assoc]
    iapply wp_slot_write capacity shares rs address region config image fixed whole gen era cpu
      (KptLeaf.word ppn permission a d) new bound _ members
      (fun response => afterWrite new () response >>= continuation) post $$ Hcert Hregs Hslot Hresv
    iintro !> %time Hregs Hslot Hresv Hmessage %positive HwrittenView
    simp only [afterWrite, BootPmp.sail_pure_bind]
    iapply Hfinal
    iunfold clientResources
    simp only [afterWord, afterReservation, receipt]
    iframe Hregs Hslot Hresv
    isplitl [Hmessage HwrittenView]
    · iexists time; iframe Hmessage HwrittenView; ipureintro; exact positive
    · ipureintro; exact canonical

/-- Full native composition of the actual cached/gate/reread/check/write
program. All pure branch equations are obtained from the program itself. -/
theorem wp_update (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (region : PMA_Region) (config : Config rs address region)
    (ppn : BitVec 44) (permission : KptLeaf.Permission) (a d cachedA cachedD : Bool)
    vpn access (supported : KptLeaf.Supported access) (allows : KptLeaf.Allows permission access) mxr doSum
    image fixed whole gen era cpu bound rr (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte (KptLeaf.word ppn permission a d))
        bound (PteCanonical.slotSet (KptLeaf.word ppn permission false false)) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs shares address
        (KptLeaf.word ppn permission cachedA cachedD) (KptLeaf.word ppn permission a d)
        (KptLeaf.word ppn permission false false) bound rr access continuation post -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program vpn address (KptLeaf.word ppn permission cachedA cachedD)
          access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [program_eq]
  cases cachedUpdate : update_PTE_Bits (KptLeaf.word ppn permission cachedA cachedD) access with
  | none =>
    simp only [BootPmp.sail_pure_bind]
    iintro #Hcert Hregs Hslot Hresv Hfinish
    iunfold finish at Hfinish
    ihave Hfinal := Hfinish $$ %Branch.cached []
    · ipureintro; exact cachedUpdate
    iunfold guarded at Hfinal
    iunfold result at Hfinal
    iapply Hfinal
    iunfold clientResources
    simp only [afterWord, afterReservation, receipt]
    iframe Hregs Hslot Hresv
    isplit
    · itrivial
    · ipureintro; exact KptLeaf.word_canonical ppn permission a d
  | some new =>
    have needs : (update_PTE_Bits (KptLeaf.word ppn permission cachedA cachedD) access).isSome = true := by
      rw [cachedUpdate]; rfl
    simp only [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hslot Hresv Hfinish
    iapply RegisterPlan.fold (hlc := hlc) capacity (footprint shares) (footprint_unique shares)
      image fixed whole gen era cpu rs gate (fun value after => value = enabled rs ∧ after = rs)
      (fun value => afterGate vpn address access mxr doSum value >>= continuation) post
      (gate_plan shares rs) $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨returned, unchanged⟩
    subst after
    subst value
    cases adue : enabled rs with
    | false =>
      simp only [afterGate, Bool.false_eq_true, ↓reduceIte, BootPmp.sail_pure_bind]
      iunfold finish at Hfinish
      ihave Hfinal := Hfinish $$ %Branch.disabled []
      · ipureintro; exact ⟨needs, adue⟩
      iunfold guarded at Hfinal
      iunfold result at Hfinal
      iapply Hfinal
      iunfold clientResources
      simp only [afterWord, afterReservation, receipt]
      iframe Hregs Hslot Hresv
      isplit
      · itrivial
      · ipureintro; exact KptLeaf.word_canonical ppn permission a d
    | true =>
      iapply wp_enabled capacity shares rs address region config ppn permission a d
        (KptLeaf.word ppn permission cachedA cachedD) vpn access supported allows mxr doSum needs adue
        image fixed whole gen era cpu bound rr continuation post $$ Hcert Hregs Hslot Hresv Hfinish

theorem actual : Spec capacity := ⟨wp_update capacity⟩

end MachCSL.Logic.SupervisorPteAD
