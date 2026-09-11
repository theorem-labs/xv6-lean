import MachCSL.Logic.EventWPSpec

namespace MachCSL.Logic.EventWP
open Iris Iris.Std Iris.BI MachCSL.Machine
open Iris.Std.LawfulPartialMap Iris.Std.PartialMap

variable (facts : InitialMapFacts)
include facts
set_option maxRecDepth 10000

theorem ownedMap_lookup (rs : RegisterFile) (r : Register) :
    get? (ownedMap rs) r = if IsPin r then none else some (⟨r, rs r⟩ : Registers.Value) := by
  simp only [ownedMap, get?_delete, facts.lookup]
  by_cases hs : r = .sig_seip <;> by_cases hm : r = .sig_meip <;>
    simp_all [IsPin, eq_comm]

theorem ownedMap_lookup_owned (rs : RegisterFile) (r : Register) (owned : IsOwned r) :
    get? (ownedMap rs) r = some (⟨r, rs r⟩ : Registers.Value) := by
  rw [ownedMap_lookup facts]
  exact if_neg owned

theorem ownedMap_write (rs : RegisterFile) (r : Register) (value : RegisterType r)
    (owned : IsOwned r) :
    ownedMap (Sail.Registers.write rs r value) = insert (ownedMap rs) r ⟨r, value⟩ := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro key
  change get? (ownedMap (Sail.Registers.write rs r value)) key =
    get? (insert (ownedMap rs) r (⟨r, value⟩ : Registers.Value)) key
  rw [ownedMap_lookup facts, get?_insert, ownedMap_lookup facts]
  by_cases same : r = key
  · subst key
    simp only [if_neg owned, Sail.Registers.write_same, ite_true]
  · rw [if_neg same, Sail.Registers.write_other rs r key value same]

variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

theorem ownedCells_access (γ : GName) (rs : RegisterFile) (r : Register) (owned : IsOwned r) :
    iprop(⊢ ownedCells capacity γ rs -∗
      Registers.regPointsto capacity γ r (.own 1) (rs r) ∗
      (∀ value : RegisterType r, Registers.regPointsto capacity γ r (.own 1) value -∗
        ownedCells capacity γ (Sail.Registers.write rs r value))) := by
  letI := capacity.registers
  unfold ownedCells Registers.regPointsto
  iintro H
  ihave ⟨Hcell, Hrestore⟩ := (BigSepM.bigSepM_insert_acc
    (Φ := fun key value => ghost_map_elem γ (.own 1) key value)
    (ownedMap_lookup_owned facts rs r owned)) $$ H
  iframe Hcell
  iintro %value Hcell
  rw [ownedMap_write facts rs r value owned]
  iapply Hrestore $$ Hcell

theorem initialCells_split (γ : GName) (rs : RegisterFile) :
    iprop(Registers.initialCells capacity γ rs ⊣⊢
      ownedCells capacity γ rs ∗
      Registers.regPointsto capacity γ .sig_seip (.own 1) (rs .sig_seip) ∗
      Registers.regPointsto capacity γ .sig_meip (.own 1) (rs .sig_meip)) := by
  letI := capacity.registers
  have seip := facts.lookup rs .sig_seip
  have meip : get? (delete (Registers.initialMap rs) .sig_seip) .sig_meip =
      some (⟨.sig_meip, rs .sig_meip⟩ : Registers.Value) := by
    rw [get?_delete_ne (by decide), facts.lookup]
  unfold Registers.initialCells ownedCells ownedMap Registers.regPointsto
  constructor
  · iintro H
    ihave ⟨Hs, Hrest⟩ := (BigSepM.bigSepM_delete seip).1 $$ H
    ihave ⟨Hm, Howned⟩ := (BigSepM.bigSepM_delete meip).1 $$ Hrest
    iframe
  · iintro ⟨Howned, Hs, Hm⟩
    iapply (BigSepM.bigSepM_delete seip).2
    iframe Hs
    iapply (BigSepM.bigSepM_delete meip).2
    iframe

section Fold
variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
variable (machine : MachineInterp.Capacity GF)

theorem fold_plan (registerRules : RegisterWP.RegisterWPSpec machine)
    (memoryRules : MemoryReadWP.MemoryReadWPSpec machine)
    (reads : ReadAllowed) (dq : DFrac) (resources : IProp GF) (era : Era.Record)
    (access : RamAccess machine era reads dq resources)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (cpu : CPU) (rs : RegisterFile) (program : SailM Unit)
    (Q : Unit → RegisterFile → Prop) (post : Empty → IProp GF)
    (plan : ExecPlan reads rs program Q) :
    iprop(⊢ MachineInterp.generationCertificate machine fixed generation era -∗
      ownedCells machine.era.registers (era.registers cpu) rs -∗ resources -∗
      (∀ result, ⌜Q () result⌝ -∗
        ownedCells machine.era.registers (era.registers cpu) result -∗ resources -∗
        RegisterWP.threadWP machine image fixed whole (.hart generation cpu (.pure ())) post) -∗
      RegisterWP.threadWP machine image fixed whole (.hart generation cpu program) post) := by
  haveI : Persistent (MachineInterp.generationCertificate machine fixed generation era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction plan with
  | @pure rs value Q good =>
    cases value
    iintro #Hcert Hregs Hram Hfinish
    iapply Hfinish $$ [] Hregs Hram
    ipureintro
    exact good
  | @readOwned rs r k Q owned rest ih =>
    iintro #Hcert Hregs Hram Hfinish
    ihave ⟨Hcell, Hrestore⟩ := ownedCells_access facts machine.era.registers
      (era.registers cpu) rs r owned $$ Hregs
    iapply registerRules.read image fixed whole generation era cpu r (.own 1) (rs r) k post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ %(rs r) Hcell
    rw [Sail.Registers.write_current]
    iapply ih $$ Hcert Hregs Hram Hfinish
  | @readPin rs r k Q pin rest ih =>
    iintro #Hcert Hregs Hram Hfinish
    iapply registerRules.readAny image fixed whole generation era cpu r k post $$ Hcert
    iintro !> %value
    iapply ih value $$ Hcert Hregs Hram Hfinish
  | @writeOwned rs r value k Q owned rest ih =>
    iintro #Hcert Hregs Hram Hfinish
    ihave ⟨Hcell, Hrestore⟩ := ownedCells_access facts machine.era.registers
      (era.registers cpu) rs r owned $$ Hregs
    iapply registerRules.write image fixed whole generation era cpu r (rs r) value k post $$ Hcert Hcell
    iintro !> Hcell
    ihave Hregs := Hrestore $$ %value Hcell
    iapply ih $$ Hcert Hregs Hram Hfinish
  | @readMem rs n req word k Q ram plain allowed rest ih =>
    haveI : Persistent (TsoRead.pristineWindow machine.era.heap.ledger era.timestamps req.pa n) := by
      unfold TsoRead.pristineWindow TsoRead.pristineByte Tso.timestampElem
      infer_instance
    iintro #Hcert Hregs Hram Hfinish
    ihave ⟨Hbytes, #Hpristine, Hrestore⟩ := access.access n req word allowed $$ Hram
    iapply memoryRules.pristine image fixed whole generation era cpu n req k dq word post ram plain $$
      Hcert Hbytes Hpristine
    iintro !> %view Hbytes Hview
    ihave Hram := Hrestore $$ Hbytes Hpristine
    iapply ih $$ Hcert Hregs Hram Hfinish

theorem eventWPSpec (registerRules : RegisterWP.RegisterWPSpec machine)
    (memoryRules : MemoryReadWP.MemoryReadWPSpec machine) : EventWPSpec machine where
  initialSplit := initialCells_split facts machine.era.registers
  fold := fold_plan facts machine registerRules memoryRules

end Fold

end MachCSL.Logic.EventWP
