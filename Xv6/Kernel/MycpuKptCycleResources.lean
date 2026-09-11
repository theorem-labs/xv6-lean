import Xv6.Kernel.MycpuKptCyclePureProofs
import Xv6.Kernel.MycpuKptFetchLink
import Xv6.Kernel.MycpuKptMemoryRules

namespace Xv6.Kernel.MycpuKptCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

theorem bodyGuards_mono r control cpu values root entrySP
    (left right : MycpuKptBody.Outcome r → IProp GF) :
    iprop(⊢ (∀ outcome, left outcome -∗ right outcome) -∗
      bodyGuards r control cpu values root entrySP left -∗
      bodyGuards r control cpu values root entrySP right) := by
  cases r with
  | registers inst =>
    simp only [bodyGuards]
    iintro Hmap Hleft
    iapply Hmap $$ %(.registers inst) Hleft
  | memory kind slot =>
    iintro Hmap Hleft
    iunfold bodyGuards
    iunfold bodyGuards at Hleft
    iapply MycpuKptMemory.guards_frame
      (P := fun ppn data outcome => iprop(⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (MycpuKptBody.slotAddress entrySP slot) ppn outcome⌝ -∗ ▷ (∀ view, left (.memory kind slot outcome view))))
      (Q := fun ppn data outcome => iprop(⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (MycpuKptBody.slotAddress entrySP slot) ppn outcome⌝ -∗ ▷ (∀ view, right (.memory kind slot outcome view))))
      (R := iprop(∀ outcome, left outcome -∗ right outcome)) (next := ?_) $$ [Hmap Hleft]
    · intro ppn data outcome
      iintro ⟨Hmap,Hleft⟩ %facts
      ihave Hleft := Hleft $$ %facts
      iintro !> %view
      ihave Hleft := Hleft $$ %view
      iapply Hmap $$ %(.memory kind slot outcome view) Hleft
    · iframe

theorem guards_mono i control cpu values root entrySP
    (left right : List KptFetchHalf.Step → Outcome i → IProp GF) :
    iprop(⊢ (∀ trace outcome, left trace outcome -∗ right trace outcome) -∗
      guards i control cpu values root entrySP left -∗ guards i control cpu values root entrySP right) := by
  iintro Hmap Hleft
  iunfold guards
  iunfold guards at Hleft
  iapply KptFetch.guardChunks_mono $$ [Hmap] Hleft
  iintro %trace Hbody
  iapply bodyGuards_mono $$ [Hmap] Hbody
  iintro %outcome Hleft
  iapply Hmap $$ %trace %outcome Hleft

variable [Platform] (capacity : Capacity GF)

theorem body_finish_eq image fixed whole gen era cpu shares control values N root r tier ξ entrySP words rr frame continuation post :
    MycpuKptBody.finish capacity image fixed whole gen era cpu shares control values N root r tier ξ entrySP words rr frame continuation post =
    bodyGuards r control cpu values root entrySP (fun outcome => iprop(
      MycpuKptBody.resources capacity era cpu shares control values N root r tier ξ entrySP words rr outcome frame -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post)) := by
  cases r <;> rfl

/-- A supplied checked finite register prefix acts only on the owned packet;
the native active rule below supplies the actual decoder/landing prefix. -/
theorem wp_prefix {A : Type} shares control after values cpu (sameMs : after .mstatus = control .mstatus)
    (program body : SailM A)
    (cut : MycpuActive.Prefix (footprint shares) (entry control cpu values)
      program body (entry after cpu values))
    image fixed whole gen era (N : Namespace) root (frame : IProp GF)
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ frame -∗
      (packet capacity era cpu (.kpt N root) after values shares -∗ frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (body >>= continuation)) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  iintro #Hcert Hpacket Hframe Hfinish
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ := (MycpuRegimeShell.partition capacity era cpu (.kpt N root) control values shares).mp $$ Hpacket
  iapply MycpuActive.Prefix.fold capacity.machine (footprint shares) (MycpuRegimeShell.footprint_unique shares)
    (entry control cpu values) (entry after cpu values) program body cut image fixed whole gen era cpu continuation post $$ Hcert Hcells
  iintro Hcells
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu (.kpt N root) after values shares).mpr $$ [Hcells Hbits Hz Htr]
  · rw [sameMs]
    iframe
  iapply Hfinish $$ Hpacket Hframe

end Xv6.Kernel.MycpuKptCycle
