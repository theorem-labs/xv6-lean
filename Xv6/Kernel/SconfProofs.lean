import Xv6.Kernel.SconfSpec
import MachCSL.Logic.SupervisorBitsLink
import MachCSL.Logic.RegisterProofs
import MachCSL.Logic.StateInterpProofs
import MachCSL.Logic.KptGhostProofs

namespace Xv6.Kernel.Sconf
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem environment_literal : EnvironmentFacts menvcfgS := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem delegated_literal : Delegated 0xffff#64 := by
  unfold Delegated
  decide

theorem pureSpec : PureSpec where
  environment_literal := environment_literal
  delegated_literal := delegated_literal
  environment_value := fun _ h => h.2.2.2.2

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The hardware component is persistent by its actual native cells,
claims and certificate; no duplicate configuration ownership is postulated. -/
instance hardware_persistent fixed gen era cpu : Persistent (hardware capacity fixed gen era cpu) := by
  unfold hardware HardwareConfig.config HardwareConfig.cells KernelMapStatic.claims
  infer_instance

theorem intro_config fixed gen era cpu ms delegation value
    (delegated : Delegated delegation) (facts : EnvironmentFacts value) :
    iprop(⊢ hardware capacity fixed gen era cpu -∗
      cell capacity era cpu .cur_privilege .Supervisor -∗ msOwn capacity era cpu ms -∗
      cell capacity era cpu .mie mieS -∗ cell capacity era cpu .mideleg delegation -∗
      cell capacity era cpu .menvcfg value -∗ sconf capacity fixed gen era cpu) := by
  iintro Hhw Hpriv Hms Hmie Hmd Henv
  unfold sconf parts
  iexists ms
  iframe Hhw Hpriv Hms
  unfold minstretInv
  isplitr
  · iempintro
  · isplitl [Hmie Hmd]
    · unfold interrupts
      iexists delegation
      iframe
      ipureintro
      exact delegated
    · unfold environment
      iexists value
      iframe
      ipureintro
      exact facts

theorem open_parts fixed gen era cpu :
    iprop(sconf capacity fixed gen era cpu ⊣⊢ ∃ ms, parts capacity fixed gen era cpu ms) := .rfl

theorem close_parts fixed gen era cpu ms :
    iprop(parts capacity fixed gen era cpu ms ⊢ sconf capacity fixed gen era cpu) := by
  iintro H
  unfold sconf
  iexists ms
  iexact H

theorem at_open fixed gen era cpu :
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ ms, sconfAt capacity fixed gen era cpu ms) := by
  unfold sconf parts sconfAt
  iintro ⟨%ms, Hhw, Hmin, Hpriv, Hms, Hintr, Henv⟩
  iexists ms
  iframe Hms
  iintro %replacement Hreplacement
  unfold sconf parts
  iexists replacement
  iframe

theorem at_close fixed gen era cpu ms :
    iprop(sconfAt capacity fixed gen era cpu ms ⊢ sconf capacity fixed gen era cpu) := by
  unfold sconfAt
  iintro ⟨Hms, Hclose⟩
  iapply Hclose $$ Hms

theorem at_facts fixed gen era cpu ms :
    iprop(sconfAt capacity fixed gen era cpu ms ⊢ ⌜SupervisorBits.MsFacts ms⌝) := by
  unfold sconfAt msOwn SupervisorBits.msOwnAt SupervisorBits.msOwn
  iintro ⟨⟨_, _, _, Hfacts⟩, _⟩
  iexact Hfacts

theorem at_sret fixed gen era cpu ms spp spie :
    iprop(⊢ sconfAt capacity fixed gen era cpu ms -∗
      SupervisorBits.sretBits capacity.supervisorBits (SupervisorBits.namesOfEra era cpu) spp spie -∗
      ⌜_get_Mstatus_SPP ms = spp ∧ _get_Mstatus_SPIE ms = spie⌝) := by
  unfold sconfAt msOwn SupervisorBits.msOwnAt SupervisorBits.msOwn SupervisorBits.sretTie
  iintro ⟨⟨_, _, Htie, _⟩, _⟩ Hbits
  iapply (SupervisorBits.actual capacity.supervisorBits).sretAgree $$ Htie Hbits

theorem at_sie fixed gen era cpu ms q value :
    iprop(⊢ sconfAt capacity fixed gen era cpu ms -∗
      SupervisorBits.bit capacity.supervisorBits (SupervisorBits.namesOfEra era cpu).sie q value -∗
      ⌜_get_Mstatus_SIE ms = value⌝) := by
  unfold sconfAt msOwn SupervisorBits.msOwnAt SupervisorBits.msOwn
  iintro ⟨⟨_, Htie, _, _⟩, _⟩ Hbit
  iapply (SupervisorBits.actual capacity.supervisorBits).agree $$ Htie Hbit

theorem hardware_access fixed gen era cpu :
    iprop(sconf capacity fixed gen era cpu ⊢
      hardware capacity fixed gen era cpu ∗ sconf capacity fixed gen era cpu) := by
  unfold sconf parts
  iintro ⟨%ms, #Hhw, Hmin, Hpriv, Hms, Hintr, Henv⟩
  iframe Hhw
  iexists ms
  iframe

theorem interrupts_access fixed gen era cpu :
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ delegation,
      cell capacity era cpu .mie mieS ∗ cell capacity era cpu .mideleg delegation ∗
      ⌜Delegated delegation⌝ ∗
      (cell capacity era cpu .mie mieS -∗ cell capacity era cpu .mideleg delegation -∗
        sconf capacity fixed gen era cpu)) := by
  unfold sconf parts interrupts
  iintro ⟨%ms, Hhw, Hmin, Hpriv, Hms, ⟨%delegation, Hmie, Hmd, %Hdeleg⟩, Henv⟩
  iexists delegation
  iframe Hmie Hmd
  isplitr
  · ipureintro; exact Hdeleg
  · iintro Hmie Hmd
    iexists ms
    iframe Hhw Hmin Hpriv Hms Henv
    iexists delegation
    iframe
    ipureintro
    exact Hdeleg

theorem environment_access fixed gen era cpu :
    iprop(sconf capacity fixed gen era cpu ⊢ ∃ value,
      cell capacity era cpu .menvcfg value ∗ ⌜EnvironmentFacts value⌝ ∗
      (cell capacity era cpu .menvcfg value -∗ sconf capacity fixed gen era cpu)) := by
  unfold sconf parts environment
  iintro ⟨%ms, Hhw, Hmin, Hpriv, Hms, Hintr, ⟨%value, Henv, %Hfacts⟩⟩
  iexists value
  iframe Henv
  isplitr
  · ipureintro; exact Hfacts
  · iintro Henv
    iexists ms
    iframe Hhw Hmin Hpriv Hms Hintr
    iexists value
    iframe
    ipureintro
    exact Hfacts

theorem privilege_agree fixed gen era cpu dq value :
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .cur_privilege dq value -∗
      ⌜value = .Supervisor⌝) := by
  unfold sconf parts cell
  iintro ⟨%ms, _, _, Hpriv, _⟩ Hvalue
  iapply Registers.regPointsto_agree capacity.machine.era.registers $$ [Hvalue Hpriv]
  iframe

theorem enable_agree fixed gen era cpu dq value :
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mie dq value -∗ ⌜value = mieS⌝) := by
  unfold sconf parts interrupts cell
  iintro ⟨%ms, _, _, _, _, ⟨%delegation, Hmie, _⟩, _⟩ Hvalue
  iapply Registers.regPointsto_agree capacity.machine.era.registers $$ [Hvalue Hmie]
  iframe

theorem environment_agree fixed gen era cpu dq value :
    iprop(⊢ sconf capacity fixed gen era cpu -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .menvcfg dq value -∗
      ⌜EnvironmentFacts value⌝) := by
  unfold sconf parts environment cell
  iintro ⟨%ms, _, _, _, _, _, ⟨%environment, Henv, %Hfacts⟩⟩ Hvalue
  ihave %same := Registers.regPointsto_agree capacity.machine.era.registers $$ [Hvalue Henv]
  · iframe
  ipureintro
  simpa only [same] using Hfacts

end Xv6.Kernel.Sconf
