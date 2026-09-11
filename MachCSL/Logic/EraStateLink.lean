import MachCSL.Logic.EraStateProofs
import MachCSL.Logic.StateInterpLink

namespace MachCSL.Logic.EraState
open Iris Iris.BI MachCSL.Machine

theorem registryEraStateSpec : EraStateSpec Era.capacity := eraStateSpec Era.capacity

end MachCSL.Logic.EraState

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Lift a proved current-era update while preserving all fixed resources.
The durable-disk equality is mandatory; disk-changing transitions need their
own fixed-authority update and cannot use this rule. -/
theorem live_update (names : FixedNames) (g g' : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (gen : g'.generation = g.generation)
    (power : g'.power = g.power) (disk : g'.devices.virtio.v_disk = g.devices.virtio.v_disk)
    (C R : IProp GF)
    (update : iprop(⊢ Era.interp capacity.era era g -∗ C ==∗ Era.interp capacity.era era g' ∗ R)) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗ C ==∗
      powerInterp capacity names g' ∗ R) := by
  unfold powerInterp generationCertificate PowerGhost.counterInterp FixedNames.power
  have count : PowerGhost.startCount g' = PowerGhost.startCount g := by
    simp [PowerGhost.startCount, gen, power]
  rw [gen, power, disk, count, live.1, live.2]
  simp only [↓reduceIte]
  iintro ⟨Hc, Hd, %entries, Hr, %domain, %current, %lookup, Hera⟩ ⟨_, _, Hregistered⟩ HC
  ihave %registered := Era.registry_lookup capacity.registry names.registry entries generation era $$ Hr Hregistered
  have same : current = era := Option.some.inj (lookup.symm.trans registered)
  subst current
  imod update $$ Hera HC with ⟨Hera, HR⟩
  imodintro
  iframe
  ipureintro
  exact ⟨domain, lookup⟩

theorem power_read_register (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (cpu : CPU) (r : Register) (dq : DFrac) (value : RegisterType r) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r dq value -∗
      ⌜g.registers cpu r = value⌝) := by
  iintro Hp Hcert Hvalue
  ihave ⟨Hera, _⟩ := live_era_access capacity names g generation era live $$ Hp Hcert
  iapply EraState.read_register capacity.era
    (GlobalRegisters.globalRegisterSpec _ (Registers.registerSpec _)) era g cpu r dq value $$ Hera Hvalue

theorem power_write_register (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (cpu : CPU) (r : Register) (old value : RegisterType r) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) old ==∗
      powerInterp capacity names (EraState.writeRegister g cpu r value) ∗
      Registers.regPointsto capacity.era.registers (era.registers cpu) r (.own 1) value) :=
  live_update capacity names g (EraState.writeRegister g cpu r value) generation era live rfl rfl rfl _ _
    (EraState.write_register capacity.era
      (GlobalRegisters.globalRegisterSpec _ (Registers.registerSpec _)) era g cpu r old value)

end MachCSL.Logic.MachineInterp
