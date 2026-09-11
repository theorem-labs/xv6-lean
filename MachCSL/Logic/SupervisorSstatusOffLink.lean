import MachCSL.Logic.SupervisorSstatusOffProofs

namespace MachCSL.Logic.SupervisorSstatusOff

/-- All eleven contracts are discharged by actual ordinary-kernel proofs;
there is no supplied component, evaluation or register-preservation oracle. -/
theorem nativeSpec : Spec where
  supports_landing_pad := supports_landing_pad
  lower_sie := lower_SIE
  write_value := write_value
  lift_lower := lift_lower
  legalized_self := legalized_self
  result_self := result_self
  result_facts := result_facts
  result_bits := result_bits
  lower_sie_zero := lower_sie_zero
  legalize_plan := legalize_plan
  off_plan := off_plan

end MachCSL.Logic.SupervisorSstatusOff
