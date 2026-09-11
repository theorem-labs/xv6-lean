import MachCSL.Logic.SupervisorDataPmaProofs

namespace MachCSL.Logic.SupervisorDataPma

theorem nativeSpec : Spec where
  check := fun _ rs dq member kind address n region => check rs dq member kind address n region
  priority := fun _ rs dq member kind address n region => priority_plan rs dq member kind address n region

end MachCSL.Logic.SupervisorDataPma
