import Xv6.Kernel.PushOffWord4BareProofs
namespace Xv6.Kernel.PushOffWord4Bare
open Iris MachCSL.Machine MachCSL.Logic

theorem nativePureSpec [Platform] : PureSpec where
  footprintUnique := unique
  transform := transform
  read := fun s rs cfg va aligned range => Read.program_boundary s rs va cfg range aligned
  write := fun s rs cfg va new aligned range => Write.virtual_boundary s rs va new cfg range aligned

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := ⟨wp_transformed capacity⟩
end Xv6.Kernel.PushOffWord4Bare
