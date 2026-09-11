import Xv6.Kernel.BareJalFetchPureProofs
import Xv6.Kernel.KernelTextDatumLink

namespace Xv6.Kernel.BareJalFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance code_persistent era pc word : Persistent (code capacity era pc word) := by
  unfold code; infer_instance

theorem partition era cpu rs shares : iprop(cells capacity era cpu rs shares ⊣⊢
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
      [(.PC,shares.pc),(.misa,shares.misa)] ∗
    SupervisorBareFetch.cells capacity.machine era cpu rs shares.bare) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem context era ξ address n word :
    iprop(KernelTextDatum.window capacity era .identity address n .discard word ⊢
      TsoContextBytesReadWP.window capacity.machine era ξ address n .discard word) :=
  (KernelTextDatum.nativeWindowSpec capacity).context_identity era ξ address n word

theorem text era address n word (positive : 0 < n) :
    iprop(KernelTextDatum.window capacity era .identity address n .discard word ⊢
      ⌜KernelTextDatum.AddrIsText address⌝) := by
  iintro Hwindow
  ihave ⟨%ppn,Hclaim,_⟩ := KernelTextDatum.choose capacity era .identity address n .discard word positive $$ Hwindow
  iunfold KernelTextDatum.claim at Hclaim
  icases Hclaim with ⟨_,%facts⟩
  ipureintro
  have ident : KernelTextDatum.physical ppn address = address := facts.2.2
  rw [← ident]
  exact facts.2.1

theorem nativeResourceSpec : ResourceSpec capacity :=
  ⟨code_persistent capacity,partition capacity,context capacity,text capacity⟩

end Xv6.Kernel.BareJalFetch
