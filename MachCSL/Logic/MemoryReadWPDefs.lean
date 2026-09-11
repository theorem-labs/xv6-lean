import MachCSL.Logic.TsoReadDefs
import MachCSL.Logic.DeadThreadDefs

namespace MachCSL.Logic.MemoryReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
open _root_.Sail.ConcurrencyInterfaceV1

abbrev ReadRequest (n : Nat) := Mem_read_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak
abbrev ReadResult (n : Nat) := _root_.Sail.Result (BitVec (8 * n) × Option Bool) Arch.abort
abbrev threadWP := @DeadThread.threadWP

/-- Explicit conditional adaptation of `wp_hart_ram_read_plain_ex`.
The callback receives and returns the ORIGINAL complete power interpretation;
the node rule, not this callback, pays the actual successor's view update. -/
def plainPremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : ReadRequest n) (k : ReadResult n → SailM Unit) (P : BitVec (8 * n) → Prop)
    (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ g : State, ⌜ThreadLive g gen⌝ -∗ MachineInterp.powerInterp capacity fixed g ={⊤,∅}=∗
    ⌜∀ view, g.views cpu ≤ view → view ≤ g.log.length →
      ∃ word, ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word ∧ P word⌝ ∗
    ▷ (|={∅,⊤}=> MachineInterp.powerInterp capacity fixed g ∗
      ∀ view word, ⌜g.views cpu ≤ view⌝ -∗ ⌜view ≤ g.log.length⌝ -∗
        ⌜ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word⌝ -∗ ⌜P word⌝ -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post))


/-- Source fixed-word callback: one word must work at EVERY reachable view.
The word may be chosen from the currently opened state. -/
def plainWordPremise {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (n : Nat)
    (req : ReadRequest n) (k : ReadResult n → SailM Unit) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ g : State, ⌜ThreadLive g gen⌝ -∗ MachineInterp.powerInterp capacity fixed g ={⊤,∅}=∗
    ∃ word, ⌜∀ view, g.views cpu ≤ view → view ≤ g.log.length →
      ReadsBytes g.image g.log (hartAgent cpu) view req.pa n word⌝ ∗
    ▷ (|={∅,⊤}=> MachineInterp.powerInterp capacity fixed g ∗
      ∀ view, ⌜g.views cpu ≤ view⌝ -∗ ⌜view ≤ g.log.length⌝ -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post))

end MachCSL.Logic.MemoryReadWP
