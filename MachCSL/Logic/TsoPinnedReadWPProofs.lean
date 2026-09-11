import MachCSL.Logic.TsoPinnedReadWPSpec
import MachCSL.Logic.TsoPinnedReadWPPure
import MachCSL.Logic.TsoPinnedReadProofs
import MachCSL.Logic.MemoryReadWPProofs
import MachCSL.Logic.MemoryExclusiveWPProofs
import MachCSL.Machine.PteCanonicalLink

namespace MachCSL.Logic.TsoPinnedReadWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem power_slot_read (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (live : ThreadLive g gen)
    (a : PhysicalAddress) (n : Nat) dq value bound sets :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      credential capacity era cpu bound -∗ slot capacity era a n dq value bound sets -∗
      MachineInterp.powerInterp capacity fixed g ∗ credential capacity era cpu bound ∗
      slot capacity era a n dq value bound sets ∗ ⌜TsoPinnedRead.SlotReads g cpu a n sets⌝) := by
  iintro Hp Hcert Hcred Hslot
  ihave ⟨Hera, Hrestore⟩ := MachineInterp.live_era_access capacity fixed g gen era live $$ Hp Hcert
  iunfold Era.interp at Hera
  icases Hera with ⟨Hregs, Hheap, Hdevice, Hdisk, Htso, Hresv, %valid⟩
  ihave %reads := TsoPinnedRead.slot_read capacity.era.tso era.tsoNames era.imageBytes
    g cpu a n dq value bound sets $$ Htso Hcred Hslot
  ihave Hp : MachineInterp.powerInterp capacity fixed g $$ [Hrestore Hregs Hheap Hdevice Hdisk Htso Hresv]
  · iapply Hrestore
    unfold Era.interp
    iframe Hregs Hheap Hdevice Hdisk Htso Hresv
    ipureintro
    exact valid
  iframe Hp Hcred Hslot
  ipureintro
  exact reads

theorem wp_plain [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu n (req : MemoryReadWP.ReadRequest n) k dq value bound sets rr post
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      credential capacity era cpu bound -∗ slot capacity era req.pa n dq value bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜Allowed n sets word⌝ -∗ credential capacity era cpu bound -∗
        slot capacity era req.pa n dq value bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem n req) k)) post) := by
  iintro #Hcert Hcred Hslot Hresv Hcontinue
  iapply MemoryReadWP.wp_ram_read_plain_ex capacity image fixed whole gen era cpu n req k
    (Allowed n sets) post ram plain $$ Hcert
  unfold MemoryReadWP.plainPremise
  iintro %g %live Hp
  ihave ⟨Hp, Hcred, Hslot, %reads⟩ := power_slot_read capacity fixed g gen era cpu live
    req.pa n dq value bound sets $$ Hp Hcert Hcred Hslot
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  isplit
  · ipureintro
    intro view lower _upper
    exact slot_reads_words g cpu req.pa n sets reads view lower
  · iintro !>
    imod Hback
    imodintro
    iframe Hp
    iintro %view %word %_lower %_upper %_read %allowed Hreceipt
    iapply Hcontinue $$ %view %word [] Hcred Hslot Hresv Hreceipt
    ipureintro
    exact allowed

theorem slot_physical (era : Era.Record) (a : PhysicalAddress) (n : Nat) dq
    (word : BitVec (8 * n)) bound sets :
    iprop(slot capacity era a n dq (nthByte word) bound sets ⊢
      TsoRead.byteWindow capacity.era.heap.ledger era.heap a n dq word) := by
  unfold slot TsoPinnedRead.slotBytes TsoRead.byteWindow
  apply BigSepL.bigSepL_mono
  intro i j _
  iintro ⟨%floor, %time, _, Hpin, _⟩
  iunfold Tso.physLedgerPin at Hpin
  icases Hpin with ⟨Hbyte, _⟩
  isimp only [Era.Capacity.tso, Era.Record.tsoNames] at Hbyte
  iexact Hbyte

theorem heap_slot_read (era : Era.Record) (g : State) (a : PhysicalAddress) (n : Nat) dq
    (word : BitVec (8 * n)) bound sets :
    iprop(⊢ Era.heapInterpAt capacity.era era g -∗
      slot capacity era a n dq (nthByte word) bound sets -∗
      ⌜readBytes g.memory a n = some word⌝) := by
  iintro Hheap Hslot
  ihave Hbytes := slot_physical capacity era a n dq word bound sets $$ Hslot
  iapply MemoryExclusiveWP.heap_window_read capacity era g a n dq word $$ Hheap Hbytes

theorem wp_exclusive [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu (req : MemoryReadWP.ReadRequest 8) k
    dq (word : BitVec 64) bound sets rr post
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      slot capacity era req.pa 8 dq (nthByte word) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, slot capacity era req.pa 8 dq (nthByte word) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem 8 req) k)) post) := by
  iintro Hcert Hslot Hfrag Hcontinue
  iapply MemoryExclusiveWP.wp_exclusive capacity image fixed whole gen era cpu 8 req k rr post ram exclusive
    $$ Hcert Hfrag
  unfold MemoryExclusiveWP.exclusivePremise
  iintro %g Hbundle Htso Hreceipt
  iunfold MemoryExclusiveWP.readBundle at Hbundle
  ihave ⟨Hr, Hheap, Hd⟩ := Hbundle
  ihave %reads := heap_slot_read capacity era g req.pa 8 dq word bound sets $$ Hheap Hslot
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  iexists word
  isplit
  · ipureintro; exact reads
  · iintro !>
    imod Hback
    imodintro
    unfold MemoryExclusiveWP.readBundle
    iframe Hr Hheap Hd Htso
    iintro Hfrag
    iapply Hcontinue $$ %g.log.length Hslot Hfrag Hreceipt

theorem wp_pte [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu (req : MemoryReadWP.ReadRequest 8) k
    dq value bound (reference : BitVec 64) rr post
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      credential capacity era cpu bound -∗
      slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon reference⌝ -∗
        ⌜PteCanonical.nonleaf reference = true → word = reference⌝ -∗
        credential capacity era cpu bound -∗
        slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok (word, none)))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (.impure (.readMem 8 req) k)) post) := by
  iintro Hcert Hcred Hslot Hresv Hcontinue
  iapply wp_plain capacity image fixed whole gen era cpu 8 req k dq value bound
    (PteCanonical.slotSet reference) rr post ram plain $$ Hcert Hcred Hslot Hresv
  iintro !> %view %word %allowed Hcred Hslot Hresv Hreceipt
  iapply Hcontinue $$ %view %word [] [] Hcred Hslot Hresv Hreceipt
  · ipureintro
    exact PteCanonical.canonical_read reference word allowed
  · ipureintro
    exact fun nonleaf => PteCanonical.exact_nonleaf reference word nonleaf allowed

theorem actual [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : Spec capacity :=
  ⟨wp_plain capacity, wp_exclusive capacity, wp_pte capacity⟩

end MachCSL.Logic.TsoPinnedReadWP
