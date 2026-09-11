import MachCSL.Logic.DeviceSpec

namespace MachCSL.Logic.Device
open Iris Iris.BI Iris.ProofMode MachCSL.Devices
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem uart_agree (γ : GName) (u u' : Uart.State) :
    ⊢@{IProp GF} uartAuth capacity γ u -∗ uartFrag capacity γ u' -∗ ⌜u' = u⌝ := by
  letI := capacity.uart
  unfold uartFrag uartAuth
  iintro Ha Hf
  ihave %h := ghost_var_agree $$ Ha Hf
  ipureintro
  exact h.symm

theorem uart_update (γ : GName) (u u' u'' : Uart.State) :
    ⊢@{IProp GF} uartAuth capacity γ u -∗ uartFrag capacity γ u' ==∗
      uartAuth capacity γ u'' ∗ uartFrag capacity γ u'' := by
  letI := capacity.uart
  exact ghost_var_update_halves u'' γ u u'

theorem plic_agree (γ : GName) (p p' : Plic.State) :
    ⊢@{IProp GF} plicAuth capacity γ p -∗ plicFrag capacity γ p' -∗ ⌜p' = p⌝ := by
  letI := capacity.plic
  unfold plicFrag plicAuth
  iintro Ha Hf
  ihave %h := ghost_var_agree $$ Ha Hf
  ipureintro
  exact h.symm

theorem plic_update (γ : GName) (p p' p'' : Plic.State) :
    ⊢@{IProp GF} plicAuth capacity γ p -∗ plicFrag capacity γ p' ==∗
      plicAuth capacity γ p'' ∗ plicFrag capacity γ p'' := by
  letI := capacity.plic
  exact ghost_var_update_halves p'' γ p p'

theorem virtio_agree (γ : GName) (v v' : Virtio.State) :
    ⊢@{IProp GF} virtioAuth capacity γ v -∗ virtioFrag capacity γ v' -∗ ⌜v' = v⌝ := by
  letI := capacity.virtio
  unfold virtioFrag virtioAuth
  iintro Ha Hf
  ihave %h := ghost_var_agree $$ Ha Hf
  ipureintro
  exact h.symm

theorem virtio_update (γ : GName) (v v' v'' : Virtio.State) :
    ⊢@{IProp GF} virtioAuth capacity γ v -∗ virtioFrag capacity γ v' ==∗
      virtioAuth capacity γ v'' ∗ virtioFrag capacity γ v'' := by
  letI := capacity.virtio
  exact ghost_var_update_halves v'' γ v v'

private theorem alloc_halves {A : Type} [GhostVarG GF A] (a : A) :
    ⊢@{IProp GF} |==> ∃ γ, ghost_var γ (.own (1 : Qp).half) a ∗
      ghost_var γ (.own (1 : Qp).half) a := by
  imod ghost_var_alloc a with ⟨%γ, H⟩
  iexists γ
  imodintro
  have h := ghost_var_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iapply h $$ H

theorem alloc (d : State) :
    ⊢@{IProp GF} |==> ∃ names, interp capacity names d ∗ fragments capacity names d := by
  letI := capacity.uart
  letI := capacity.plic
  letI := capacity.virtio
  imod alloc_halves d.uart with ⟨%γu, Hu, Huf⟩
  imod alloc_halves d.plic with ⟨%γp, Hp, Hpf⟩
  imod alloc_halves d.virtio with ⟨%γv, Hv, Hvf⟩
  iexists (Names.mk γu γp γv)
  imodintro
  unfold interp fragments uartFrag uartAuth plicFrag plicAuth virtioFrag virtioAuth
  iframe

theorem agree (names : Names) (d d' : State) :
    ⊢@{IProp GF} interp capacity names d -∗ fragments capacity names d' -∗ ⌜d' = d⌝ := by
  unfold interp fragments
  iintro ⟨Hu, Hp, Hv⟩ ⟨Huf, Hpf, Hvf⟩
  ihave %hu := uart_agree capacity names.uart d.uart d'.uart $$ Hu Huf
  ihave %hp := plic_agree capacity names.plic d.plic d'.plic $$ Hp Hpf
  ihave %hv := virtio_agree capacity names.virtio d.virtio d'.virtio $$ Hv Hvf
  ipureintro
  cases d; cases d'; congr

theorem update (names : Names) (d d' target : State) :
    ⊢@{IProp GF} interp capacity names d -∗ fragments capacity names d' ==∗
      interp capacity names target ∗ fragments capacity names target := by
  unfold interp fragments
  iintro ⟨Hu, Hp, Hv⟩ ⟨Huf, Hpf, Hvf⟩
  imod uart_update capacity names.uart d.uart d'.uart target.uart $$ Hu Huf with ⟨Hu, Huf⟩
  imod plic_update capacity names.plic d.plic d'.plic target.plic $$ Hp Hpf with ⟨Hp, Hpf⟩
  imod virtio_update capacity names.virtio d.virtio d'.virtio target.virtio $$ Hv Hvf with ⟨Hv, Hvf⟩
  imodintro
  iframe

theorem deviceSpec : DeviceSpec capacity where
  uart_agree := uart_agree capacity
  uart_update := uart_update capacity
  plic_agree := plic_agree capacity
  plic_update := plic_update capacity
  virtio_agree := virtio_agree capacity
  virtio_update := virtio_update capacity
  alloc := alloc capacity

theorem interp_uart_update (names : Names) (d : State) (old target : Uart.State) :
    ⊢@{IProp GF} interp capacity names d -∗ uartFrag capacity names.uart old ==∗
      interp capacity names { d with uart := target } ∗ uartFrag capacity names.uart target := by
  unfold interp
  iintro ⟨Hu, Hp, Hv⟩ Huf
  imod uart_update capacity names.uart d.uart old target $$ Hu Huf with ⟨Hu, Huf⟩
  imodintro
  iframe

theorem interp_plic_update (names : Names) (d : State) (old target : Plic.State) :
    ⊢@{IProp GF} interp capacity names d -∗ plicFrag capacity names.plic old ==∗
      interp capacity names { d with plic := target } ∗ plicFrag capacity names.plic target := by
  unfold interp
  iintro ⟨Hu, Hp, Hv⟩ Hpf
  imod plic_update capacity names.plic d.plic old target $$ Hp Hpf with ⟨Hp, Hpf⟩
  imodintro
  iframe

theorem interp_virtio_update (names : Names) (d : State) (old target : Virtio.State) :
    ⊢@{IProp GF} interp capacity names d -∗ virtioFrag capacity names.virtio old ==∗
      interp capacity names { d with virtio := target } ∗ virtioFrag capacity names.virtio target := by
  unfold interp
  iintro ⟨Hu, Hp, Hv⟩ Hvf
  imod virtio_update capacity names.virtio d.virtio old target $$ Hv Hvf with ⟨Hv, Hvf⟩
  imodintro
  iframe

end MachCSL.Logic.Device
