import MachCSL.Logic.DeviceDefs

namespace MachCSL.Logic.Device
open Iris Iris.BI MachCSL.Devices

structure DeviceSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  uart_agree : ∀ γ u u', iprop(⊢ uartAuth capacity γ u -∗ uartFrag capacity γ u' -∗ ⌜u' = u⌝)
  uart_update : ∀ γ u u' u'', iprop(⊢ uartAuth capacity γ u -∗ uartFrag capacity γ u' ==∗
    uartAuth capacity γ u'' ∗ uartFrag capacity γ u'')
  plic_agree : ∀ γ p p', iprop(⊢ plicAuth capacity γ p -∗ plicFrag capacity γ p' -∗ ⌜p' = p⌝)
  plic_update : ∀ γ p p' p'', iprop(⊢ plicAuth capacity γ p -∗ plicFrag capacity γ p' ==∗
    plicAuth capacity γ p'' ∗ plicFrag capacity γ p'')
  virtio_agree : ∀ γ v v', iprop(⊢ virtioAuth capacity γ v -∗ virtioFrag capacity γ v' -∗ ⌜v' = v⌝)
  virtio_update : ∀ γ v v' v'', iprop(⊢ virtioAuth capacity γ v -∗ virtioFrag capacity γ v' ==∗
    virtioAuth capacity γ v'' ∗ virtioFrag capacity γ v'')
  alloc : ∀ d, iprop(⊢ |==> ∃ names, interp capacity names d ∗ fragments capacity names d)

end MachCSL.Logic.Device
