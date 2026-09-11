import MachCSL.Logic.UartGhostDefs

namespace MachCSL.Logic.UartGhost
open Iris Iris.BI MachCSL.Memory

structure UartGhostSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  allocate : ∀ u, iprop(⊢ |==> ∃ names, ghosts capacity names u ∗ initialClients capacity names u)
  sentGet : ∀ names u, iprop(⊢ sentAuth capacity names u -∗
    sentAuth capacity names u ∗ sent capacity names (Devices.Uart.accepted u))
  outGet : ∀ names u, iprop(⊢ outAuth capacity names u -∗ outAuth capacity names u ∗ outLB capacity names u.out)
  sentUpdate : ∀ names u u', Devices.Uart.accepted u <+: Devices.Uart.accepted u' →
    iprop(sentAuth capacity names u ⊢ |==> (sentAuth capacity names u' ∗ sent capacity names (Devices.Uart.accepted u')))
  outUpdate : ∀ names u u', u.out <+: u'.out →
    iprop(outAuth capacity names u ⊢ |==> (outAuth capacity names u' ∗ outLB capacity names u'.out))
  outPrefix : ∀ names u bytes, iprop(⊢ outAuth capacity names u -∗ outLB capacity names bytes -∗ ⌜bytes <+: u.out⌝)
  txAgree : ∀ names u bytes, iprop(⊢ txAuth capacity names u -∗ txOwn capacity names bytes -∗
    ⌜Devices.Uart.accepted u = bytes⌝)
  txUpdate : ∀ names u bytes u', iprop(⊢ txAuth capacity names u -∗ txOwn capacity names bytes ==∗
    txAuth capacity names u' ∗ txOwn capacity names (Devices.Uart.accepted u'))
  dlabAgree : ∀ names u dq value, iprop(⊢ dlabAuth capacity names u -∗ dlabIs capacity names dq value -∗
    ⌜Devices.Uart.dlab u = value⌝)
  dlabUpdate : ∀ names u value u',
    iprop(⊢ dlabAuth capacity names u -∗ dlabIs capacity names (.own (1 : Qp).half) value ==∗
      dlabAuth capacity names u' ∗ dlabIs capacity names (.own (1 : Qp).half) (Devices.Uart.dlab u'))
  dlabFreeze : ∀ names, iprop(dlabIs capacity names (.own (1 : Qp).half) false ⊢ |==> dlabOff capacity names)
  stable : ∀ names u u', Devices.Uart.accepted u' = Devices.Uart.accepted u →
    u'.out = u.out → Devices.Uart.dlab u' = Devices.Uart.dlab u →
    iprop(ghosts capacity names u ⊢ ghosts capacity names u')
  ready : ∀ names u bytes,
    iprop(⊢ txOwn capacity names bytes -∗ outLB capacity names bytes -∗ dlabOff capacity names -∗
      txAuth capacity names u -∗ outAuth capacity names u -∗ dlabAuth capacity names u -∗
      ⌜u.tx = [] ∧ Devices.Uart.dlab u = false⌝)
  poll : ∀ names u bytes, Devices.Uart.thre u = true →
    iprop(⊢ txOwn capacity names bytes -∗ txAuth capacity names u -∗ outAuth capacity names u -∗
      txOwn capacity names bytes ∗ txAuth capacity names u ∗ outAuth capacity names u ∗
      outLB capacity names bytes ∗ ⌜u.tx = [] ∧ Devices.Uart.accepted u = bytes⌝)

end MachCSL.Logic.UartGhost
