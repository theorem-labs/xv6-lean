import MachCSL.Logic.IcacheTopRegistryDefs

namespace MachCSL.Logic.IcacheTopRegistry
open Iris Iris.Std Iris.BI

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  allocate : ∀ names (N : Namespace) (E : CoPset) nodes,
    (∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node) →
    iprop(⊢ FsTop.auth capacity.top names.top nodes -∗ armAuth capacity names ∅
      ={E}=∗ invariant capacity names N)
  arm : ∀ names (N : Namespace) (E : CoPset) i t q, (↑N : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names N -∗ LogTx.tx_pin capacity.transactions names.transactions t q
      ={E}=∗ ∃ k, armed capacity names k t q {i})
  disarm : ∀ names (N : Namespace) (E : CoPset) k t q S i node, (↑N : CoPset) ⊆ E →
    Xv6.Fs.DurableNode.Local i node →
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q S -∗
      FsTop.frag capacity.top names.top i node ={E}=∗
      armed capacity names k t q (S \ {i}) ∗ FsTop.frag capacity.top names.top i node)
  release : ∀ names (N : Namespace) (E : CoPset) k t q, (↑N : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names N -∗ armed capacity names k t q ∅
      ={E}=∗ LogTx.tx_pin capacity.transactions names.transactions t q)
  clean_access : ∀ names (N : Namespace) (E : CoPset), (↑N : CoPset) ⊆ E →
    iprop(⊢ invariant capacity names N -∗ LogTx.auth capacity.transactions names.transactions ∅
      ={E, E \ ↑N}=∗ ∃ nodes,
      FsTop.auth capacity.top names.top nodes ∗
      ⌜∀ i node, nodes[i]? = some node → Xv6.Fs.DurableNode.Local i node⌝ ∗
      LogTx.auth capacity.transactions names.transactions ∅ ∗
      (FsTop.auth capacity.top names.top nodes ={E \ ↑N, E}=∗ True))

end MachCSL.Logic.IcacheTopRegistry
