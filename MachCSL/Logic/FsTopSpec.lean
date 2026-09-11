import MachCSL.Logic.FsTopDefs

namespace MachCSL.Logic.FsTop
open Iris Iris.Std Iris.CMRA Iris.BI

structure FsTopSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  lookup : ∀ γ nodes dq i node, iprop(⊢ auth capacity γ nodes -∗ fragQ capacity γ dq i node -∗
    ⌜nodes[i]? = some node⌝)
  agree : ∀ γ dq1 dq2 i left right, iprop(⊢ fragQ capacity γ dq1 i left -∗
    fragQ capacity γ dq2 i right -∗ ⌜left = right⌝)
  split : ∀ γ i node (q1 q2 : Qp),
    fragQ capacity γ (.own (q1 + q2)) i node ⊣⊢
      fragQ capacity γ (.own q1) i node ∗ fragQ capacity γ (.own q2) i node
  update : ∀ γ nodes i old new, iprop(⊢ auth capacity γ nodes -∗ frag capacity γ i old ==∗
    auth capacity γ (nodes.insert i new) ∗ frag capacity γ i new)
  allocate : ∀ nodes, iprop(⊢ |==> ∃ γ, auth capacity γ nodes ∗ allFragments capacity γ nodes)

end MachCSL.Logic.FsTop
