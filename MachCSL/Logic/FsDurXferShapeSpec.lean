import MachCSL.Logic.FsDurXferShapeDefs

namespace MachCSL.Logic.FsDurXferShape
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState FsDurXferRuns
variable {GF : BundledGFunctors}

structure ShapeSpec (view : FsView.View GF) : Prop where
  inodeRuns : ∀ sb i node, FsState.inodePhi view sb i node ⊢ ⌜NodeLens node⌝ ∗ phiRuns view (FsDurXferShape.inodeRuns sb i node)
  inodeOfRuns : ∀ sb i node, NodeLens node → phiRuns view (FsDurXferShape.inodeRuns sb i node) ⊢ FsState.inodePhi view sb i node
  poolRuns : ∀ nb used, FsState.freePool view nb used ⊢ ∃ pool, ⌜PoolPM (FsState.poolIndices nb) used pool⌝ ∗ phiRuns view (FsDurXferShape.poolRuns pool)
  poolOfRuns : ∀ nb used pool, PoolPM (FsState.poolIndices nb) used pool → phiRuns view (FsDurXferShape.poolRuns pool) ⊢ FsState.freePool view nb used
  footprintRuns : ∀ state, FsState.footprint view (.own 1) state ⊢ ∃ pool, ⌜Shape state pool⌝ ∗ phiRuns view (fsRuns state pool)
  footprintOfRuns : ∀ state pool, Shape state pool → phiRuns view (fsRuns state pool) ⊢ FsState.footprint view (.own 1) state
  fractionalRuns : ∀ dq state, FsState.footprint view dq state ⊢ ∃ pool, ⌜Shape state pool⌝ ∗ phiRunsQ view (atShare dq (fsRuns state pool))
  fractionalOfRuns : ∀ dq state pool, Shape state pool → phiRunsQ view (atShare dq (fsRuns state pool)) ⊢ FsState.footprint view dq state

end MachCSL.Logic.FsDurXferShape
