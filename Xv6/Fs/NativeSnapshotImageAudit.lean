import Xv6.Fs.NativeSnapshotImage
import Lean

/-! Reusable whole-environment audit of designated initial allocation callers.
Run `audit_fs_initial_allocation` after importing the full project umbrellas in
CI. Running it here also checks the concrete leaf's imported closure. -/
open Lean Elab Command

elab "audit_fs_initial_allocation" : command => do
  let env ← getEnv
  let generic := #[
    (`MachCSL.Logic.FsDurSnapshot.Initial.snap_bytes_alloc, `MachCSL.Logic.FsDurSnapshotAllocProofs),
    (`MachCSL.Logic.FsDurSnapshot.Initial.fs_snap_alloc, `MachCSL.Logic.FsDurSnapshotAllocProofs),
    (`MachCSL.Logic.FsDurSnapshot.Initial.P_dur_alloc, `MachCSL.Logic.FsDurSnapshotAllocProofs),
    (`MachCSL.Logic.FsDurSnapshot.Initial.initialSpec, `MachCSL.Logic.FsDurSnapshotAllocProofs),
    (`MachCSL.Logic.FsDurSnapshot.Initial.preserve_physical_authority, `MachCSL.Logic.FsDurSnapshotLink),
    (`MachCSL.Logic.FsDurSnapshot.Initial.preserve_map_authority, `MachCSL.Logic.FsDurSnapshotLink)]
  let literal := #[
    (`Xv6.Fs.Image.NativeSnapshot.allocate_snapshot, `Xv6.Fs.NativeSnapshotImage),
    (`Xv6.Fs.Image.NativeSnapshot.allocate_durable, `Xv6.Fs.NativeSnapshotImage),
    (`Xv6.Fs.Image.NativeSnapshot.allocate_with_physical_authority, `Xv6.Fs.NativeSnapshotImage)]
  let approved := generic ++ literal
  let watched := approved.map Prod.fst
  for (name, expectedModule) in approved do
    let some info := env.find? name | throwError "Missing designated initial allocation declaration {name}"
    unless info.isTheorem do throwError "Expected checked allocation theorem {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing physical origin for {name}"
    unless env.header.moduleNames[idx.toNat]! == expectedModule do
      throwError "Unexpected defining module for initial allocation declaration {name}"
  let mut calls : Nat := 0
  for (name, info) in env.constants.toList do
    let mut dependencies := info.type.getUsedConstants
    if let some body := info.value? (allowOpaque := true) then dependencies := dependencies ++ body.getUsedConstants
    if let .inductInfo value := info then dependencies := dependencies ++ value.ctors.toArray
    for target in watched do
      if dependencies.contains target then
        unless watched.contains name do
          throwError "Unclassified initial snapshot allocation caller {name} references {target}; runtime code must use source-instance transfer"
        calls := calls + 1
  unless calls == 9 do throwError "Expected 9 reviewed initial-allocation call edges, found {calls}"
  logInfo m!"Initial snapshot call graph: {generic.size} generic allocation/wrapper declarations, {literal.size} designated literal initial callers, {calls} approved direct edges; no other caller in the current imported environment."

audit_fs_initial_allocation
