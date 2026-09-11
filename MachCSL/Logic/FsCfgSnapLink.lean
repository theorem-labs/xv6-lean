import MachCSL.Logic.FsCfgSnapProofs
import MachCSL.Logic.FsCrashLink

namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.BI

theorem registryRouteSpec : RouteSpec FsCrash.nativeBootstrapCapacity :=
  routeSpec FsCrash.nativeBootstrapCapacity

theorem registryReadSpec : ReadSpec FsCrash.nativeBootstrapCapacity :=
  readSpec FsCrash.nativeBootstrapCapacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc FsCrash.registry] :
    Spec FsCrash.nativeBootstrapCapacity := actual FsCrash.nativeBootstrapCapacity

theorem snapshot_disk_same : FsCrash.nativeBootstrapCapacity.crash.disk =
    FsCrash.nativeBootstrapCapacity.boot.era.disk := rfl

theorem physical_name_retained (template : DiskClient.Names) (era : Era.Record) :
    (FsBootRecovery.forEra template era).img = era.disk := rfl

end MachCSL.Logic.FsCfgSnap
