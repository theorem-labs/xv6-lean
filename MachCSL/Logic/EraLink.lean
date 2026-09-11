import MachCSL.Logic.EraProofs
import MachCSL.Logic.EraRegistryProofs
import MachCSL.Logic.HeapLink
import MachCSL.Logic.DiskLink
import MachCSL.Logic.GlobalRegistersLink
import MachCSL.Logic.DeviceLink
import MachCSL.Logic.ReservationLink
import MachCSL.Logic.TsoInterpProofs

namespace MachCSL.Logic.Era

theorem contracts {GF : Iris.BundledGFunctors} (c : Capacity GF) : Contracts c :=
  ⟨GlobalRegisters.globalRegisterSpec c.registers (Registers.registerSpec c.registers),
    Heap.heapSpec c.heap, Device.deviceSpec c.devices, Disk.diskSpec c.disk,
    Reservations.reservationSpec c.reservations, Tso.Interp.interpSpec c.tso⟩

theorem registryEraSpec : EraSpec capacity := eraSpec capacity (contracts capacity)

end MachCSL.Logic.Era
