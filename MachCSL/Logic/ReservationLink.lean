import MachCSL.Logic.ReservationRegistry
import MachCSL.Logic.ReservationProofs
import Lean.Util.CollectAxioms

namespace MachCSL.Logic.Reservations

theorem registryReservationSpec : ReservationSpec registryCapacity := reservationSpec registryCapacity

end MachCSL.Logic.Reservations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let text := name.toString
    if text.startsWith "MachCSL.Logic.Reservations." ||
        text.startsWith "_private.MachCSL.Logic.Reservation" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} reservation declarations; standard foundational axioms only."
