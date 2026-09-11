import Xv6.Kernel.Correspondence
import Xv6.Kernel.MetadataProofs
import Lean.Util.CollectAxioms

/-! Enforced theorem-cone audit and kernel regression checks for sparse import.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
namespace Xv6.Kernel.Tests

theorem first_winner : listMap [(3, (1 : UInt8)), (3, 2)] 3 = some 1 := by decide

theorem source_code_hole : code 0x80005ba0 = none := by decide

theorem source_data_hole : data 0x80006000 = none := by decide

theorem source_bss_absent : fileBytes 0x8000a2a0 = none := by decide

theorem source_entry_byte : code entry = some 0x17 := by decide

end Xv6.Kernel.Tests

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if info.isTheorem && (text.startsWith "Xv6.Kernel." ||
        text.startsWith "_private.Xv6.Kernel." ||
        text.startsWith "Xv6.Generated.KernelMaps.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} kernel-map theorem cones; standard foundational axioms only."
