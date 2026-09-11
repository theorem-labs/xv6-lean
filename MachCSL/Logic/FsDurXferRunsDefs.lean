import MachCSL.Logic.FsDurBytesDefs
import MachCSL.Logic.FsViewLink

/-! Exact FsDurXfer §§0–2d run carriers and native predicates. Runs use
signed addresses, arbitrary byte lists, and positional disjointness. -/
namespace MachCSL.Logic.FsDurXferRuns
open Iris Iris.Std Iris.BI Iris.CMRA MachCSL.Memory

abbrev Run := (Int × Int) × List Byte
def runBlock (run : Run) : Int := run.1.1
def runOffset (run : Run) : Int := run.1.2
def runBytes (run : Run) : List Byte := run.2
def runMap (run : Run) : FsDurBytes.ByteMap :=
  FsDurBytes.byteRun (runBlock run * 1024 + runOffset run) (runBytes run)
def runUnion (runs : List Run) : FsDurBytes.ByteMap :=
  runs.foldr (fun run rest => FsDurBytes.leftUnion (runMap run) rest) ∅
def RunsDisjoint (runs : List Run) : Prop :=
  ∀ (k j : Nat) r1 r2, k ≠ j → runs[k]? = some r1 → runs[j]? = some r2 →
    PartialMap.disjoint (M := Disk.ImageMap) (runMap r1) (runMap r2)

abbrev QRun := DFrac × Run
def atShare (dq : DFrac) (runs : List Run) : List QRun := runs.map (dq, ·)
def strip (runs : List QRun) : List Run := runs.map Prod.snd
def SharesOK (runs : List QRun) : Prop :=
  ∀ (k : Nat) run, runs[k]? = some run → ¬✓ (run.1 • run.1)

variable {GF : BundledGFunctors}
def phiMap (view : FsView.View GF) (bytes : FsDurBytes.ByteMap) : IProp GF := FsDurBytes.byteLedger view bytes
def phiRuns (view : FsView.View GF) (runs : List Run) : IProp GF :=
  bigSepL (fun _ run => FsView.byteRange view (runBlock run) (runOffset run) (runBytes run)) runs
def phiMapQ (view : FsView.View GF) (dq : DFrac) (bytes : FsDurBytes.ByteMap) : IProp GF :=
  bigSepM (M := Disk.ImageMap) (fun a v => view.phi dq a v) bytes
def phiRunsQ (view : FsView.View GF) (runs : List QRun) : IProp GF :=
  bigSepL (fun _ run => FsView.byteRangeQ view run.1 (runBlock run.2) (runOffset run.2) (runBytes run.2)) runs

def PhiAgree (view : FsView.View GF) (authority : IProp GF) (bytes : FsDurBytes.ByteMap) : Prop :=
  ∀ dq a byte, authority ∗ view.phi dq a byte ⊢ ⌜bytes[a]? = some byte⌝

end MachCSL.Logic.FsDurXferRuns
