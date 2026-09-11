import MachCSL.Logic.JalBootResourcesDefs
import MachCSL.Logic.EventWPProofs
import MachCSL.Logic.RegisterProofs
import MachCSL.Logic.ReservationProofs

namespace MachCSL.Logic.JalBootResources
open Iris Iris.Std Iris.BI MachCSL.Machine
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap Iris.Std.LawfulFiniteMap
variable {GF : BundledGFunctors}

theorem registers_split (capacity : Registers.Capacity GF) (names : GlobalRegisters.Names)
    (files : CPU → RegisterFile) :
    iprop(⊢ GlobalRegisters.allInitialCells capacity names files -∗ cpuRegisters capacity names files ∗
      PlicWP.wireCells capacity names (fun cpu => files cpu .sig_seip) (fun cpu => files cpu .sig_meip)) := by
  unfold GlobalRegisters.allInitialCells cpuRegisters PlicWP.wireCells
  iintro H
  iapply BigSepS.bigSepS_sep.1
  iapply BigSepS.bigSepS_mono $$ H
  intro cpu _
  exact (EventWP.initialCells_split ⟨Registers.initialMap_lookup⟩ capacity (names cpu) (files cpu)).1

theorem resvMap_ofSet (values : CPU → Reservations.Value) :
    Reservations.resvMap values =
      (Iris.Std.FiniteMap.ofSetWith values GlobalRegisters.allCPUs : Reservations.ReservationMap Reservations.Value) := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro cpu
  change get? (Reservations.resvMap values) cpu = get? (Iris.Std.FiniteMap.ofSetWith (M := Reservations.ReservationMap) values GlobalRegisters.allCPUs) cpu
  rw [Reservations.resvMap_lookup]
  symm
  exact get?_ofList_some (List.mem_map_of_mem (Iris.Std.FiniteSet.mem_toList.mpr
    (GlobalRegisters.mem_allCPUs cpu))) noDupKeys_map_pair

theorem reservations_split (capacity : Reservations.Capacity GF) (γ : GName)
    (values : CPU → Reservations.Value) :
    iprop(Reservations.allFragments capacity γ values ⊣⊢ cpuReservations capacity γ values) := by
  letI := capacity.reservations
  unfold Reservations.allFragments cpuReservations Reservations.resvFrag
  rw [resvMap_ofSet]
  exact BigSepM.bigSepM_ofSetWith _ _ _

end MachCSL.Logic.JalBootResources
