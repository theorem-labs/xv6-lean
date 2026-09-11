import MachCSL.Logic.LogEpochDefs
import Xv6.Fs.InodeRegionImageDefs

namespace MachCSL.Logic.IcacheEpoch
open Iris Iris.BI Xv6.Fs Xv6.Fs.SnapshotConfig

/-- The log names and per-inum observation names are supplied by the same era. -/
structure Names where
  logEpoch : GName
  logged : GName
  observation : Int → GName
  inodeStart : Int

def iblkOf (names : Names) (inum : Int) : Int := inum / 16 + names.inodeStart

variable {GF : BundledGFunctors} (capacity : LogEpoch.Capacity GF) (names : Names)

def izrcpt (inum : Int) (record : Dinode) (value : Nat) : IProp GF :=
  iprop(⌜record.nlink.toNat = 0⌝ → (⌜value = 0⌝ ∨ ∃ epoch : Nat,
    LogEpoch.logged_at capacity names.logged epoch (iblkOf names inum) ∗ ⌜value ≤ epoch⌝))

def ireg_ep (inum : Int) (record : Dinode) : IProp GF :=
  iprop(∃ value : Nat, LogEpoch.epochAuth capacity (names.observation inum) value ∗
    LogEpoch.log_epoch_lb capacity names.logEpoch value ∗ izrcpt capacity names inum record value)

def nlz_obs (inum : Int) (epoch : Nat) : IProp GF :=
  LogEpoch.log_epoch_lb capacity (names.observation inum) epoch

end MachCSL.Logic.IcacheEpoch
