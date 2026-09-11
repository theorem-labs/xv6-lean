import MachCSL.Logic.SupervisorBitsDefs
import MachCSL.Logic.RegisterPlanDefs

/-! Source `WpGprCsrwCommon.v:240–301`, `WpGprCsrwC.v:1362–1429,1675–1702`,
and `WpSieFlipBits.v:289–345`. The pure value below specializes the actual
generated legalizer to enabled S/U, supported virtual memory and supported
Zicfilp. It deliberately preserves arbitrary saved ELP bits. -/
namespace MachCSL.Logic.SupervisorSstatusOff
open Iris MachCSL.Machine LeanPaperStock.Functions

def misaValue : BitVec 64 := 0x800000000014112d#64

def writeValue (ms : BitVec 64) : BitVec 64 :=
  lower_mstatus ms &&& ~~~(2#64)

/-- Exact source symbolic legalized value; the actual finite read plan is
proved separately. Unsupported nominal MPP falls back to User. -/
def legalized (old value : BitVec 64) : BitVec 64 :=
  let mpp := if SupervisorBits.haveNominalValue (_get_Mstatus_MPP value)
    then _get_Mstatus_MPP value else privLevel_to_bits .User
  let next :=
    _update_Mstatus_SIE
      (_update_Mstatus_MIE
        (_update_Mstatus_SPIE
          (_update_Mstatus_MPIE
            (_update_Mstatus_SPP
              (_update_Mstatus_MPP
                (_update_Mstatus_VS
                  (_update_Mstatus_FS
                    (_update_Mstatus_XS
                      (_update_Mstatus_MPRV
                        (_update_Mstatus_SUM
                          (_update_Mstatus_MXR
                            (_update_Mstatus_TVM
                              (_update_Mstatus_TW
                                (_update_Mstatus_TSR
                                  (_update_Mstatus_SPELP
                                    (_update_Mstatus_MPELP old (_get_Mstatus_MPELP value))
                                    (_get_Mstatus_SPELP value))
                                  (_get_Mstatus_TSR value))
                                (_get_Mstatus_TW value))
                              (_get_Mstatus_TVM value))
                            (_get_Mstatus_MXR value))
                          (_get_Mstatus_SUM value))
                        (_get_Mstatus_MPRV value))
                      (extStatus_map_forwards .Off))
                    (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS value)))
                  (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS value)))
                mpp)
              (_get_Mstatus_SPP value))
            (_get_Mstatus_MPIE value))
          (_get_Mstatus_SPIE value))
        (_get_Mstatus_MIE value))
      (_get_Mstatus_SIE value)
  let dirty := (extStatus_map_backwards (_get_Mstatus_FS next) == .Dirty) ||
    ((extStatus_map_backwards (_get_Mstatus_XS next) == .Dirty) ||
      (extStatus_map_backwards (_get_Mstatus_VS next) == .Dirty))
  _update_Mstatus_SD next (bool_to_bit dirty)

def result (ms : BitVec 64) : BitVec 64 :=
  legalized ms (lift_sstatus ms (writeValue ms))

def program (ms : BitVec 64) : SailM (BitVec 64) :=
  legalize_sstatus ms (writeValue ms)

end MachCSL.Logic.SupervisorSstatusOff
