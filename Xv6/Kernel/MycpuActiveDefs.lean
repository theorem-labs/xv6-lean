import Xv6.Kernel.MycpuFetchDefs
import Xv6.Kernel.MycpuDecodeDefs
import MachCSL.Logic.SupervisorInterruptDefs

/-! Exact active-hart continuation and a structural register prefix.
Source: generated Step.lean:321–396; SmodeCore.v:173–245. -/
namespace Xv6.Kernel.MycpuActive
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
open Step ExecutionResult extension virtaddr
open _root_.Sail

structure Shares where
  fetch : MycpuFetch.Shares
  enable : DFrac
  delegation : DFrac
  environment : DFrac
  landing : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  MycpuFetch.footprint shares.fetch ++
    [(.mie, shares.enable), (.mideleg, shares.delegation),
     (.menvcfg, shares.environment), (.elp, shares.landing), (.nextPC, .own 1)]

def interruptShares (shares : Shares) : MachCSL.Logic.SupervisorInterrupt.Shares :=
  ⟨shares.fetch.misa, shares.fetch.bare.translation.status, shares.enable, shares.delegation⟩

structure Config (rs : RegisterFile) (i : Fin 14) (region : PMA_Region) : Prop where
  fetch : MycpuFetch.Config rs i region
  interrupts : SupervisorInterrupt.Disabled rs
  decode : MycpuDecode.Config i rs
  landing : rs .elp = 0#1

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

def instbits (i : Fin 14) : BitVec 32 := BitVec.ofNat 32 (MycpuDecode.encoding i)
def prepared (i : Fin 14) (rs : RegisterFile) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .nextPC (Sail.BitVec.addInt (rs .PC) (MycpuDecode.width i))

/-- Exactly one ExecuteAs redirection; the second result is returned verbatim. -/
def executeTail [Platform] (i : Fin 14) : SailM Step := do
  let first ← execute (MycpuDecode.decoded i)
  let final ← match first with
    | .ExecuteAs other => execute other
    | other => pure other
  pure (.Step_Execute (final, instbits i))

/-- The complete generated continuation, retaining all error and trap branches. -/
def afterFetch [Platform] (step_no : Nat) (fetched : FetchResult) : SailM Step := _root_.Sail.SailME.run do
  match (ext_fetch_hook fetched) with
  | .F_Ext_Error e => (pure (Step_Ext_Fetch_Failure e))
  | .F_Error (e, addr) => (pure (Step_Fetch_Failure ((Virtaddr addr), e)))
  | .F_RVC h =>
    (do
      let _ : Unit := (sail_instr_announce h)
      let _ : Unit := (fetch_callback h)
      let instbits : BitVec 32 := (zero_extend (m := 32) h)
      let instruction ← do (ext_decode_compressed h)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg .cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg .PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted h)
                            (HAppend.hAppend ") " (← (instruction_to_str instruction)))))))))))
            (zero_extend (m := 64) (← readReg .PC))))
      else (pure ())
      if ((← (is_landing_pad_expected ())) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          if ((← (currentlyEnabled Ext_Zca)) : Bool)
          then
            (do
              writeReg .nextPC (BitVec.addInt (← readReg .PC) 2)
              let result ← (( do
                match (← (execute instruction)) with
                | .ExecuteAs other_inst => (execute other_inst)
                | result => (pure result) ) : SailME Step ExecutionResult )
              (pure (Step_Execute (result, instbits))))
          else (pure (Step_Execute ((Illegal_Instruction ()), instbits)))))
  | .F_Base w =>
    (do
      let _ : Unit := (sail_instr_announce w)
      let _ : Unit := (fetch_callback w)
      let instbits : BitVec 32 := (zero_extend (m := 32) w)
      let instruction ← do (ext_decode w)
      if ((get_config_print_instr ()) : Bool)
      then
        (pure (print_log_instr
            (HAppend.hAppend "["
              (HAppend.hAppend (Int.repr step_no)
                (HAppend.hAppend "] ["
                  (HAppend.hAppend (← (privLevel_to_str (← readReg .cur_privilege)))
                    (HAppend.hAppend "]: "
                      (HAppend.hAppend (BitVec.toFormatted (← readReg .PC))
                        (HAppend.hAppend " ("
                          (HAppend.hAppend (BitVec.toFormatted w)
                            (HAppend.hAppend ") " (← (instruction_to_str instruction)))))))))))
            (zero_extend (m := 64) (← readReg .PC))))
      else (pure ())
      if (((← (is_landing_pad_expected ())) && (LeanPaperStock.Functions.not (is_lpad_instruction instruction))) : Bool)
      then
        (do
          let r ← do (trap (make_landing_pad_exception ()))
          (pure (Step_Execute (r, instbits))))
      else
        (do
          writeReg .nextPC (BitVec.addInt (← readReg .PC) 4)
          let result ← (( do
            match (← (execute instruction)) with
            | .ExecuteAs other_inst => (execute other_inst)
            | result => (pure result) ) : SailME Step ExecutionResult )
          (pure (Step_Execute (result, instbits)))))

/-- Structural register-only progress to an actual residual body, not a claim
that the residual terminates or is safe. -/
inductive Prefix (fp : RegisterFootprint.Footprint) :
    RegisterFile → SailM α → SailM α → RegisterFile → Prop where
  | done {rs body} : Prefix fp rs body body rs
  | prefix {rs middle after} {segment : SailM β} {value} {next : β → SailM α} {body}
      (first : RegisterPlan.Returns fp rs segment value middle)
      (rest : Prefix fp middle (next value) body after) :
      Prefix fp rs (segment >>= next) body after

end Xv6.Kernel.MycpuActive
