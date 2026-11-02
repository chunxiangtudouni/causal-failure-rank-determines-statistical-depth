module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludeCode_057

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordVM

variable {C : Type*}

theorem copy_path (caller : Statement C) (run : List (WholeCopy.State (HeaderNat.Store (OriginalFee.Store C))))
    (before final : WholeCopy.State (HeaderNat.Store (OriginalFee.Store C))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (WholeCopy.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map copyCfg).head?=some (copyCfg before) ∧
    (run.map copyCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map copyCfg).getLast?=some (copyCfg final) := by
  let old:=WholeCopy.program (C := HeaderNat.Store (OriginalFee.Store C)) .halt
  let isoProgram:=StoreIso.machine (copyIso C) old
  have iso:=StoreIso.actual_path_on (copyIso C) old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on copyLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [copyLabel,notDone,ite_false,program]
      rfl)
  have maps : (run.map (StoreIso.configuration (copyIso C))).map (LabelMap.configuration copyLabel)=run.map copyCfg := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem rewind_path (caller : Statement C) (run : List (Rewind.State (HeaderNat.Store (OriginalFee.Store C))))
    (before final : Rewind.State (HeaderNat.Store (OriginalFee.Store C))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Rewind.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map rewindCfg).head?=some (rewindCfg before) ∧
    (run.map rewindCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map rewindCfg).getLast?=some (rewindCfg final) := by
  let old:=Rewind.program (C := HeaderNat.Store (OriginalFee.Store C)) .halt
  let isoProgram:=StoreIso.machine (copyIso C) old
  have iso:=StoreIso.actual_path_on (copyIso C) old isoProgram run before final first chain last
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on rewindLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [rewindLabel,notDone,ite_false,program]
      rfl)
  have maps : (run.map (StoreIso.configuration (copyIso C))).map (LabelMap.configuration rewindLabel)=run.map rewindCfg := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem header_path (caller : Statement C) (run : List (HeaderNat.State (WholeCopy.Store (OriginalFee.Store C))))
    (before final : HeaderNat.State (WholeCopy.Store (OriginalFee.Store C))) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (HeaderNat.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map headerCfg).head?=some (headerCfg before) ∧
    (run.map headerCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map headerCfg).getLast?=some (headerCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (HeaderNat.program .halt) .done rfl run final chain last active
  have mapped:=LabelMap.actual_path_on headerLabel (HeaderNat.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [headerLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem fee_path (caller : Statement C) (registers : Extra) (run : List (OriginalFee.State C))
    (before final : OriginalFee.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (OriginalFee.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (feeCfg registers)).head?=some (feeCfg registers before) ∧
    (run.map (feeCfg registers)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (feeCfg registers)).getLast?=some (feeCfg registers final) := by
  let old:=OriginalFee.program (C := C) .halt
  let liftedProgram : OriginalFee.Label → TM2.Stmt RatInput.Alphabet OriginalFee.Label (Extra × OriginalFee.Store C) :=
    ContextLift.machine old
  have lifted:=ContextLift.actual_path old registers run before final first chain last
  let isoProgram:=StoreIso.machine (feeIso C) liftedProgram
  have iso:=StoreIso.actual_path_on (feeIso C) liftedProgram isoProgram
    (run.map (ContextLift.configuration registers)) _ _ lifted.1 lifted.2.1 lifted.2.2.1
    (by intro current member point selected; rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on feeLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [feeLabel,notDone,ite_false,program]
      rfl)
  have maps : ((run.map (ContextLift.configuration registers)).map (StoreIso.configuration (feeIso C))).map
      (LabelMap.configuration feeLabel)=run.map (feeCfg registers) := by
    simp only [List.map_map]
    rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end B23_4_RatWordPrep.OriginalPrelude
