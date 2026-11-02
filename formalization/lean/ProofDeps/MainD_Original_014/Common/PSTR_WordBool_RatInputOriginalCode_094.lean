module

public import Common.PSTR_WordBool_RatInputAPI_093
public import Common.PSTR_SYM_WordPriorOriginalRun_099

/-! One fixed original word-prior parser/exporter followed by the real
original-pair encoder. The shared port is an identical physical state. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Original

open Turing PSTRWordVM RationalControllerComputation

abbrev Prior := PSTRSymbolicWordPriorStack.Store
abbrev Store (C : Type*) := Encoder.Store (C×Prior)

inductive Label where
  | prior : PSTRSymbolicRatExport.Joined.GlobalLabel→Label
  | encoder : Encoder.Label→Label
  | done : Label
  deriving DecidableEq,Fintype

instance : Inhabited Label:=⟨.prior 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def storeMap (C : Type*) : PSTRSymbolicRatExport.Joined.GlobalMemory (C×WordNatIO.Store)≃Store C where
  toFun value:=(((value.1.1.1,value.1.2),value.2),value.1.1.2)
  invFun value:=(((value.1.1.1,value.2),value.1.1.2),value.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

def priorLabel (point : PSTRSymbolicRatExport.Joined.GlobalLabel) : Label :=
  if point=5 then .encoder (.collect 0) else .prior point

def encoderLabel (point : Encoder.Label) : Label := if point=.done then .done else .encoder point

noncomputable def program (caller : Statement C) : Label→Statement C
  | .prior point=>LabelMap.statement priorLabel (StoreIso.statement (storeMap C)
      (PSTRSymbolicRatExport.Joined.combinedProgram (C:=C×WordNatIO.Store) point))
  | .encoder point=>LabelMap.statement encoderLabel (Encoder.program (C:=C×Prior) .halt point)
  | .done=>caller

def priorConfiguration (before : PSTRSymbolicRatExport.Joined.GlobalState (C×WordNatIO.Store)) : State C :=
  LabelMap.configuration priorLabel (StoreIso.configuration (storeMap C) before)

def encoderConfiguration (before : Encoder.State (C×Prior)) : State C :=
  LabelMap.configuration encoderLabel before

def initial (context : C) (bits : List Bool) : State C :=
  priorConfiguration (PSTRSymbolicRatExport.Joined.initial (context,(false,false)) (fun _=>[]) bits)

theorem program_prior (caller : Statement C) (point : PSTRSymbolicRatExport.Joined.GlobalLabel) (proper : point≠5) :
    program caller (priorLabel point)=LabelMap.statement priorLabel (StoreIso.statement (storeMap C)
      (PSTRSymbolicRatExport.Joined.combinedProgram (C:=C×WordNatIO.Store) point)) := by
  simp only [priorLabel,proper,ite_false,program]

theorem prior_path (caller : Statement C)
    (trace : List (PSTRSymbolicRatExport.Joined.GlobalState (C×WordNatIO.Store)))
    (before final : PSTRSymbolicRatExport.Joined.GlobalState (C×WordNatIO.Store))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step PSTRSymbolicRatExport.Joined.combinedProgram a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 5) :
    (trace.map priorConfiguration).head?=some (priorConfiguration before) ∧
    (trace.map priorConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map priorConfiguration).getLast?=some (priorConfiguration final) := by
  let old:=PSTRSymbolicRatExport.Joined.combinedProgram (C:=C×WordNatIO.Store)
  let isoProgram:=StoreIso.machine (storeMap C) old
  have iso:=StoreIso.actual_path_on (storeMap C) old isoProgram trace before final first chain last
    (by intro current member point selected;rfl)
  have proper:=NativeMulLink.no_early_halt_port isoProgram 5 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped:=LabelMap.actual_path_on priorLabel isoProgram (program caller) _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
    intro current member point selected
    exact program_prior caller point (by intro same;subst point;exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (storeMap C))).map (LabelMap.configuration priorLabel)=
      trace.map priorConfiguration := by rw [List.map_map];rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem program_encoder (caller : Statement C) (point : Encoder.Label) (proper : point≠.done) :
    program caller (encoderLabel point)=LabelMap.statement encoderLabel (Encoder.program (C:=C×Prior) .halt point) := by
  simp only [encoderLabel,proper,ite_false,program]

theorem encoder_path (caller : Statement C) (trace : List (Encoder.State (C×Prior)))
    (before final : Encoder.State (C×Prior))
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (Encoder.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map encoderConfiguration).head?=some (encoderConfiguration before) ∧
    (trace.map encoderConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (trace.map encoderConfiguration).getLast?=some (encoderConfiguration final) := by
  have proper:=NativeMulLink.no_early_halt_port (Encoder.program .halt) .done rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on encoderLabel (Encoder.program .halt) (program caller) trace before final first chain last (by
    intro current member point selected
    exact program_encoder caller point (by intro same;subst point;exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem work_ne_input (slot : RatInput.Stack) (owned : Encoder.Work slot) : slot≠0 ∧ slot≠1 := by
  fin_cases slot <;> simp_all [Encoder.Work]

theorem bank_from_empty (background : RatInput.Stack→List Bool) (packet : List Bool)
    (empty : ∀ slot,Encoder.Work slot→background slot=[]) :
    Encoder.bank background packet [] [] [] [] [] [] [] []=Function.update background 15 packet := by
  funext slot
  fin_cases slot <;> first | rfl | simpa [Encoder.bank,Function.update_apply] using (empty _ (by simp [Encoder.Work])).symm

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Original
