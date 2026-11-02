module

public import B23_4_RatWordPrep_SeqCmp_WordInputSizes_138

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C σ Λ Ω : Type*}

/-- Static store reassociation preserves the exact physical scanner cost. -/
theorem clock_storeIso (iso : σ ≃ Store C) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (memory : σ) (slots : RatInput.Stack → List Bool) :
    ScannerStatement.clock (StoreIso.statement iso body) (iso memory) slots=
      ScannerStatement.clock body memory slots := by
  induction body generalizing memory slots with
  | push slot value tail ih =>
    simpa only [StoreIso.statement,ScannerStatement.clock,Equiv.symm_apply_apply] using
      congrArg (fun clock => (slots slot).length+(value memory::slots slot).length+2+clock)
        (ih memory (Function.update slots slot (value memory::slots slot)))
  | peek slot value tail ih =>
    simpa only [StoreIso.statement,ScannerStatement.clock,Equiv.symm_apply_apply] using
      congrArg (fun clock => (slots slot).length+(slots slot).length+2+clock)
        (ih (value memory (slots slot).head?) slots)
  | pop slot value tail ih =>
    simpa only [StoreIso.statement,ScannerStatement.clock,Equiv.symm_apply_apply] using
      congrArg (fun clock => (slots slot).length+(slots slot).tail.length+2+clock)
        (ih (value memory (slots slot).head?) (Function.update slots slot (slots slot).tail))
  | load value tail ih =>
    simpa only [StoreIso.statement,ScannerStatement.clock,Equiv.symm_apply_apply] using ih (value memory) slots
  | branch test yes no ihYes ihNo =>
    cases choice : test memory <;>
      simp only [StoreIso.statement,ScannerStatement.clock,Equiv.symm_apply_apply,choice,
        Bool.false_eq_true,ite_false,ite_true,ihYes,ihNo]
  | goto target | halt => rfl

theorem clock_labelMap (mapping : Λ → Ω) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (memory : σ) (slots : RatInput.Stack → List Bool) :
    ScannerStatement.clock (LabelMap.statement mapping body) memory slots=
      ScannerStatement.clock body memory slots := by
  induction body generalizing memory slots with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih =>
    simp only [LabelMap.statement,ScannerStatement.clock,ih]
  | load value _ ih => exact ih (value memory) slots
  | branch test _ _ yes no =>
    cases choice : test memory <;>
      simp only [LabelMap.statement,ScannerStatement.clock,choice,Bool.false_eq_true,ite_false,ite_true,yes,no]
  | goto _ | halt => rfl

def stateClock {τ Ψ : Type*} (source : Ψ → TM2.Stmt RatInput.Alphabet Ψ τ)
    (current : TM2.Cfg RatInput.Alphabet Ψ τ) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

def traceClockSum {τ Ψ : Type*} (source : Ψ → TM2.Stmt RatInput.Alphabet Ψ τ)
    (trace : List (TM2.Cfg RatInput.Alphabet Ψ τ)) : Nat :=
  (trace.dropLast.map (stateClock source)).sum

def mappedCfg (iso : σ ≃ Store C) (rename : Λ → Label) (current : TM2.Cfg RatInput.Alphabet Λ σ) : State C :=
  LabelMap.configuration rename (StoreIso.configuration iso current)

theorem mapped_clock (iso : σ ≃ Store C) (rename : Λ → Label)
    (source : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (current : TM2.Cfg RatInput.Alphabet Λ σ)
    (same : ∀ point,current.l=some point→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (source point))) :
    stateClock (program caller) (mappedCfg iso rename current)=stateClock source current := by
  cases current with
  | mk point memory slots =>
    cases point with
    | none => rfl
    | some point =>
      change ScannerStatement.clock (program caller (rename point)) (iso memory) slots=
        ScannerStatement.clock (source point) memory slots
      rw [same point rfl,clock_labelMap,clock_storeIso]

/-- Equality on the actual proper trace, so a parent Sigma-clock bound
is consumed on the same mapped witness without a second run. -/
theorem mapped_clockSum (iso : σ ≃ Store C) (rename : Λ → Label)
    (source : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (same : ∀ current∈trace.dropLast,∀ point,current.l=some point→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (source point))) :
    traceClockSum (program caller) (trace.map (mappedCfg iso rename))=traceClockSum source trace := by
  unfold traceClockSum
  rw [←List.map_dropLast,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro current member
  exact mapped_clock iso rename source caller current (same current member)

/-- Exact internal-node transport. Every stack snapshot is unchanged;
only its finite control-store address is statically reassociated. -/
theorem mapped_nodes (iso : σ ≃ Store C) (rename : Λ → Label)
    (source : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (point : Λ) (memory : σ) (slots : RatInput.Stack → List Bool)
    (same : program caller (rename point)=LabelMap.statement rename (StoreIso.statement iso (source point))) :
    AuxWorkspace.nodes (program caller (rename point)) (iso memory) slots=
      (AuxWorkspace.nodes (source point) memory slots).map (StoreIso.snapshot iso) := by
  rw [same,LabelMap.nodes_statement,StoreIso.nodes_configuration]

theorem mapped_length (iso : σ ≃ Store C) (rename : Λ → Label)
    (trace : List (TM2.Cfg RatInput.Alphabet Λ σ)) :
    (trace.map (mappedCfg iso rename)).length=trace.length := List.length_map ..

end B23_4_RatWordPrep.WordFinish.Resources
