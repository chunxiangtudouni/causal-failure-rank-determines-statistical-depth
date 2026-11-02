module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeInit_040

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.Frame

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {Λ σ : Type*}

/-- Every physical stack read, including peek, and every write is restricted.
The frozen WritesOnly predicate alone is insufficient for frame extension. -/
def AccessesOnly (allowed : RatInput.Stack → Prop) : TM2.Stmt RatInput.Alphabet Λ σ → Prop
  | .push point _ tail | .pop point _ tail | .peek point _ tail => allowed point ∧ AccessesOnly allowed tail
  | .load _ tail => AccessesOnly allowed tail
  | .branch _ yes no => AccessesOnly allowed yes ∧ AccessesOnly allowed no
  | .goto _ | .halt => True

def accessDecidable (allowed : RatInput.Stack → Prop) [DecidablePred allowed] :
    (body : TM2.Stmt RatInput.Alphabet Λ σ) → Decidable (AccessesOnly allowed body)
  | .push _ _ tail | .pop _ _ tail | .peek _ _ tail => by
    change Decidable (_ ∧ AccessesOnly allowed tail)
    letI:=accessDecidable allowed tail
    infer_instance
  | .load _ tail => accessDecidable allowed tail
  | .branch _ yes no => by
    change Decidable (AccessesOnly allowed yes ∧ AccessesOnly allowed no)
    letI:=accessDecidable allowed yes
    letI:=accessDecidable allowed no
    infer_instance
  | .goto _ | .halt => isTrue trivial

instance (allowed : RatInput.Stack → Prop) [DecidablePred allowed]
    (body : TM2.Stmt RatInput.Alphabet Λ σ) : Decidable (AccessesOnly allowed body) := accessDecidable allowed body

def configuration (slot : RatInput.Stack) (cells : List Bool) (before : TM2.Cfg RatInput.Alphabet Λ σ) :
    TM2.Cfg RatInput.Alphabet Λ σ := ⟨before.l,before.var,Function.update before.stk slot cells⟩

theorem stepAux_configuration (allowed : RatInput.Stack → Prop) (slot : RatInput.Stack)
    (untouched : ¬allowed slot) (cells : List Bool) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : AccessesOnly allowed body) (memory : σ) (contents : RatInput.Stack → List Bool) :
    TM2.stepAux body memory (Function.update contents slot cells)=
      configuration slot cells (TM2.stepAux body memory contents) := by
  induction body generalizing memory contents with
  | push point value tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [TM2.stepAux,Function.update_of_ne different,Function.update_comm (Ne.symm different)]
    exact ih good.2 _ _
  | pop point update tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [TM2.stepAux,Function.update_of_ne different,Function.update_comm (Ne.symm different)]
    exact ih good.2 _ _
  | peek point update tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [TM2.stepAux,Function.update_of_ne different]
    exact ih good.2 _ _
  | load update tail ih => exact ih good _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test memory
    · simpa only [TM2.stepAux,selected,Bool.cond_false] using ihNo good.2 memory contents
    · simpa only [TM2.stepAux,selected,Bool.cond_true] using ihYes good.1 memory contents
  | goto target | halt => rfl

theorem step_configuration (allowed : RatInput.Stack → Prop) (slot : RatInput.Stack)
    (untouched : ¬allowed slot) (cells : List Bool) (source : Λ → TM2.Stmt RatInput.Alphabet Λ σ)
    (good : ∀ point,AccessesOnly allowed (source point)) (before : TM2.Cfg RatInput.Alphabet Λ σ) :
    TM2.step source (configuration slot cells before)=
      (TM2.step source before).map (configuration slot cells) := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => rfl
    | some point =>
      change some (TM2.stepAux (source point) memory (Function.update contents slot cells))=_
      rw [stepAux_configuration allowed slot untouched cells _ (good point)]
      rfl

theorem chain_configuration (allowed : RatInput.Stack → Prop) (slot : RatInput.Stack)
    (untouched : ¬allowed slot) (cells : List Bool) (source : Λ → TM2.Stmt RatInput.Alphabet Λ σ)
    (good : ∀ point,AccessesOnly allowed (source point)) (run : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (chain : run.IsChain (fun before after => TM2.step source before=some after)) :
    (run.map (configuration slot cells)).IsChain (fun before after => TM2.step source before=some after) := by
  induction run with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      apply List.isChain_cons_cons.mpr
      refine ⟨?_,ih later⟩
      rw [step_configuration allowed slot untouched cells source good,edge,Option.map_some]

/-- Extending a genuinely unaccessed physical stack leaves actual scanner
clock unchanged, not merely bounded by a new loose workspace estimate. -/
theorem clock_configuration (allowed : RatInput.Stack → Prop) (slot : RatInput.Stack)
    (untouched : ¬allowed slot) (cells : List Bool) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : AccessesOnly allowed body) (memory : σ) (contents : RatInput.Stack → List Bool) :
    ScannerStatement.clock body memory (Function.update contents slot cells)=
      ScannerStatement.clock body memory contents := by
  induction body generalizing memory contents with
  | push point value tail ih | pop point value tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [ScannerStatement.clock,Function.update_of_ne different,Function.update_comm (Ne.symm different)]
    rw [ih good.2]
  | peek point update tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [ScannerStatement.clock,Function.update_of_ne different]
    rw [ih good.2]
  | load update tail ih => exact ih good _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test memory
    · simpa only [ScannerStatement.clock,selected,Bool.false_eq_true,ite_false] using ihNo good.2 memory contents
    · simpa only [ScannerStatement.clock,selected,ite_true] using ihYes good.1 memory contents
  | goto target | halt => rfl

def snapshot (slot : RatInput.Stack) (cells : List Bool)
    (node : σ × (RatInput.Stack → List Bool)) : σ × (RatInput.Stack → List Bool) :=
  (node.1,Function.update node.2 slot cells)

theorem nodes_configuration (allowed : RatInput.Stack → Prop) (slot : RatInput.Stack)
    (untouched : ¬allowed slot) (cells : List Bool) (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (good : AccessesOnly allowed body) (memory : σ) (contents : RatInput.Stack → List Bool) :
    AuxWorkspace.nodes body memory (Function.update contents slot cells)=
      (AuxWorkspace.nodes body memory contents).map (snapshot slot cells) := by
  induction body generalizing memory contents with
  | push point value tail ih | pop point value tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [AuxWorkspace.nodes,List.map_cons,Function.update_of_ne different,Function.update_comm (Ne.symm different)]
    exact congrArg (fun later => (memory,Function.update contents slot cells)::later) (ih good.2 _ _)
  | peek point update tail ih =>
    have different : point≠slot := by intro same; subst point; exact untouched good.1
    simp only [AuxWorkspace.nodes,List.map_cons,Function.update_of_ne different]
    exact congrArg (fun later => (memory,Function.update contents slot cells)::later) (ih good.2 _ _)
  | load update tail ih =>
    exact congrArg (fun later => (memory,Function.update contents slot cells)::later) (ih good _ _)
  | branch test yes no ihYes ihNo =>
    cases selected : test memory
    · simpa only [AuxWorkspace.nodes,List.map_cons,selected,Bool.false_eq_true,ite_false,snapshot] using
        congrArg (fun later => (memory,Function.update contents slot cells)::later) (ihNo good.2 memory contents)
    · simpa only [AuxWorkspace.nodes,List.map_cons,selected,ite_true,snapshot] using
        congrArg (fun later => (memory,Function.update contents slot cells)::later) (ihYes good.1 memory contents)
  | goto target | halt => rfl

end B23_4_RatWordPrep.Frame
