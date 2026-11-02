module

public import PSTR_WordBool_WordOutput_Syntax_001

/-! Readonly caller context and hit/map registers, including primitive
internal snapshots. The property is discharged for this concrete source. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def Readonly {Λ : Type*} : TM2.Stmt RatInput.Alphabet Λ (Store C) → Prop
  | .push _ _ tail=>Readonly tail
  | .peek _ update tail | .pop _ update tail=>
      (∀ memory value,(update memory value).1.1=memory.1.1) ∧ Readonly tail
  | .load update tail=>(∀ memory,(update memory).1.1=memory.1.1) ∧ Readonly tail
  | .branch _ yes no=>Readonly yes ∧ Readonly no
  | .goto _ | .halt=>True

theorem readonly_labels {Λ Ω : Type*} (mapping : Λ → Ω) (body : TM2.Stmt RatInput.Alphabet Λ (Store C)) :
    Readonly (LabelMap.statement mapping body) ↔ Readonly body := by
  induction body <;> simp only [LabelMap.statement,Readonly, *]

theorem readonly_put (bits : List Bool) (next : Statement C) (good : Readonly next) : Readonly (putBits bits next) := by
  induction bits generalizing next with
  | nil=>exact good
  | cons bit later ih=>exact ih _ good

theorem readonly_drop (bits : List Bool) (next : Statement C) (good : Readonly next) : Readonly (dropBits bits next) := by
  induction bits with
  | nil=>exact good
  | cons bit later ih=>exact ⟨by intros;rfl,ih⟩

theorem readonly_old_prefix (bits : List Bool) (next : RatInput.Encoder.Statement (C × Bool × Bool))
    (good : Readonly next) : Readonly (RatInput.Encoder.putPrefix bits next) := by
  induction bits generalizing next with
  | nil=>exact good
  | cons bit later ih=>exact ih _ good

theorem readonly_old_program (point : RatInput.Encoder.Label) :
    Readonly (RatInput.Encoder.program (C:=C × Bool × Bool) .halt point) := by
  cases point with
  | finish=>exact readonly_old_prefix _ _ trivial
  | done=>trivial
  | collect point=>
    fin_cases point
    all_goals
      dsimp [RatInput.Encoder.program,LabelMap.statement,StoreIso.statement,StackIso.statement,
        RatInput.program,RatInput.fieldBody,RatInput.restoreBody,PSTRSymbolicNaturalExport.program,Readonly]
      repeat' constructor
      all_goals (intros; rfl)
  | reverseNum | reverseDen=>
    all_goals
      dsimp [RatInput.Encoder.program,LabelMap.statement,StackIso.statement,RatOutput.program,Readonly]
      repeat' constructor
      all_goals (intros; rfl)
  | den point | num point=>
    fin_cases point
    all_goals
      dsimp [RatInput.Encoder.program,LabelMap.statement,StackIso.statement,WordNatIO.callerProgram,
        WordNatIO.program,WordNatIO.jump,ContextLift.statement,Readonly]
      repeat' constructor
      all_goals (intros; rfl)

theorem program_readonly (point : Label) : Readonly (program (C:=C) .halt point) := by
  cases point with
  | collect point=>exact (readonly_labels _ _).mpr (readonly_old_program point)
  | suffix point=>exact (readonly_labels _ _).mpr (readonly_old_program point)
  | prepare=>
    refine ⟨by intros;rfl,?_⟩
    constructor <;> apply readonly_put
    all_goals constructor <;> apply readonly_put <;> trivial
  | trim=>exact readonly_drop _ _ (readonly_put _ _ trivial)
  | done=>trivial

theorem nodes_readonly {Λ : Type*} (body : TM2.Stmt RatInput.Alphabet Λ (Store C)) (good : Readonly body)
    (memory : Store C) (contents : Stack → List Bool) :
    ∀ node∈AuxWorkspace.nodes body memory contents,node.1.1.1=memory.1.1 := by
  induction body generalizing memory contents with
  | push slot value tail ih=>
    intro node member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · exact ih good _ _ node later
  | peek slot update tail ih=>
    intro node member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · exact (ih good.2 _ _ node later).trans (good.1 memory _)
  | pop slot update tail ih=>
    intro node member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · exact (ih good.2 _ _ node later).trans (good.1 memory _)
  | load update tail ih=>
    intro node member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · exact (ih good.2 _ _ node later).trans (good.1 memory)
  | branch test yes no ihYes ihNo=>
    intro node member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · cases choice : test memory
      · exact ihNo good.2 memory contents node (by simpa only [choice,Bool.false_eq_true,ite_false] using later)
      · exact ihYes good.1 memory contents node (by simpa only [choice,ite_true] using later)
  | goto target=>intro node member;have same:=List.mem_singleton.mp member;subst node;rfl
  | halt=>intro node member;have same:=List.mem_singleton.mp member;subst node;rfl

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
