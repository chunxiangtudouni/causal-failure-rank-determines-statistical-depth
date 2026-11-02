module

public import RootPaper_TableCost_Replay004
public import RootPaper_BudgetCost_Closed001
public import RootB236_RiskFold_TargetWidths010

/-! Operand provenance for the charged budget recursion. Every call comes
from a real already-visited report prefix. Bounds use the original budget,
the number of reports, and numerical words in the actual saved archive. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01CacheRecord252 PSTRTableRecordDecision
open RationalControllerComputation
open RootPaper.Reference
variable {I : Instance}

theorem budgetWork_origin (initial : Rat) (events : List ReferenceBudgetEvent) (call : ScalarCall I)
    (member : call∈(budgetWork (I:=I) initial events).2) :
    ∃ before event later risk,events=before++event::later ∧
      referenceBudgetPath initial before=some risk ∧ call∈(budgetStepWork event.1 event.2 risk).2 := by
  induction events generalizing initial with
  | nil => simp only [budgetWork,List.not_mem_nil] at member
  | cons event later ih =>
      simp only [budgetWork] at member
      cases one:(budgetStepWork (I:=I) event.1 event.2 initial).1 with
      | none =>
          simp only [one] at member
          exact ⟨[],event,later,initial,rfl,rfl,member⟩
      | some child =>
          simp only [one,List.mem_append] at member
          rcases member with front|tail
          · exact ⟨[],event,later,initial,rfl,rfl,front⟩
          · obtain ⟨before,next,rest,risk,shape,path,called⟩:=ih child tail
            refine ⟨event::before,next,rest,risk,?_,?_,called⟩
            · simp only [List.cons_append,shape]
            · simp only [referenceBudgetPath,←budgetStepWork_value (I:=I),one,Option.bind_some,path]

def CallBound (S D : Nat) : ScalarCall I→Prop
  | .budgetVisit kind _ risk => PSTRWordBool.RatInput.Encoder.fieldSize risk≤S ∧ RootB236.RiskFold.caseDepth kind≤D
  | .half risk => PSTRWordBool.RatInput.Encoder.fieldSize risk≤S
  | .target risk depth => 0<risk ∧ 1≤depth ∧ PSTRWordBool.RatInput.Encoder.fieldSize risk≤S ∧ depth≤D
  | .badRisk risk target => PSTRWordBool.RatInput.Encoder.fieldSize risk≤S ∧
      PSTRWordBool.RatInput.Encoder.fieldSize target≤128*(2*S+3*D+15)
  | .word _ _ _ => False

theorem budgetStep_callBound (kind : ReferenceBudgetCase) (error : Bool) (risk : Rat)
    (S D : Nat) (positive : 0<risk) (width : PSTRWordBool.RatInput.Encoder.fieldSize risk≤S)
    (depth : RootB236.RiskFold.caseDepth kind≤D) (call : ScalarCall I)
    (member : call∈(budgetStepWork kind error risk).2) : CallBound S D call := by
  cases kind with
  | infiniteRank =>
      have same : call=.budgetVisit .infiniteRank error risk := by simpa only [budgetStepWork,budgetArithmetic,List.mem_singleton] using member
      subst call
      exact ⟨width,depth⟩
  | noTool =>
      cases error with
      | true =>
          have same : call=.budgetVisit .noTool true risk := by simpa only [budgetStepWork,budgetArithmetic,ite_true,List.mem_singleton] using member
          subst call
          exact ⟨width,depth⟩
      | false =>
          simp only [budgetStepWork,budgetArithmetic,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl
          · exact ⟨width,depth⟩
          · exact width
  | finiteBad d =>
      have targetWidth : PSTRWordBool.RatInput.Encoder.fieldSize (controllerTarget risk d.val)≤128*(2*S+3*D+15) := by
        have old:=RootB236.RiskFold.target_width risk d.val positive d.pos
        change d.val≤D at depth
        omega
      cases error with
      | false =>
          simp only [budgetStepWork,budgetArithmetic,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl
          · exact ⟨width,depth⟩
          · exact width
      | true =>
          simp only [budgetStepWork,budgetArithmetic,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl
          · exact ⟨width,depth⟩
          · exact ⟨positive,d.pos,width,depth⟩
          · exact ⟨width,targetWidth⟩

theorem budgetWork_callBound (budget : Rat) (events : List ReferenceBudgetEvent) (D : Nat)
    (valid : 0<budget ∧ budget≤1/2)
    (depths : ∀ event∈events,RootB236.RiskFold.caseDepth event.1≤D)
    (call : ScalarCall I) (member : call∈(budgetWork (I:=I) (budget/2) events).2) :
    CallBound (2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*events.length+4) D call := by
  obtain ⟨before,event,later,risk,shape,path,called⟩:=budgetWork_origin (budget/2) events call member
  have count : before.length≤events.length := by rw [shape,List.length_append,List.length_cons];omega
  have width:=RootB236.RiskFold.original_path_width budget before risk valid path
  have initial : ReferenceBudgetValid (budget/2) := by constructor <;> linarith [valid.1,valid.2]
  have positive:0<risk:=(referenceBudgetPath_valid_floor before (budget/2) risk initial path).1.1
  have present : event∈events := by rw [shape];exact List.mem_append_right _ List.mem_cons_self
  exact budgetStep_callBound event.1 event.2 risk _ D positive (by omega) (depths event present) call called

theorem decoded_depth (q : Nat) (packet : List Nat) (kind : ReferenceBudgetCase)
    (selected : recordKind q packet=some kind) :
    RootB236.RiskFold.caseDepth kind=0 ∨ RootB236.RiskFold.caseDepth kind∈packet := by
  cases packet with
  | nil => cases selected
  | cons current tail =>
    cases tail with
    | nil => cases selected
    | cons good tail =>
      cases tail with
      | nil => cases selected
      | cons bad tail =>
        cases tail with
        | nil => cases selected
        | cons tool later =>
          change encodedKind q current bad=some kind at selected
          unfold encodedKind at selected
          split_ifs at selected
          all_goals cases Option.some.inj selected
          all_goals simp only [RootB236.RiskFold.caseDepth,List.mem_cons]
          all_goals tauto

theorem archive_kind_depth (q : Nat) (records : List Nat) (index : Nat) (kind : ReferenceBudgetCase)
    (selected : recordKind q (readRecord records index)=some kind) :
    RootB236.RiskFold.caseDepth kind≤records.sum := by
  rcases decoded_depth q (readRecord records index) kind selected with zero|present
  · omega
  · have member : RootB236.RiskFold.caseDepth kind∈records :=
      List.mem_of_mem_drop (List.mem_of_mem_take present)
    exact List.le_sum_of_mem member

def CacheDepth (records : List Nat) (cache : ReferenceReplayCache I) : Prop :=
  ∀ event∈cache.events,RootB236.RiskFold.caseDepth event.1≤records.sum

end RootPaper.TableCost
