module

public import Common.PSTR_WordBool_RatOutputRun_077

/-! Whole-Tape output yields a real finite prefix through its TRUE footer.
ALL remaining finite cells are paid pops. No exact finite R or empty L is
inferred from ListBlank;079 discharges this internal interface using073. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput

open Turing RationalControllerComputation PA17TMRatArithmeticParse002 PSTRWordVM

variable {C : Type*}

theorem encodeNat_one : encodeNat 1 = [true,false,true] := by decide

theorem singleton_format (value : Rat) :
    encode [.rational value] = rawInput (sign value) (numeratorDigits value) (denominatorDigits value) [] := by
  simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [encodeNat_one,rational_datum]
  simp only [rawInput,List.append_assoc,List.cons_append,List.nil_append]

theorem finite_singleton (value : Rat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (encode [.rational value])) :
    ∃ padding, right = rawInput (sign value) (numeratorDigits value) (denominatorDigits value) padding := by
  let front := [true,false,true,true,sign value] ++ rawField (numeratorDigits value) ++ rawField (denominatorDigits value)
  obtain ⟨padding,shape⟩ := PSTRSymbolicNaturalExport.finite_marked_prefix front [] right
    (by simpa only [singleton_format,rawInput,front,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using same)
  exact ⟨padding,by simpa only [front,rawInput,List.append_assoc,List.cons_append,List.nil_append] using shape⟩

theorem actual_singleton_reader (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : Store) (value : Rat) (right left counter target : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (encode [.rational value])) :
    ∃ trace : List (State C),
      trace.head? = some (state background 0 context memory right left counter target) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some (state background 8 context (false,false) [] [] counter
        (PSTRSymbolicRatExport.packet (sign value) (numeratorDigits value) (denominatorDigits value) target)) ∧
      trace.length ≤ left.length+2*right.length+16 ∧
      ∀ current ∈ trace, Safe background context
        (outside background+right.length+left.length+counter.length+target.length+8) current := by
  obtain ⟨padding,shape⟩ := finite_singleton value right same
  subst right
  obtain ⟨trace,head,chain,last,count,safe⟩ := actual_reader caller background context memory
    (sign value) (numeratorDigits value) (denominatorDigits value) padding left counter target
  refine ⟨trace,head,chain,last,?_,?_⟩
  · rw [rawInput_length]
    omega
  · intro current member
    apply safe_mono (safe current member)
    rw [rawInput_length]
    dsimp [massBound]
    omega

theorem program_actions (caller : Statement C) (point : Label) (proper : point ≠ 8) :
    ScannerClock.actions (program caller point) ≤ 8 := by
  fin_cases point
  all_goals first | exact False.elim (proper rfl) | simp [program,ScannerClock.actions,jump]

theorem program_pushes (caller : Statement C) (point : Label) (proper : point ≠ 8) :
    AuxWorkspace.pushes (program caller point) ≤ 3 := by
  fin_cases point
  all_goals first | exact False.elim (proper rfl) | simp [program,AuxWorkspace.pushes,jump]

theorem program_writes (caller : Statement C) (point : Label) (proper : point ≠ 8) :
    StackIso.WritesOnly (fun slot : Stack => slot = 13 ∨ slot = 14 ∨ slot = 7 ∨ slot = 15) (program caller point) := by
  fin_cases point
  all_goals first | exact False.elim (proper rfl) | simp [program,StackIso.WritesOnly,jump]

theorem internal_bound (caller : Statement C) (background : Stack → List Bool) (context : C)
    (current : State C) (K : Nat) (safe : Safe background context K current) (point : Label) (proper : point ≠ 8) :
    (∀ node ∈ AuxWorkspace.nodes (program caller point) current.var current.stk,
      (∀ slot, (node.2 slot).length ≤ K+3) ∧
      ∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → node.2 slot = background slot) ∧
    ScannerStatement.clock (program caller point) current.var current.stk ≤ 16*(K+4) := by
  have bounded : ∀ slot, (current.stk slot).length ≤ K := by
    intro slot
    exact (Finset.single_le_sum (f:=fun other : Stack => (current.stk other).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ slot)).trans safe.2.2
  have pushes := program_pushes caller point proper
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ K bounded node member slot).trans (by omega)
    · intro slot notR notL notC notT
      have frame := StackIso.nodes_frame _ _ (program_writes caller point proper) current.var current.stk slot
        (by simp only [notR,notL,notC,notT,or_self,not_false_eq_true]) node member
      exact frame.trans (safe.2.1 slot notR notL notC notT)
  · have clock := ScannerClock.clock_bound (program caller point) current.var current.stk K bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions caller point proper)) (by omega))

end PaperProofs.Common.Native.PSTRWordBool.RatOutput
