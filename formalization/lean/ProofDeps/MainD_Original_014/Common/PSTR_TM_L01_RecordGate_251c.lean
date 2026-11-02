module
public import Common.PSTR_TM_L01_RecordGate_251b

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
open PaperProofs.Common.Native.RationalControllerComputation

def positions (trace : List (MachineState 4)) : List Int :=
  (trace.map (displacement gateMachine)).scanl (·+·) 0

theorem positions_take (trace : List (MachineState 4)) (clock : Nat) :
    positions (trace.take clock) = (positions trace).take (clock+1) := by
  unfold positions
  rw [List.map_take]
  exact (List.take_scanl (0 : Int) (trace.map (displacement gateMachine)) clock).symm

private theorem prefix_space (trace : List (MachineState 4)) (inputLength cap clock : Nat)
    (bounded : ∀ p ∈ positions trace, 0 ≤ p ∧ p ≤ (cap : Int)) :
    visitedSpace gateMachine inputLength (trace.take clock) ≤ max inputLength cap+1 := by
  let ps := positions (trace.take clock)
  have bounds (p : Int) (member : p ∈ ps) : 0 ≤ p ∧ p ≤ (cap : Int) := by
    change p ∈ positions (trace.take clock) at member
    rw [positions_take] at member
    exact bounded p (List.mem_of_mem_take member)
  have initial : (inputLength : Int) ≤ (max inputLength cap : Nat) := by
    exact_mod_cast Nat.le_max_left inputLength cap
  have ceiling : (cap : Int) ≤ (max inputLength cap : Nat) := by
    exact_mod_cast Nat.le_max_right inputLength cap
  have high : ps.foldl max (inputLength : Int) ≤ (max inputLength cap : Nat) :=
    PSTRTMTrace002.foldl_max_le ps _ _ initial (fun p member => (bounds p member).2.trans ceiling)
  have low : 0 ≤ ps.foldl min 0 :=
    PSTRTMTrace002.le_foldl_min ps 0 0 (by omega) (fun p member => (bounds p member).1)
  change (ps.foldl max (inputLength : Int)-ps.foldl min 0).toNat+1 ≤ _
  omega

theorem zero_positions (left suffix : List Bool) :
    positions (zeroTrace left suffix) = [0,1,2,3,3] := by
  simp [positions,zero_moves]

theorem nonzero_positions (left tail : List Bool) :
    positions (nonzeroTrace left tail) = [0,1,0,0] := by
  simp [positions,nonzero_moves]

theorem zero_prefix_space (left suffix : List Bool) (inputLength clock : Nat) :
    visitedSpace gateMachine inputLength ((zeroTrace left suffix).take clock) ≤ max inputLength 3+1 := by
  apply prefix_space _ _ 3 _
  intro p member
  rw [zero_positions] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem nonzero_prefix_space (left tail : List Bool) (inputLength clock : Nat) :
    visitedSpace gateMachine inputLength ((nonzeroTrace left tail).take clock) ≤ max inputLength 1+1 := by
  apply prefix_space _ _ 1 _
  intro p member
  rw [nonzero_positions] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> norm_num

/-- Internal real records entry. The actual parent producer proves its
count domain, which is not a new original planner qualification or input.
All movement is measured from THIS entry; the caller must genuinely link
the HALT port/return and compose its preceding displacement. -/
theorem actual_records_entry (left : List Bool) (data : List Datum) (suffix : List Bool)
    (domain : data = [] ∨ 4 ≤ data.length) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom gateMachine (state 0 left (encode data++suffix)) trace (final left data suffix) ∧
      final left data suffix ∈ StateTransition.eval (Turing.TM0.step gateMachine)
        (state 0 left (encode data++suffix)) ∧
      trace.length = (if data = [] then 4 else 3) ∧
      trace.map (displacement gateMachine) = (if data = [] then [1,1,1,0] else [1,-1,0]) ∧
      (∀ p ∈ positions trace, 0 ≤ p ∧ p ≤ 3) ∧
      ∀ clock, visitedSpace gateMachine (encode data++suffix).length (trace.take clock) ≤
        (encode data++suffix).length+1 := by
  obtain ⟨trace,actual,length,moves⟩ := records_gate_contract left data suffix domain
  have reach := PSTRTMTrace002.chain_reaches (Turing.TM0.step gateMachine) trace
    (state 0 left (encode data++suffix)) (final left data suffix) actual.1 actual.2.1 actual.2.2.1
  have bounded : ∀ p ∈ positions trace, 0 ≤ p ∧ p ≤ (3 : Int) := by
    intro p member
    unfold positions at member
    rw [moves] at member
    by_cases empty : data = []
    · simp only [empty,ite_true] at member
      have scan : ([1,1,1,0] : List Int).scanl (·+·) 0 = [0,1,2,3,3] := by simp
      rw [scan] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> norm_num
    · simp only [empty,ite_false] at member
      have scan : ([1,-1,0] : List Int).scanl (·+·) 0 = [0,1,0,0] := by simp
      rw [scan] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨trace,actual,StateTransition.mem_eval.mpr ⟨reach,actual.2.2.2⟩,length,moves,bounded,?_⟩
  intro clock
  have space := prefix_space trace (encode data++suffix).length 3 clock bounded
  have size := encoded_right_length data suffix
  rw [Nat.max_eq_left (by omega : 3 ≤ (encode data++suffix).length)] at space
  exact space

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTML01RecordGate251
