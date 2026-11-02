module

public import PaperProofs.Retained.RootRetainedQueries_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootRetainedQueries

open PaperProofs.Common PaperProofs.Retained

theorem assignmentValid_matchable (I : Instance) (errors : Finset I.Stage)
    (candidate : List (Option I.Tool)) (h : AssignmentValid I errors candidate) :
    Matchable I errors := by
  classical
  have chooseTool : ∀ i : {i : I.Stage // i ∈ errors},
      ∃ tool, candidate[i.val.val]?.join = some tool ∧ tool ∈ I.eligible i.val := by
    intro i
    simpa only [i.property, ↓reduceIte] using h.2.1 i.val
  choose f hf using chooseTool
  refine ⟨f, ?_, ?_⟩
  · intro i j heq
    apply Subtype.ext
    exact h.2.2 i.val j.val (f i) (hf i).1 (heq ▸ (hf j).1)
  · intro i
    exact (hf i).2

theorem matching_assignment_exists (I : Instance) (errors : Finset I.Stage)
    (hm : Matchable I errors) :
    ∃ candidate ∈ assignmentCandidates I, AssignmentValid I errors candidate := by
  classical
  obtain ⟨f, hinj, hcompatible⟩ := hm
  let entry : I.Stage → Option I.Tool := fun i =>
    if h : i ∈ errors then some (f ⟨i, h⟩) else none
  let candidate := List.ofFn entry
  have entryAt (i : I.Stage) : candidate[i.val]?.join = entry i := by
    simp [candidate, i.isLt]
  have hvalid : AssignmentValid I errors candidate := by
    refine ⟨by simp [candidate, Instance.stageCount], ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ errors
      · simp only [hi, ↓reduceIte]
        exact ⟨f ⟨i, hi⟩, by simp [entryAt, entry, hi], hcompatible ⟨i, hi⟩⟩
      · simp [hi, entryAt, entry]
    · intro i j tool hi hj
      rw [entryAt] at hi hj
      have hei : i ∈ errors := by
        by_contra hnot
        simp [entry, hnot] at hi
      have hej : j ∈ errors := by
        by_contra hnot
        simp [entry, hnot] at hj
      have hfi : f ⟨i, hei⟩ = tool := by simpa [entry, hei] using hi
      have hfj : f ⟨j, hej⟩ = tool := by simpa [entry, hej] using hj
      exact congrArg Subtype.val (hinj (hfi.trans hfj.symm))
  refine ⟨candidate, ?_, hvalid⟩
  apply List.mem_sections.mpr
  apply List.forall₂_of_length_eq_of_get
  · simp [candidate]
  · intro n hn hm
    have hn' : n < I.stageCount := by simpa [candidate, Instance.stageCount] using hn
    change (List.ofFn entry)[n] ∈
      (List.ofFn (fun _stage : I.Stage => none :: (List.finRange I.toolCount).map some))[n]
    simp only [List.getElem_ofFn]
    dsimp only [entry]
    split
    · simp
    · simp

theorem terminalAssignmentCorrect (I : Instance) : TerminalAssignmentCorrect I := by
  classical
  constructor
  · intro errors candidate h
    exact of_decide_eq_true (List.find?_some
      (p := fun candidate => decide (AssignmentValid I errors candidate)) h)
  · intro errors
    constructor
    · intro hm
      obtain ⟨candidate, hmem, hv⟩ := matching_assignment_exists I errors hm
      exact List.find?_isSome.mpr ⟨candidate, hmem, decide_eq_true hv⟩
    · intro hs
      obtain ⟨candidate, _, hv⟩ := List.find?_isSome.mp hs
      exact assignmentValid_matchable I errors candidate (of_decide_eq_true hv)

end RootRetainedQueries
