module

public import Paid.PDROC_BitVM_VM_Control_Cleanup_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

/-- A proposition about actual already-read query bytes, never an input
field or an unbounded control-store value. The prologue/reader derives it. -/
structure QueryReady (query : Nat) (contents : Stack → List Bool) : Prop where
  candidateEmpty : contents 24 = []
  queryWord : contents 26 = encodeNatBits query
  savedEmpty : contents 27 = []
  literalScratch : contents 28 = []

def nextEntry (code : Program) (candidate : PC code) : Label code :=
  ((literalPC code (candidate.val + 1)).map (fun point => entry code (.inl (.literal point)))).getD (cleanupEntry code)

theorem compared_literal (candidate : Nat) (contents : Stack → List Bool)
    (a : contents 24 = []) (b : contents 27 = []) :
    Log.InputCompare.compared (Function.update contents 24 (encodeNatBits candidate)) = contents := by
  funext slot
  by_cases h24 : slot = 24
  · subst slot
    simp [Log.InputCompare.compared, a]
  · by_cases h27 : slot = 27
    · subst slot
      simp [Log.InputCompare.compared, b]
    · simp [Log.InputCompare.compared, Function.update_of_ne h24, Function.update_of_ne h27]

theorem literal_transfer (code : Program) (pointer : Register) (candidate : PC code)
    (store : Store code) (contents : Stack → List Bool) (scratch : contents 28 = []) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents)
      (atEntry code (.inl (.compare candidate)) nextStore (Function.update contents 24 (encodeNatBits candidate.val))),
      selected code nextStore = selected code store ∧ path.posts.length = (contents 24).length + 3 := by
  obtain ⟨after, path, label, data, flags, count⟩ := literal_call code pointer candidate store contents scratch
  rcases after with ⟨actualLabel, nextStore, actualData⟩
  change actualLabel = some (returned code (.inl (.literal candidate))) at label
  change actualData = Function.update contents 24 (encodeNatBits candidate.val) at data
  subst actualLabel; subst actualData
  have edge := literal_resume code pointer candidate nextStore (Function.update contents 24 (encodeNatBits candidate.val))
  let joined := path.trans (ActualPath.single edge)
  refine ⟨nextStore, joined, flags, ?_⟩
  exact (ActualPath.trans_length path (ActualPath.single edge)).trans count

/-- The Nat test in this STATEMENT OF THEOREM describes the observed
exit only. The machine program has NO query argument: its real bytewise
comparison produces BoolEq, and only that flag chooses the actual edge.
No target Fin is supplied or made from the unknown Nat query. -/
theorem candidate_cycle (code : Program) (pointer : Register) (candidate : PC code) (query : Nat)
    (store : Store code) (contents : Stack → List Bool) (ready : QueryReady query contents) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents)
      ⟨some (if candidate.val = query then cleanupEntry code else nextEntry code candidate), nextStore, contents⟩,
      selected code nextStore = (if candidate.val = query then some candidate else selected code store) ∧
      path.posts.length ≤ 4 * natBits candidate.val + 11 := by
  obtain ⟨s1, literalPath, selectedLiteral, literalCount⟩ :=
    literal_transfer code pointer candidate store contents ready.literalScratch
  let written := Function.update contents (24 : Stack) (encodeNatBits candidate.val)
  have address : written 24 = encodeNatBits candidate.val := Function.update_self _ _ _
  have queryWord : written 26 = encodeNatBits query := by simpa [written] using ready.queryWord
  have savedWord : written 27 = [] := by simpa [written] using ready.savedEmpty
  obtain ⟨after, comparison, label, data, selectedComparison, equalFlag, comparisonCount⟩ :=
    comparison_call code pointer candidate query s1 written address queryWord savedWord
  have sameData : after.stk = contents := data.trans (compared_literal candidate.val contents ready.candidateEmpty ready.savedEmpty)
  rcases after with ⟨actualLabel, s2, actualData⟩
  change actualLabel = some (returned code (.inl (.compare candidate))) at label
  change actualData = contents at sameData
  subst actualLabel; subst actualData
  have literalLength : literalPath.posts.length = 3 := by simpa only [ready.candidateEmpty, List.length_nil, Nat.zero_add] using literalCount
  by_cases matched : candidate.val = query
  · have observed : equalityFlag code candidate s2 = true := equalFlag.trans (by simp [matched])
    have edge := compare_true_edge code pointer candidate s2 contents observed
    let joined := (literalPath.trans comparison).trans (ActualPath.single edge)
    refine ⟨setSelected code (some candidate) s2,
      ⟨joined.posts, joined.chain, by simpa only [ite_eq_left matched] using joined.last⟩, ?_, ?_⟩
    · simp only [ite_eq_left matched, selected_set]
    · have count : joined.posts.length = literalPath.posts.length + comparison.posts.length + 1 := by
        simp only [joined, ActualPath.trans, ActualPath.single, List.length_append, List.length_cons, List.length_nil]
      have bound : comparison.posts.length + 1 ≤ 4 * natBits candidate.val + 8 := comparisonCount
      change joined.posts.length ≤ 4 * natBits candidate.val + 11
      omega
  · have observed : equalityFlag code candidate s2 = false := equalFlag.trans (by simp [matched])
    have edge := compare_false_edge code pointer candidate s2 contents observed
    let joined := (literalPath.trans comparison).trans (ActualPath.single edge)
    refine ⟨s2,
      ⟨joined.posts, joined.chain, by simpa only [ite_eq_right matched, nextEntry] using joined.last⟩, ?_, ?_⟩
    · rw [ite_eq_right matched]
      exact selectedComparison.trans selectedLiteral
    · have count : joined.posts.length = literalPath.posts.length + comparison.posts.length + 1 := by
        simp only [joined, ActualPath.trans, ActualPath.single, List.length_append, List.length_cons, List.length_nil]
      have bound : comparison.posts.length + 1 ≤ 4 * natBits candidate.val + 8 := comparisonCount
      change joined.posts.length ≤ 4 * natBits candidate.val + 11
      omega

end PDROC.BitVM.VM.Control.Indirect
