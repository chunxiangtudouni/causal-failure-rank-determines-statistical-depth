module

public import Paid.PDROC_BitVM_VM_Control_Candidate_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

/-- Fixed source-code constant. No maximum runtime word width is an
input to the selector, its alphabet, labels or finite store. -/
def candidateBudget (code : Program) : Nat :=
  Finset.univ.sup (fun candidate : PC code => 4 * natBits candidate.val + 11)

theorem candidateCost_le (code : Program) (candidate : PC code) :
    4 * natBits candidate.val + 11 ≤ candidateBudget code :=
  Finset.le_sup (f := fun point : PC code => 4 * natBits point.val + 11) (Finset.mem_univ candidate)

/-- Logical meaning of the finite flag produced by ACTUAL comparisons.
There is no conversion lower query Nat to Fin, even in this relation. -/
def SearchMeaning (code : Program) (query lower : Nat) : Option (PC code) → Prop
  | some candidate => candidate.val = query ∧ lower ≤ candidate.val
  | none => ∀ candidate : PC code, lower ≤ candidate.val → candidate.val ≠ query

theorem meaning_step (code : Program) (query : Nat) (candidate : PC code) (choice : Option (PC code))
    (different : candidate.val ≠ query)
    (meaning : SearchMeaning code query (candidate.val + 1) choice) :
    SearchMeaning code query candidate.val choice := by
  cases choice with
  | some found => exact ⟨meaning.1, by have lower := meaning.2; omega⟩
  | none =>
    intro point lower
    by_cases same : point.val = candidate.val
    · simpa only [same] using different
    · exact meaning point (by omega)

theorem matched_candidate (code : Program) (pointer : Register) (candidate : PC code) (query : Nat)
    (store : Store code) (contents : Stack → List Bool) (ready : QueryReady query contents)
    (matched : candidate.val = query) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents)
      ⟨some (cleanupEntry code), nextStore, contents⟩,
      selected code nextStore = some candidate ∧ path.posts.length ≤ candidateBudget code := by
  obtain ⟨nextStore, path, flags, count⟩ := candidate_cycle code pointer candidate query store contents ready
  refine ⟨nextStore, ⟨path.posts, path.chain, ?_⟩, ?_, count.trans (candidateCost_le code candidate)⟩
  · simpa only [ite_eq_left matched] using path.last
  · simpa only [ite_eq_left matched] using flags

theorem mismatched_candidate (code : Program) (pointer : Register) (candidate : PC code) (query : Nat)
    (store : Store code) (contents : Stack → List Bool) (ready : QueryReady query contents)
    (different : candidate.val ≠ query) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents)
      ⟨some (nextEntry code candidate), nextStore, contents⟩,
      selected code nextStore = selected code store ∧ path.posts.length ≤ candidateBudget code := by
  obtain ⟨nextStore, path, flags, count⟩ := candidate_cycle code pointer candidate query store contents ready
  refine ⟨nextStore, ⟨path.posts, path.chain, ?_⟩, ?_, count.trans (candidateCost_le code candidate)⟩
  · simpa only [ite_eq_right different] using path.last
  · simpa only [ite_eq_right different] using flags

/-- The recursive variable is proof-only distance to the end of FIXED
source code. Runtime control is the literal FinPC labels and real BoolEq
edges of program004; the unknown Nat query remains only tape DATA. -/
theorem search_tail (code : Program) (pointer : Register) (query remaining : Nat) :
    ∀ (candidate : PC code), code.size - candidate.val = remaining + 1 →
    ∀ (store : Store code) (contents : Stack → List Bool), QueryReady query contents → selected code store = none →
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal candidate)) store contents)
      ⟨some (cleanupEntry code), nextStore, contents⟩,
      SearchMeaning code query candidate.val (selected code nextStore) ∧
      path.posts.length ≤ (remaining + 1) * candidateBudget code := by
  induction remaining with
  | zero =>
    intro candidate distance store contents ready unselected
    by_cases matched : candidate.val = query
    · obtain ⟨nextStore, path, flags, count⟩ := matched_candidate code pointer candidate query store contents ready matched
      refine ⟨nextStore, path, ?_, ?_⟩
      · rw [flags]
        exact ⟨matched, Nat.le_refl _⟩
      · simpa using count
    · obtain ⟨nextStore, path, flags, count⟩ := mismatched_candidate code pointer candidate query store contents ready matched
      have outside : code.size ≤ candidate.val + 1 := by have inside := candidate.isLt; omega
      have finish : nextEntry code candidate = cleanupEntry code := by
        rw [nextEntry, literalPC_outside code (candidate.val + 1) outside]
        rfl
      refine ⟨nextStore, ⟨path.posts, path.chain, by simpa only [finish] using path.last⟩, ?_, ?_⟩
      · rw [flags, unselected]
        intro point lower
        have last : point.val = candidate.val := by have inside := point.isLt; omega
        simpa only [last] using matched
      · simpa using count
  | succ remaining ih =>
    intro candidate distance store contents ready unselected
    by_cases matched : candidate.val = query
    · obtain ⟨nextStore, path, flags, count⟩ := matched_candidate code pointer candidate query store contents ready matched
      refine ⟨nextStore, path, ?_, ?_⟩
      · rw [flags]
        exact ⟨matched, Nat.le_refl _⟩
      · calc
          path.posts.length ≤ candidateBudget code := count
          _ ≤ (remaining + 1 + 1) * candidateBudget code := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (candidateBudget code) (by omega : 1 ≤ remaining + 1 + 1)
    · obtain ⟨s1, first, carry, firstBound⟩ := mismatched_candidate code pointer candidate query store contents ready matched
      have nextBound : candidate.val + 1 < code.size := by have inside := candidate.isLt; omega
      let next : PC code := ⟨candidate.val + 1, nextBound⟩
      have nextDistance : code.size - next.val = remaining + 1 := by dsimp [next]; omega
      obtain ⟨s2, second, meaning, secondBound⟩ :=
        ih next nextDistance s1 contents ready (carry.trans unselected)
      have nextLabel : nextEntry code candidate = entry code (.inl (.literal next)) := by
        rw [nextEntry, literalPC_of_lt code (candidate.val + 1) nextBound]
        rfl
      let firstPath : Path code pointer (atEntry code (.inl (.literal candidate)) store contents)
          (atEntry code (.inl (.literal next)) s1 contents) :=
        ⟨first.posts, first.chain, by simpa only [nextLabel, atEntry] using first.last⟩
      let joined := firstPath.trans second
      refine ⟨s2, joined, meaning_step code query candidate (selected code s2) matched meaning, ?_⟩
      have length : joined.posts.length = first.posts.length + second.posts.length := ActualPath.trans_length firstPath second
      rw [length]
      nlinarith

/-- All literal PC candidates, in order, on ONE genuine source path.
The output is a bounded finite flag justified by byte comparison, or a
proof that no source-code PC matched. It is never a supplied target. -/
theorem search_all (code : Program) (pointer : Register) (query : Nat)
    (store : Store code) (contents : Stack → List Bool)
    (positive : 0 < code.size) (ready : QueryReady query contents) (unselected : selected code store = none) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (.inl (.literal ⟨0, positive⟩)) store contents)
      ⟨some (cleanupEntry code), nextStore, contents⟩,
      SearchMeaning code query 0 (selected code nextStore) ∧
      path.posts.length ≤ code.size * candidateBudget code := by
  have distance : code.size - (⟨0, positive⟩ : PC code).val = (code.size - 1) + 1 := by dsimp; omega
  obtain ⟨nextStore, path, meaning, count⟩ := search_tail code pointer query (code.size - 1)
    ⟨0, positive⟩ distance store contents ready unselected
  refine ⟨nextStore, path, meaning, ?_⟩
  have width : code.size - 1 + 1 = code.size := by omega
  simpa only [width] using count

end PDROC.BitVM.VM.Control.Indirect
