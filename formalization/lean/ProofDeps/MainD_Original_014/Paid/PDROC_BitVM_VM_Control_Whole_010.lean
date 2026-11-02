module

public import Paid.PDROC_BitVM_VM_Control_Search_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Common.IO

def queried (contents : Stack → List Bool) (query : Nat) : Stack → List Bool :=
  Function.update (cleared contents) 26 (encodeNatBits query)

theorem queried_ready (contents : Stack → List Bool) (query : Nat) : QueryReady query (queried contents query) := by
  constructor <;> simp [queried, cleared]

theorem queried_cost (contents : Stack → List Bool) (query : Nat) :
    scratchCost (queried contents query) = (encodeNatBits query).length := by
  simp [scratchCost, queried, cleared]

theorem cleared_cost (contents : Stack → List Bool) : scratchCost (cleared contents) = 0 := by
  simp [scratchCost, cleared]

theorem cleared_register (contents : Stack → List Bool) (reg : Register) :
    cleared contents (registerSlot reg) = contents (registerSlot reg) := by
  apply cleared_other
  intro slot
  have upper := (registerSlot_bounds reg).2
  fin_cases slot <;>
    (intro same; have values := congrArg Fin.val same; simp [clearSlot] at values; omega)

theorem cleared_query (contents : Stack → List Bool) (query : Nat) :
    cleared (queried contents query) = cleared contents := by
  funext slot
  by_cases a : slot = 24
  · subst slot; simp [queried, cleared]
  · by_cases b : slot = 26
    · subst slot; simp [queried, cleared]
    · by_cases c : slot = 27
      · subst slot; simp [queried, cleared]
      · by_cases d : slot = 28
        · subst slot; simp [queried, cleared]
        · simp [queried, cleared, Function.update_of_ne a, Function.update_of_ne b,
            Function.update_of_ne c, Function.update_of_ne d]

theorem cleared_idempotent (contents : Stack → List Bool) : cleared (cleared contents) = cleared contents := by
  funext slot
  by_cases a : slot = 24
  · subst slot; simp [cleared]
  · by_cases b : slot = 26
    · subst slot; simp [cleared]
    · by_cases c : slot = 27
      · subst slot; simp [cleared]
      · by_cases d : slot = 28
        · subst slot; simp [cleared]
        · simp [cleared, Function.update_of_ne a, Function.update_of_ne b,
            Function.update_of_ne c, Function.update_of_ne d]

/-- Enter the finite candidate scan by the ACTUAL typed flag. Code0
has no PC candidate and really goes to cleanup, rather than inventing a
Fin0 target. Nonempty code starts its literal0 macro with a real goto. -/
theorem search_from_pointer (code : Program) (pointer : Register) (query : Nat)
    (store : Store code) (contents : Stack → List Bool) (ready : QueryReady query contents)
    (unselected : selected code store = none) (typed : typedFlag code store = true) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      ⟨some (returned code (.inl .pointer)), store, contents⟩
      ⟨some (cleanupEntry code), nextStore, contents⟩,
      SearchMeaning code query 0 (selected code nextStore) ∧
      path.posts.length ≤ code.size * candidateBudget code + 1 := by
  by_cases positive : 0 < code.size
  · have edge : TM2.step (program code pointer)
        (⟨some (returned code (.inl .pointer)), store, contents⟩ : State code) =
        some (atEntry code (.inl (.literal ⟨0, positive⟩)) store contents) := by
      simpa only [literalPC_of_lt code 0 positive, Option.map_some, Option.getD_some, atEntry] using
        typed_pointer_resume code pointer store contents typed
    obtain ⟨nextStore, search, meaning, count⟩ := search_all code pointer query store contents positive ready unselected
    let joined := (ActualPath.single edge).trans search
    refine ⟨nextStore, joined, meaning, ?_⟩
    have length : joined.posts.length = 1 + search.posts.length := ActualPath.trans_length (ActualPath.single edge) search
    rw [length]
    omega
  · have empty : code.size = 0 := by omega
    have absent : literalPC code 0 = none := literalPC_outside code 0 (by omega)
    have edge : TM2.step (program code pointer)
        (⟨some (returned code (.inl .pointer)), store, contents⟩ : State code) =
        some ⟨some (cleanupEntry code), store, contents⟩ := by
      simpa only [absent, Option.map_none, Option.getD_none] using typed_pointer_resume code pointer store contents typed
    refine ⟨store, ActualPath.single edge, ?_, ?_⟩
    · rw [unselected]
      intro point _
      have inside := point.isLt
      omega
    · change 1 ≤ code.size * candidateBudget code + 1
      omega

/-- Complete UNKNOWN-Nat indirect selection from the ORIGINAL register.
The same trace resets the finite flag, physically clears caller scratch,
reads/restores the register, matches actual bytes against every fixed PC,
and really clears query26 etc before local HALT/parent return. -/
theorem natural_path (code : Program) (pointer : Register) (query : Nat)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query)) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (selectedIndex code) store contents) ⟨none, nextStore, cleared contents⟩,
      SearchMeaning code query 0 (selected code nextStore) ∧
      path.posts.length ≤ scratchCost contents + 3 * (encodeNatBits query).length + code.size * candidateBudget code + 33 := by
  obtain ⟨s1, first, unselected, firstCount⟩ := prologue_path code pointer store contents
  have word : cleared contents (registerSlot pointer) = encodeCellBits (.natural query) :=
    (cleared_register contents pointer).trans register
  have scratch : cleared contents 24 = [] := cleared_empty contents 0
  obtain ⟨after, second, label, data, carry, typed, secondCount⟩ :=
    natural_pointer_call code pointer query s1 (cleared contents) word scratch
  have emptyQuery : cleared contents 26 = [] := cleared_empty contents 1
  have same : after.stk = queried contents query := by simpa only [emptyQuery, List.append_nil, queried] using data
  rcases after with ⟨actualLabel, s2, actualData⟩
  change actualLabel = some (returned code (.inl .pointer)) at label
  change actualData = queried contents query at same
  subst actualLabel; subst actualData
  obtain ⟨s3, third, meaning, thirdCount⟩ := search_from_pointer code pointer query s2 (queried contents query)
    (queried_ready contents query) (carry.trans unselected) typed
  obtain ⟨s4, fourth, finalCarry, fourthCount⟩ := clears_path code pointer true s3 (queried contents query)
  let cleanup : Path code pointer ⟨some (cleanupEntry code), s3, queried contents query⟩
      ⟨none, s4, cleared contents⟩ :=
    ⟨fourth.posts, fourth.chain, by simpa [cleared_query, atEntry, clearMacro, cleanupEntry] using fourth.last⟩
  let joined := ((first.trans second).trans third).trans cleanup
  refine ⟨s4, joined, ?_, ?_⟩
  · rw [finalCarry]
    exact meaning
  · have lastCount : cleanup.posts.length = (encodeNatBits query).length + 12 := by
      simpa only [queried_cost] using fourthCount
    have sum : joined.posts.length = first.posts.length + second.posts.length + third.posts.length + cleanup.posts.length := by
      simp only [joined, ActualPath.trans, List.length_append]
    rw [sum]
    omega

theorem rational_path (code : Program) (pointer : Register) (query : Rat)
    (store : Store code) (contents : Stack → List Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational query)) :
    ∃ nextStore : Store code, ∃ path : Path code pointer
      (atEntry code (selectedIndex code) store contents) ⟨none, nextStore, cleared contents⟩,
      selected code nextStore = none ∧ path.posts.length = scratchCost contents + 29 := by
  obtain ⟨s1, first, unselected, firstCount⟩ := prologue_path code pointer store contents
  have word : cleared contents (registerSlot pointer) = encodeCellBits (.rational query) :=
    (cleared_register contents pointer).trans register
  obtain ⟨after, second, label, data, carry, invalid, secondCount⟩ :=
    rational_pointer_call code pointer query s1 (cleared contents) word
  rcases after with ⟨actualLabel, s2, actualData⟩
  change actualLabel = some (returned code (.inl .pointer)) at label
  change actualData = cleared contents at data
  subst actualLabel; subst actualData
  have edge := invalid_pointer_resume code pointer s2 (cleared contents) invalid
  obtain ⟨s3, fourth, finalCarry, fourthCount⟩ := clears_path code pointer true s2 (cleared contents)
  let cleanup : Path code pointer ⟨some (cleanupEntry code), s2, cleared contents⟩
      ⟨none, s3, cleared contents⟩ :=
    ⟨fourth.posts, fourth.chain, by simpa [cleared_idempotent, atEntry, clearMacro, cleanupEntry] using fourth.last⟩
  let joined := (((first.trans second).trans (ActualPath.single edge))).trans cleanup
  refine ⟨s3, joined, finalCarry.trans (carry.trans unselected), ?_⟩
  have lastCount : cleanup.posts.length = 12 := by simpa only [cleared_cost, Nat.zero_add] using fourthCount
  simp only [joined, ActualPath.trans, ActualPath.single, List.length_append, List.length_cons, List.length_nil]
  omega

end PDROC.BitVM.VM.Control.Indirect
