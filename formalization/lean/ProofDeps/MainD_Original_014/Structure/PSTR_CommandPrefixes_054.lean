module

public import Structure.PSTR_Script_002

/-! Same-count prefixes and actual call composition for causal command
sequences, including a final unpaired query. AllowedSequence is only a
proof invariant to derive from the actual history; it is not a new caller
qualification or an assertion that arbitrary histories are realizable. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCommandPrefixes

open AlgorithmClaims CompactControllerClaims

def AllowedSequence {q : Nat} (full : List (Finset (Fin q))) : Configuration q → List Command → Prop
  | _, [] => True
  | configuration, command :: later => Allowed full configuration command ∧
      AllowedSequence full (nextConfiguration q full configuration command) later

theorem run_take {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (commands : List Command) (counts : List Nat)
    (heap : BitVec bits → BitVec bits)
    (hrun : CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap)
    (count : Nat) :
    CommandsRunClaims constant q full capWords heapWords program configuration
      (commands.take count) (counts.take count) heap := by
  induction count generalizing configuration commands counts heap with
  | zero => trivial
  | succ count ih =>
    cases commands with
    | nil =>
      cases counts with
      | nil => trivial
      | cons steps later => exact False.elim hrun
    | cons command commands =>
      cases counts with
      | nil => exact False.elim hrun
      | cons steps counts => exact ⟨hrun.1, hrun.2.1, ih _ _ _ _ hrun.2.2⟩

theorem run_prefix {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (commands current : List Command) (counts : List Nat)
    (heap : BitVec bits → BitVec bits) (hprefix : current.IsPrefix commands)
    (hrun : CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap) :
    CommandsRunClaims constant q full capWords heapWords program configuration current
      (counts.take current.length) heap := by
  obtain ⟨later, rfl⟩ := hprefix
  have h := run_take full program configuration (current ++ later) counts heap hrun current.length
  simpa only [List.take_append_length] using h

theorem allowed_of_run {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (commands : List Command) (counts : List Nat)
    (heap : BitVec bits → BitVec bits)
    (hrun : CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap) :
    AllowedSequence full configuration commands := by
  induction commands generalizing configuration counts heap with
  | nil => trivial
  | cons command commands ih =>
    cases counts with
    | nil => exact False.elim hrun
    | cons steps counts => exact ⟨hrun.1, ih _ _ _ hrun.2.2⟩

theorem stageScript_allowed {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (commands : List Command)
    (script : StageScript q full configuration commands) : AllowedSequence full configuration commands := by
  induction script with
  | «prefix» => trivial
  | stage configuration declaration later hd ha continuation ih =>
    exact ⟨PSTRScript.script_query_allowed configuration declaration hd ha, ha, ih⟩

theorem call_mono_constant {bits q small large capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (command : Command) (steps : Nat)
    (heap : BitVec bits → BitVec bits) (hconstant : small ≤ large)
    (hcall : CallClaims small q full capWords heapWords program configuration command steps heap) :
    CallClaims large q full capWords heapWords program configuration command steps heap :=
  ⟨hcall.1, hcall.2.1.trans (Nat.mul_le_mul_right _ hconstant), hcall.2.2⟩

theorem run_mono_constant {bits q small large capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (commands : List Command) (counts : List Nat)
    (heap : BitVec bits → BitVec bits) (hconstant : small ≤ large)
    (hrun : CommandsRunClaims small q full capWords heapWords program configuration commands counts heap) :
    CommandsRunClaims large q full capWords heapWords program configuration commands counts heap := by
  induction commands generalizing configuration counts heap with
  | nil =>
    cases counts with
    | nil => trivial
    | cons steps counts => exact False.elim hrun
  | cons command commands ih =>
    cases counts with
    | nil => exact False.elim hrun
    | cons steps counts =>
      exact ⟨hrun.1, call_mono_constant full program configuration command steps heap hconstant hrun.2.1,
        ih _ _ _ hrun.2.2⟩

theorem commands_of_calls {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (calls : ∀ (configuration : Configuration q) (heap : BitVec bits → BitVec bits),
      HeapRepresents q full capWords configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims constant q full capWords heapWords program configuration command steps heap)
    (configuration : Configuration q) (commands : List Command)
    (allowed : AllowedSequence full configuration commands)
    (heap : BitVec bits → BitVec bits) (rep : HeapRepresents q full capWords configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap ∧
      commandsCost q full program commands counts heap ≤
        constant * commands.length * liveWork q (treeSize q full) := by
  induction commands generalizing configuration heap with
  | nil => exact ⟨[], rfl, trivial, by simp [commandsCost]⟩
  | cons command commands ih =>
    obtain ⟨steps, hcall⟩ := calls configuration heap rep command allowed.1
    let nextHeap := (packingRun (callInput q full command) program steps (packingInitial heap)).heap
    obtain ⟨counts, hlen, hrun, hcost⟩ := ih (nextConfiguration q full configuration command)
      allowed.2 nextHeap hcall.2.2.1
    refine ⟨steps :: counts, by simpa only [List.length_cons] using congrArg Nat.succ hlen,
      ⟨allowed.1, hcall, hrun⟩, ?_⟩
    change callCost q full program command steps heap + commandsCost q full program commands counts nextHeap ≤ _
    calc
      _ ≤ constant * liveWork q (treeSize q full) +
          constant * commands.length * liveWork q (treeSize q full) := Nat.add_le_add hcall.2.1 hcost
      _ = constant * (command :: commands).length * liveWork q (treeSize q full) := by
        simp only [List.length_cons]
        ring

theorem calls_for_all_prefixes {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (calls : ∀ (configuration : Configuration q) (heap : BitVec bits → BitVec bits),
      HeapRepresents q full capWords configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims constant q full capWords heapWords program configuration command steps heap)
    (configuration : Configuration q) (commands : List Command)
    (allowed : AllowedSequence full configuration commands)
    (heap : BitVec bits → BitVec bits) (rep : HeapRepresents q full capWords configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap ∧
      commandsCost q full program commands counts heap ≤
        constant * commands.length * liveWork q (treeSize q full) ∧
      ∀ current : List Command, current.IsPrefix commands →
        CommandsRunClaims constant q full capWords heapWords program configuration current
          (counts.take current.length) heap := by
  obtain ⟨counts, hlen, hrun, hcost⟩ := commands_of_calls full program calls configuration commands allowed heap rep
  exact ⟨counts, hlen, hrun, hcost, fun current hp => run_prefix full program configuration commands current counts heap hp hrun⟩

theorem bounded_commands {bits q localConstant chargedConstant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (calls : ∀ (configuration : Configuration q) (heap : BitVec bits → BitVec bits),
      HeapRepresents q full capWords configuration heap →
      ∀ command : Command, Allowed full configuration command →
      ∃ steps : Nat, CallClaims localConstant q full capWords heapWords program configuration command steps heap)
    (configuration : Configuration q) (commands : List Command)
    (allowed : AllowedSequence full configuration commands)
    (hlength : commands.length ≤ 2 * full.length + 1) (hconstant : 2 * localConstant ≤ chargedConstant)
    (heap : BitVec bits → BitVec bits) (rep : HeapRepresents q full capWords configuration heap) :
    ∃ counts : List Nat,
      counts.length = commands.length ∧
      CommandsRunClaims chargedConstant q full capWords heapWords program configuration commands counts heap ∧
      commandsCost q full program commands counts heap ≤
        chargedConstant * (full.length + 1) * liveWork q (treeSize q full) ∧
      ∀ current : List Command, current.IsPrefix commands →
        CommandsRunClaims chargedConstant q full capWords heapWords program configuration current
          (counts.take current.length) heap := by
  obtain ⟨counts, hlen, hrun, hcost⟩ := commands_of_calls full program calls configuration commands allowed heap rep
  have hc : localConstant ≤ chargedConstant := (show localConstant ≤ 2 * localConstant by omega).trans hconstant
  have large := run_mono_constant full program configuration commands counts heap hc hrun
  refine ⟨counts, hlen, large, hcost.trans ?_,
    fun current hp => run_prefix full program configuration commands current counts heap hp large⟩
  apply Nat.mul_le_mul_right
  calc
    localConstant * commands.length ≤ localConstant * (2 * full.length + 1) := Nat.mul_le_mul_left _ hlength
    _ ≤ (2 * localConstant) * (full.length + 1) := by
      have h := Nat.mul_le_mul_left localConstant (show 2 * full.length + 1 ≤ 2 * (full.length + 1) by omega)
      calc
        _ ≤ localConstant * (2 * (full.length + 1)) := h
        _ = _ := by ring
    _ ≤ chargedConstant * (full.length + 1) := Nat.mul_le_mul_right _ hconstant

end PaperProofs.Structure.LaminarTree.PSTRCommandPrefixes
