module

public import Structure.PSTR_LiveControllerDirect_135
public import Structure.PSTR_LiveControllerJoin_138

/-! Original ALL-q, ALL-command live calls for ONE fixed1514-op program.
Every declaration continuation is constructed from its actual update run. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17A19RuntimeEntry020

private theorem destination_correct (q start correct failed done index : Nat) (hq : q ≠ 0) :
    PSTRLiveDispatch.destination q .correct start correct failed done index = correct := by
  simp only [PSTRLiveDispatch.destination, hq, ite_false]

private theorem destination_error_none (q start correct failed done index : Nat) (hq : q ≠ 0)
    (hi : index = 0) :
    PSTRLiveDispatch.destination q .error start correct failed done index = failed := by
  simp only [PSTRLiveDispatch.destination, hq, ite_false, hi, ite_true]

private theorem destination_error_some (q start correct failed done index : Nat) (hq : q ≠ 0)
    (hi : index ≠ 0) :
    PSTRLiveDispatch.destination q .error start correct failed done index = start + 18 := by
  simp only [PSTRLiveDispatch.destination, hq, ite_false, hi]

theorem update_of_prefix {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (hq : 0 < q) (declaration : command = .correct ∨ command = .error)
    (heap : BitVec (wordBits full) → BitVec (wordBits full)) (steps : Nat)
    (pref : PrefixPost full configuration command heap steps) :
    ∃ count ≤ 102, PSTRLiveControllerUpdate.UpdatePost full configuration (capacity full) command
      PSTRLiveControllerCode.program count 1514 (allocatedWords full)
      (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)) := by
  let program := PSTRLiveControllerCode.program
  have length : program.length ≤ 8192 := by rw [PSTRLiveControllerCode.program_length]; decide
  have hqne : q ≠ 0 := Nat.ne_of_gt hq
  rcases declaration with rfl | rfl
  · let after := packingRun (callInput q full .correct) program steps (packingInitial heap)
    have rep : HeapRepresents q full (capacity full) configuration after.heap := by
      simpa only [hqne, ite_false] using pref.represented
    have pc : after.pc = BitVec.ofNat (wordBits full) (5 * 1494) := by
      exact pref.pc.trans (congrArg (fun position : Nat => BitVec.ofNat (wordBits full) (5 * position))
        (destination_correct q 1371 1494 1505 1514 (after.register .index).toNat hqne))
    have post := PSTRLiveControllerUpdate.actual_correct full configuration program 1494 1514 after hq hl allowed rep
      PSTRLiveControllerCode.correct_block PSTRLiveControllerCode.correct_return_block length PSTRLiveControllerCode.literal pc pref.active
    exact ⟨8, by decide, post⟩
  · let after := packingRun (callInput q full .error) program steps (packingInitial heap)
    have rep : HeapRepresents q full (capacity full) configuration after.heap := by
      simpa only [hqne, ite_false] using pref.represented
    let cursor : configuration.stage < full.length + 1 := by have hs := allowed.2; omega
    have reply : ReplyCorrect q (callback q full ⟨configuration.stage, cursor⟩ configuration.used)
        (replyState q (capacity full) after) := pref.reply cursor
    cases choose : (callback q full ⟨configuration.stage, cursor⟩ configuration.used).tool with
    | none =>
      have index : (after.register .index).toNat = 0 := by
        simpa only [replyState, choose] using reply.2.2.2
      have pc : after.pc = BitVec.ofNat (wordBits full) (5 * 1505) := by
        exact pref.pc.trans (congrArg (fun position : Nat => BitVec.ofNat (wordBits full) (5 * position))
          (destination_error_none q 1371 1494 1505 1514 (after.register .index).toNat hqne index))
      have post := PSTRLiveControllerUpdate.actual_fail full configuration program 1505 1514 after hq hl allowed choose rep
        PSTRLiveControllerCode.fail_block PSTRLiveControllerCode.fail_return_block length PSTRLiveControllerCode.literal pc pref.active
      exact ⟨6, by decide, post⟩
    | some tool =>
      have index : (after.register .index).toNat = tool.val + 1 := by
        simpa only [replyState, choose] using reply.2.2.2
      have nonzero : (after.register .index).toNat ≠ 0 := by omega
      have pc : after.pc = BitVec.ofNat (wordBits full) (5 * 1389) := by
        exact pref.pc.trans (congrArg (fun position : Nat => BitVec.ofNat (wordBits full) (5 * position))
          (destination_error_some q 1371 1494 1505 1514 (after.register .index).toNat hqne nonzero))
      have post := PSTRLiveControllerUpdate.actual_selected full configuration program 1389 1514 after tool hq hl allowed choose rep reply
        (pref.width hq) PSTRLiveControllerCode.selected_block PSTRLiveControllerCode.selected_return_block
        length PSTRLiveControllerCode.literal pc pref.active
      exact ⟨102, Nat.le_refl _, post⟩

theorem actual_active_call {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 123, ActiveCall full configuration command heap steps := by
  by_cases direct : q = 0 ∨ command = .query
  · exact actual_direct_active full configuration command allowed hl heap rep direct
  · have hq : 0 < q := Nat.pos_of_ne_zero (fun h => direct (Or.inl h))
    have declaration : command = .correct ∨ command = .error := by
      cases command with
      | query => exact False.elim (direct (Or.inr rfl))
      | correct => exact Or.inl rfl
      | error => exact Or.inr rfl
    obtain ⟨steps, upper, pref⟩ := actual_prefix full configuration command allowed hl heap rep
    obtain ⟨count, bounded, update⟩ := update_of_prefix full configuration command allowed hl hq declaration heap steps pref
    exact active_after_update full configuration command heap steps count upper bounded pref update

theorem actual_call {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 124,
      CallClaims 32768 q full (capacity full) (allocatedWords full)
        PSTRLiveControllerCode.program configuration command steps heap := by
  obtain ⟨steps, upper, post⟩ := actual_active_call full configuration command allowed hl heap rep
  exact ⟨steps + 1, by omega, callClaims_of_active full configuration command heap steps upper post⟩

end PaperProofs.Structure.LaminarTree.PSTRLiveController
