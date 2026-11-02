module

public import Structure.PSTR_LiveControllerPrefix_137
public import Structure.PSTR_LiveControllerHalt_134

/-! Direct terminal case of the SAME1514-op live program: q0 commands
already updated inline, and positive QUERY. Other declarations follow136. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17A19RuntimeEntry020

theorem actual_direct_active {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap)
    (direct : q = 0 ∨ command = .query) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 123, ActiveCall full configuration command heap steps := by
  obtain ⟨steps, upper, pref⟩ := actual_prefix full configuration command allowed hl heap rep
  have dest (index : Nat) : PSTRLiveDispatch.destination q command 1371 1494 1505 1514 index = 1514 := by
    rcases direct with hq | rfl
    · simp only [PSTRLiveDispatch.destination, hq, ite_true]
    · simp only [PSTRLiveDispatch.destination, ite_self]
  have represented : HeapRepresents q full (capacity full) (nextConfiguration q full configuration command)
      (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).heap := by
    rcases direct with hq | rfl
    · simpa only [hq, ite_true] using pref.represented
    · simpa only [nextConfiguration, ite_self] using pref.represented
  refine ⟨steps, by omega, ?_, pref.active, represented, pref.reply, pref.capacityBound, pref.table, pref.safe⟩
  rw [PSTRLiveControllerCode.program_length]
  simpa only [dest] using pref.pc

theorem actual_direct_call {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap)
    (direct : q = 0 ∨ command = .query) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 124,
      CallClaims 32768 q full (capacity full) (allocatedWords full)
        PSTRLiveControllerCode.program configuration command steps heap := by
  obtain ⟨steps, upper, post⟩ := actual_direct_active full configuration command allowed hl heap rep direct
  exact ⟨steps + 1, by omega, callClaims_of_active full configuration command heap steps upper post⟩

end PaperProofs.Structure.LaminarTree.PSTRLiveController
