module

public import Structure.PSTR_RepairEntry_045
public import Structure.PSTR_ReplySafety_026
public import Structure.PSTR_HD_HeadsReplyWords_128

/-! Actual selected-error program: locator19, cursor2, spill8, genuine
entry42, repair21, restore10. The entry really establishes flag=W11.
It is not inserted into the old39 theorem under a false cursor frame. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open PSTRReplySpill

def cursorProgram : List PackingOp :=
  [.base (.base (.constant .flag 8)),
   .base (.base (.add .flag .address .flag))]

def prepareProgram : List PackingOp := PSTRCountWorkspace.program ++ cursorProgram

def program : List PackingOp :=
  (((prepareProgram ++ spillProgram) ++ PSTRRepairEntry.program) ++ PSTRRuntimeRepair.program) ++ restoreProgram

theorem cursor_length : cursorProgram.length = 2 := rfl
theorem prepare_length : prepareProgram.length = 21 := rfl
theorem program_length : program.length = 102 := rfl

theorem cursor_straight : StraightProgram cursorProgram := by
  simp [cursorProgram, StraightProgram, StraightOp]

theorem straight_append {left right : List PackingOp}
    (hl : StraightProgram left) (hr : StraightProgram right) : StraightProgram (left ++ right) := by
  intro op hop
  rcases List.mem_append.mp hop with h | h
  · exact hl op h
  · exact hr op h

theorem prepare_straight : StraightProgram prepareProgram :=
  straight_append PSTRCountWorkspace.program_straight cursor_straight

theorem program_straight : StraightProgram program :=
  straight_append (straight_append (straight_append (straight_append prepare_straight spill_straight)
    PSTRRepairEntry.program_straight) PSTRRuntimeRepair.program_straight) restore_straight

theorem cursor_values {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (workspace : Nat) (ha : state.register .address = BitVec.ofNat bits workspace) :
    let after := executeOps rom cursorProgram state
    after.register .flag = BitVec.ofNat bits (workspace + 8) ∧ ReplyRegisters state after ∧ after.heap = state.heap := by
  simp +decide only [cursorProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ha, BitVec.ofNat_add_ofNat, ReplyRegisters, and_self]

theorem reply_registers_trans {bits : Nat} {before middle after : WordState bits}
    (h1 : ReplyRegisters before middle) (h2 : ReplyRegisters middle after) : ReplyRegisters before after :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem prepare_values {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap) :
    let after := executeOps (callInput q full command) prepareProgram state
    after.register .flag = BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 8) ∧
      ReplyRegisters state after ∧ after.heap = state.heap := by
  have located := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have cursor := cursor_values (callInput q full command)
    (executeOps (callInput q full command) PSTRCountWorkspace.program state) _ located.1
  rw [prepareProgram, executeOps_append]
  refine ⟨cursor.1, ?_, cursor.2.2.trans located.2.2.2.2.2.1⟩
  exact reply_registers_trans ⟨located.2.1, located.2.2.2.1, located.2.2.2.2.1, located.2.2.1⟩ cursor.2.1

theorem prepare_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 21) :
    (executeOps rom (prepareProgram.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem savedWord_of_reply {bits : Nat} (before after : WordState bits)
    (reply : ReplyRegisters before after) (offset : Nat) : savedWord after offset = savedWord before offset := by
  rcases reply with ⟨hv, ho, hf, hi⟩
  cases offset with
  | zero => exact hv
  | succ offset => cases offset with
    | zero => exact ho
    | succ offset => cases offset with
      | zero => exact hf
      | succ offset => exact hi

theorem spill_prefix_frame_outside {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base physical : Nat) (flag : state.register .flag = BitVec.ofNat bits base)
    (room : Fits bits (base + 3)) (fit : Fits bits physical)
    (outside : physical < base ∨ base + 3 < physical) (count : Nat) (hc : count ≤ 8) :
    (executeOps rom (spillProgram.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hne (offset : Nat) (ho : offset ≤ 3) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (base + offset) :=
    (ofNat_injective_of_fit _ _ fit (slot_fit base room offset ho)).not.mpr (by rcases outside with h | h <;> omega)
  have hz := hne 0 (by decide)
  simp only [Nat.add_zero] at hz
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  interval_cases count <;>
    simp +decide only [spillProgram, List.take_succ_cons, List.take_zero, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      flag, BitVec.ofNat_add_ofNat, h2, h3, hz, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide)]

theorem spill_width_slot {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (workspace : Nat) (flag : state.register .flag = BitVec.ofNat bits (workspace + 8))
    (room : Fits bits (workspace + 12)) :
    (executeOps rom spillProgram state).heap (BitVec.ofNat bits (workspace + 12)) =
      state.heap (BitVec.ofNat bits (workspace + 12)) := by
  simpa only [show 8 = spillProgram.length from rfl, List.take_length] using
    spill_prefix_frame_outside rom state (workspace + 8) (workspace + 12) flag
      ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room) room (Or.inr (by omega)) 8 le_rfl

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
