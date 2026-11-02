module

public import Structure.PSTR_BuildLower_ControlDataFrame_061

/-! Every actual dynamic-expression prefix protects the disjoint lexical
counter/save bank. Real copies for saving/restoring counters have an exact
single-slot write range. All statements concern real executed instructions. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlDataFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

theorem dynamic_prefix_offset (rom : PhysicalROM) (target : Register) (expr : Expr)
    (offset : Nat) (hoff : Fits bits offset) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hvm : offset ≠ registerOffset target) (outside : offset < 128 ∨ 128 + expr.size ≤ offset)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((DynamicStep.code target expr).take count) state).heap
      (state.register .address + BitVec.ofNat bits offset) = state.heap (state.register .address + BitVec.ofNat bits offset) := by
  have exprFrame : BankRangeFrame (bits := bits) rom (fixedExprCode expr) 128 (128 + expr.size) := by
    simpa only [fixedExprCode, relocateExpr_size] using
      bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) rom 128
  let middle := executeOps rom ((fixedExprCode expr).take count) state
  have middleBase : middle.register .address = state.register .address := exprFrame.1 state count
  have middleHeap := range_offset rom (fixedExprCode expr) 128 (128 + expr.size) exprFrame ht offset hoff outside state count
  have htarget : Fits bits (registerOffset target) := by
    have hh := (registerSlot_bounds target).2
    change registerOffset target < 39 at hh
    change registerOffset target < 2 ^ bits
    omega
  have tail := relativeWrite_prefix_frame rom (registerOffset target) middle
    (state.register .address + BitVec.ofNat bits offset)
    (by rw [middleBase]; exact offset_ne _ _ _ hoff htarget hvm) (count - (fixedExprCode expr).length)
  rw [DynamicStep.code, List.take_append, executeOps_append]
  exact tail.trans middleHeap

theorem dynamic_actual_prefix_offset (rom : PhysicalROM) (left right : List PackingOp) (target : Register) (expr : Expr)
    (offset : Nat) (hoff : Fits bits offset) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hvm : offset ≠ registerOffset target) (outside : offset < 128 ∨ 128 + expr.size ≤ offset)
    (state : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DynamicStep.code target expr ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ (DynamicStep.code target expr).length) :
    (packingRun rom (left ++ DynamicStep.code target expr ++ right) count state).heap
      (state.register .address + BitVec.ofNat bits offset) = state.heap (state.register .address + BitVec.ofNat bits offset) := by
  rw [SourceRep.straight_prefix rom left _ right state (DynamicStep.code_straight target expr) hcode hpcfit hpc ha count hc]
  exact dynamic_prefix_offset rom target expr offset hoff ht hvm outside state count

theorem copy_range (rom : PhysicalROM) (source target : Nat) :
    BankRangeFrame (bits := bits) rom (relativeCopy source target) target (target + 1) := by
  apply bankRangeFrame_append
  · refine ⟨fun state count => relativeRead_prefix_base rom source .value state (by decide) count, ?_⟩
    intro state point _ count
    exact relativeRead_prefix_heap rom source .value point state count
  · exact ViewFrame.relativeWrite_range rom target target (target + 1) le_rfl (by omega)

theorem copy_offset_frame (rom : PhysicalROM) (source target offset : Nat)
    (ht : Fits bits target) (hoff : Fits bits offset) (hne : offset ≠ target)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((relativeCopy source target).take count) state).heap
      (state.register .address + BitVec.ofNat bits offset) = state.heap (state.register .address + BitVec.ofNat bits offset) := by
  apply (copy_range rom source target).2
  intro changed hlo hhi
  have he : changed = target := by omega
  rw [he]
  exact offset_ne _ _ _ hoff ht hne

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlDataFrame
