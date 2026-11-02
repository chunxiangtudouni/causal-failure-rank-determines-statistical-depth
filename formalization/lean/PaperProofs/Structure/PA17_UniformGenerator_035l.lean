module

public import PaperProofs.Structure.PA17_UniformGenerator_035j

/-! Actual numeric/access safety of streaming output and loop controls.
Only the precise heap cells read by a block carry local numeric premises. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035l

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035a PA17UniformGenerator035b
  PA17UniformGenerator035c PA17UniformGenerator035d PA17UniformGenerator035e
  PA17UniformGenerator035j

theorem emitTail_numeric (rom : PhysicalROM) (B heapWords cursor outputBase : Nat)
    (hc : cursor ≤ B) (hca : cursor < heapWords) (houtput : outputBase ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hcount : state.heap cursor + 1 ≤ B) (haddress : outputBase + state.heap cursor ≤ B)
    (haccess : outputBase + state.heap cursor < heapWords) :
    NumericSafe B heapWords rom (emitTail cursor outputBase) state := by
  have hone : 1 ≤ B := by omega
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 8 at hn
    interval_cases count <;> cases register <;>
      simp [emitTail, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 8 at hn
    interval_cases count <;>
      simp [emitTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca, haccess]

theorem emitWord_numeric (expression : Expr) (rom : PhysicalROM) (B heapWords stack cursor outputBase : Nat)
    (hb : expression.Below stack) (hstackB : stack + expression.size ≤ B)
    (hstackH : stack + expression.size ≤ heapWords) (hcursor : cursor < stack) (hca : cursor < heapWords)
    (houtput : outputBase ≤ B) (state : NatState) (hr : RegistersLE B state)
    (hchecked : ExprChecked rom state.heap B heapWords expression)
    (hcount : state.heap cursor + 1 ≤ B) (haddress : outputBase + state.heap cursor ≤ B)
    (haccess : outputBase + state.heap cursor < heapWords) :
    NumericSafe B heapWords rom (emitWord expression stack cursor outputBase) state := by
  have hs := expression_numeric expression rom B heapWords stack hb hstackB hstackH state hr hchecked
  have hf := (expression.compile_correct rom stack hb state).2.1 cursor hcursor
  have hsize : 1 ≤ expression.size := by cases expression <;> simp [Expr.size]
  rw [emitWord]
  apply NumericSafe.append _ _ _ _ _ _ hs
  exact emitTail_numeric rom B heapWords cursor outputBase (by omega) hca houtput _ (hs.final _ _ _ _ _)
    (by rw [hf]; exact hcount) (by rw [hf]; exact haddress) (by rw [hf]; exact haccess)

theorem bind_numeric (expression : Expr) (rom : PhysicalROM) (B heapWords stack target : Nat)
    (hb : expression.Below stack) (hstackB : stack + expression.size ≤ B)
    (hstackH : stack + expression.size ≤ heapWords) (ht : target ≤ B) (hta : target < heapWords)
    (state : NatState) (hr : RegistersLE B state) (hchecked : ExprChecked rom state.heap B heapWords expression) :
    NumericSafe B heapWords rom (PA17UniformGenerator035d.bind expression stack target) state := by
  have hs := expression_numeric expression rom B heapWords stack hb hstackB hstackH state hr hchecked
  rw [PA17UniformGenerator035d.bind]
  exact NumericSafe.append _ _ _ _ _ _ hs (spill_numeric rom B heapWords target ht hta _ (hs.final _ _ _ _ _))

theorem loopHead_numeric (rom : PhysicalROM) (B heapWords counter exit : Nat)
    (hc : counter ≤ B) (hca : counter < heapWords) (hexit : exit ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hcount : state.heap counter ≤ B) :
    NumericSafe B heapWords rom (loopHead counter exit) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 4 at hn
    interval_cases count <;> cases register <;>
      simp [loopHead, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 4 at hn
    interval_cases count <;>
      simp [loopHead, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca]

theorem loopTail_numeric (rom : PhysicalROM) (B heapWords counter entry : Nat)
    (hc : counter ≤ B) (hca : counter < heapWords) (hentry : entry ≤ B) (hone : 1 ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hcount : state.heap counter ≤ B) :
    NumericSafe B heapWords rom (loopTail counter entry) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 8 at hn
    interval_cases count <;> cases register <;>
      simp [loopTail, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 8 at hn
    interval_cases count <;>
      simp [loopTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca]

theorem straight_prefix_run (rom : PhysicalROM) (left ops right : List PackingOp)
    (hstraight : ∀ op ∈ ops, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ ops.length) :
    natRun rom (left ++ ops ++ right) count state = runOps rom (ops.take count) state := by
  have hlen : (ops.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hlen]
  exact natRun_of_straight_segment rom _ _ left.length
    (by simp only [List.length_append, hlen]; omega)
    (fun position hp => by
      have hh := segment_index left ops right position (by rw [hlen] at hp; omega)
      simpa only [List.getElem_take] using hh)
    (fun op hm => hstraight op (List.mem_of_mem_take hm)) state hpc ha

theorem straight_segment_numeric (rom : PhysicalROM) (B heapWords : Nat) (left ops right : List PackingOp)
    (hstraight : ∀ op ∈ ops, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hs : NumericSafe B heapWords rom ops state) :
    (∀ count ≤ ops.length, RegistersLE B (natRun rom (left ++ ops ++ right) count state)) ∧
      ∀ count (hc : count < ops.length), NatAccessFits rom heapWords
        (natRun rom (left ++ ops ++ right) count state) ops[count] := by
  constructor
  · intro count hc; rw [straight_prefix_run rom left ops right hstraight state hpc ha count hc]; exact hs.1 count hc
  · intro count hc; rw [straight_prefix_run rom left ops right hstraight state hpc ha count hc.le]; exact hs.2 count hc

theorem branch_segment_prefix (rom : PhysicalROM) (left lead right : List PackingOp) (last : PackingOp)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ lead.length + 1) :
    natRun rom (left ++ (lead ++ [last]) ++ right) count state = runOps rom ((lead ++ [last]).take count) state := by
  exact natRun_segment_prefix rom _ lead last left.length
    (by simp only [List.length_append, List.length_singleton]; omega)
    (fun position hp => by
      have hh := segment_index left (lead ++ [last]) right position (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.getElem_append_left hp] using hh)
    (by
      have hh := segment_index left (lead ++ [last]) right lead.length (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] using hh)
    hstraight state hpc ha count hc

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035l
