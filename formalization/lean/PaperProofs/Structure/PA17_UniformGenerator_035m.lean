module

public import PaperProofs.Structure.PA17_UniformGenerator_035l

/-! Dynamic fetched-prefix safety including PC alignment and active control.
Straight and branching segments share the actual encoded program and actual
natRun clock; no externally supplied trace is used. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035m

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035a PA17UniformGenerator035b
  PA17UniformGenerator035c PA17UniformGenerator035d PA17UniformGenerator035e
  PA17UniformGenerator035j PA17UniformGenerator035l

def RunSafe (B heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp) (steps : Nat) (state : NatState) : Prop :=
  (∀ count ≤ steps, let fresh := natRun rom program count state
    RegistersLE B fresh ∧ fresh.halted = false ∧ ∃ index ≤ program.length, fresh.pc = 5 * index) ∧
  (∀ count < steps, let fresh := natRun rom program count state
    ∃ index, ∃ hi : index < program.length, fresh.pc = 5 * index ∧ NatAccessFits rom heapWords fresh program[index])

theorem RunSafe.final (B heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp) (steps : Nat)
    (state : NatState) (hs : RunSafe B heapWords rom program steps state) :
    RegistersLE B (natRun rom program steps state) ∧ (natRun rom program steps state).halted = false ∧
      ∃ index ≤ program.length, (natRun rom program steps state).pc = 5 * index := hs.1 steps le_rfl

theorem RunSafe.add (B heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp) (left right : Nat)
    (state : NatState) (hl : RunSafe B heapWords rom program left state)
    (hr : RunSafe B heapWords rom program right (natRun rom program left state)) :
    RunSafe B heapWords rom program (left + right) state := by
  constructor
  · intro count hc
    by_cases hleft : count ≤ left
    · exact hl.1 count hleft
    · have he : count = left + (count - left) := by omega
      rw [he, natRun_add]
      exact hr.1 (count - left) (by omega)
  · intro count hc
    by_cases hleft : count < left
    · exact hl.2 count hleft
    · have he : count = left + (count - left) := by omega
      rw [he, natRun_add]
      exact hr.2 (count - left) (by omega)

theorem straight_segment_safe (rom : PhysicalROM) (B heapWords : Nat) (left ops right : List PackingOp)
    (hstraight : ∀ op ∈ ops, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hs : NumericSafe B heapWords rom ops state) :
    RunSafe B heapWords rom (left ++ ops ++ right) ops.length state := by
  have hrun := straight_prefix_run rom left ops right hstraight state hpc ha
  constructor
  · intro count hc
    rw [hrun count hc]
    refine ⟨hs.1 count hc, (runOps_halted rom _ state).trans ha, left.length + count, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · rw [runOps_pc rom _ state (fun op hm => hstraight op (List.mem_of_mem_take hm)),
        List.length_take_of_le hc, hpc]
      omega
  · intro count hc
    rw [hrun count hc.le]
    refine ⟨left.length + count, by simp only [List.length_append]; omega, ?_, ?_⟩
    · rw [runOps_pc rom _ state (fun op hm => hstraight op (List.mem_of_mem_take hm)),
        List.length_take_of_le hc.le, hpc]
      omega
    · rw [segment_index left ops right count hc]
      exact hs.2 count hc

theorem branch_segment_safe (rom : PhysicalROM) (B heapWords : Nat) (left lead right : List PackingOp) (last : PackingOp)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hs : NumericSafe B heapWords rom (lead ++ [last]) state)
    (hfinal : ∃ index ≤ (left ++ (lead ++ [last]) ++ right).length,
      (runOps rom (lead ++ [last]) state).pc = 5 * index) :
    RunSafe B heapWords rom (left ++ (lead ++ [last]) ++ right) (lead.length + 1) state := by
  have hrun := branch_segment_prefix rom left lead right last hstraight state hpc ha
  have hlen : (lead ++ [last]).length = lead.length + 1 := by simp only [List.length_append, List.length_singleton]
  constructor
  · intro count hc
    rw [hrun count hc]
    refine ⟨hs.1 count (by omega), (runOps_halted rom _ state).trans ha, ?_⟩
    by_cases hlast : count = lead.length + 1
    · simpa only [hlast, ← hlen, List.take_length] using hfinal
    · have hn : count ≤ lead.length := by omega
      rw [List.take_append_of_le_length hn]
      refine ⟨left.length + count, by simp only [List.length_append, hlen]; omega, ?_⟩
      rw [runOps_pc rom _ state (fun op hm => hstraight op (List.mem_of_mem_take hm)),
        List.length_take_of_le hn, hpc]
      omega
  · intro count hc
    rw [hrun count hc.le]
    have hn : count ≤ lead.length := by omega
    refine ⟨left.length + count, by simp only [List.length_append, hlen]; omega, ?_, ?_⟩
    · rw [List.take_append_of_le_length hn, runOps_pc rom _ state (fun op hm => hstraight op (List.mem_of_mem_take hm)),
        List.length_take_of_le hn, hpc]
      omega
    · rw [segment_index left (lead ++ [last]) right count (by omega)]
      exact hs.2 count (by omega)

theorem loopHead_safe (rom : PhysicalROM) (B heapWords counter exitIndex : Nat) (left right : List PackingOp)
    (hc : counter ≤ B) (hca : counter < heapWords) (hexit : 5 * exitIndex ≤ B)
    (htarget : exitIndex ≤ (left ++ loopHead counter (5 * exitIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE B state) (hcount : state.heap counter ≤ B) :
    RunSafe B heapWords rom (left ++ loopHead counter (5 * exitIndex) ++ right) 4 state := by
  let lead := (loopHead counter (5 * exitIndex)).take 3
  have hcode : loopHead counter (5 * exitIndex) = lead ++ [.jumpIfZero .value .fresh] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .value .fresh)
    (by simp [lead, loopHead, NoJump]) state hpc ha
    (by rw [← hcode]; exact loopHead_numeric rom B heapWords counter (5 * exitIndex) hc hca hexit state hr hcount)
  rw [← hcode]
  by_cases hz : state.heap counter = 0
  · exact ⟨exitIndex, htarget, by rw [head_pc, ite_eq_left hz]⟩
  · refine ⟨left.length + 4, by simp only [List.length_append]; change left.length + 4 ≤ left.length + 4 + right.length; omega, ?_⟩
    rw [head_pc, ite_eq_right hz, hpc]
    omega

theorem loopTail_safe (rom : PhysicalROM) (B heapWords counter entryIndex : Nat) (left right : List PackingOp)
    (hc : counter ≤ B) (hca : counter < heapWords) (hentry : 5 * entryIndex ≤ B) (hone : 1 ≤ B)
    (htarget : entryIndex ≤ (left ++ loopTail counter (5 * entryIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE B state) (hcount : state.heap counter ≤ B) :
    RunSafe B heapWords rom (left ++ loopTail counter (5 * entryIndex) ++ right) 8 state := by
  let lead := (loopTail counter (5 * entryIndex)).take 7
  have hcode : loopTail counter (5 * entryIndex) = lead ++ [.jumpIfZero .flag .fresh] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .flag .fresh)
    (by simp [lead, loopTail, NoJump]) state hpc ha
    (by rw [← hcode]; exact loopTail_numeric rom B heapWords counter (5 * entryIndex) hc hca hentry hone state hr hcount)
  rw [← hcode]
  exact ⟨entryIndex, htarget, tail_pc rom counter (5 * entryIndex) state⟩

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035m
