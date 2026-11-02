module

public import PaperProofs.Structure.PA17_UniformGenerator_035g
public import PaperProofs.Structure.PA17_UniformGenerator_035m

/-! Actual forward-copy prefix blocks, using hardware-only controls.
Bounds apply only to the source word actually loaded and the real addresses. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035aa

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035g PA17UniformGenerator035j PA17UniformGenerator035m

theorem copyInit_numeric (rom : PhysicalROM) (B heapWords cursor source : Nat)
    (hc : cursor ≤ B) (hca : cursor < heapWords) (hs : source ≤ B) (hone : 1 ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hn : state.heap cursor ≤ B) :
    NumericSafe B heapWords rom (copyInit cursor source) state := by
  constructor
  · intro count hcount register
    have hh := hr register
    change count ≤ 6 at hcount
    interval_cases count <;> cases register <;>
      simp [copyInit, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hcount
    change count < 6 at hcount
    interval_cases count <;>
      simp [copyInit, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca]

theorem copyHead_numeric (rom : PhysicalROM) (B heapWords exit : Nat) (he : exit ≤ B)
    (state : NatState) (hr : RegistersLE B state) : NumericSafe B heapWords rom (copyHead exit) state := by
  constructor
  · intro count hcount register
    have hh := hr register
    change count ≤ 2 at hcount
    interval_cases count <;> cases register <;>
      simp [copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hcount
    change count < 2 at hcount
    interval_cases count <;> trivial

theorem copyTail_numeric (rom : PhysicalROM) (B heapWords entry : Nat) (he : entry ≤ B)
    (state : NatState) (hr : RegistersLE B state)
    (hvalue : state.heap (state.register .address) ≤ B)
    (hsource : state.register .address < heapWords) (htarget : state.register .index < heapWords)
    (hnextSource : state.register .address + state.register .fresh ≤ B)
    (hnextTarget : state.register .index + state.register .fresh ≤ B) :
    NumericSafe B heapWords rom (copyTail entry) state := by
  have hsub := (Nat.sub_le (state.register .total) (state.register .fresh)).trans (hr .total)
  constructor
  · intro count hcount register
    have hh := hr register
    change count ≤ 7 at hcount
    interval_cases count <;> cases register <;>
      simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hcount
    change count < 7 at hcount
    interval_cases count <;>
      simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hsource, htarget]

theorem copyHead_safe (rom : PhysicalROM) (B heapWords exitIndex : Nat) (left right : List PackingOp)
    (he : 5 * exitIndex ≤ B) (ht : exitIndex ≤ (left ++ copyHead (5 * exitIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state) :
    RunSafe B heapWords rom (left ++ copyHead (5 * exitIndex) ++ right) 2 state := by
  let lead : List PackingOp := [.base (.base (.constant .old (5 * exitIndex)))]
  have hcode : copyHead (5 * exitIndex) = lead ++ [.jumpIfZero .total .old] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .total .old)
    (by simp [lead, NoJump]) state hpc ha (by rw [← hcode]; exact copyHead_numeric rom B heapWords _ he state hr)
  rw [← hcode]
  by_cases hz : state.register .total = 0
  · exact ⟨exitIndex, ht, by rw [copy_head_pc, ite_eq_left hz]⟩
  · refine ⟨left.length + 2, by simp only [List.length_append]; change left.length + 2 ≤ left.length + 2 + right.length; omega, ?_⟩
    rw [copy_head_pc, ite_eq_right hz, hpc]
    omega

theorem copyTail_safe (rom : PhysicalROM) (B heapWords entryIndex : Nat) (left right : List PackingOp)
    (he : 5 * entryIndex ≤ B) (ht : entryIndex ≤ (left ++ copyTail (5 * entryIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hz : state.register .flag = 0) (hvalue : state.heap (state.register .address) ≤ B)
    (hsource : state.register .address < heapWords) (htarget : state.register .index < heapWords)
    (hnextSource : state.register .address + state.register .fresh ≤ B)
    (hnextTarget : state.register .index + state.register .fresh ≤ B) :
    RunSafe B heapWords rom (left ++ copyTail (5 * entryIndex) ++ right) 7 state := by
  let lead := (copyTail (5 * entryIndex)).take 6
  have hcode : copyTail (5 * entryIndex) = lead ++ [.jumpIfZero .flag .old] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .flag .old)
    (by simp [lead, copyTail, NoJump]) state hpc ha
    (by rw [← hcode]; exact copyTail_numeric rom B heapWords _ he state hr hvalue hsource htarget hnextSource hnextTarget)
  rw [← hcode]
  exact ⟨entryIndex, ht, copy_tail_pc rom _ state hz⟩

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035aa
