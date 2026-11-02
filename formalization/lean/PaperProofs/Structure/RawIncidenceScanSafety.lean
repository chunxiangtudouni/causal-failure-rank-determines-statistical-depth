module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.PackingWordBounds
import Mathlib.Tactic.IntervalCases

/-! Numeric and access invariants of the actual encoded q-bit scan. All
scratch cells and raw incidence reads below belong to the original checker. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceScanSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM

def registerBound (N q : Nat) : Nat := N * q + N + q + 640

def RegistersBound (N q : Nat) (state : NatState) : Prop :=
  ∀ reg : Register, state.register reg ≤ registerBound N q

def NatAccessFits (rom : PhysicalROM) (heapWords : Nat) (state : NatState) : PackingOp → Prop
  | .base op => AccessFits rom heapWords ⟨state.register, state.heap, state.pc⟩ op
  | _ => True

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  RegistersBound full.length q state ∧ state.pc ≤ 630 ∧
    ∃ index ≤ checker.length, state.pc = 5 * index ∧
      (state.halted = false → match PackingOp.decode (natFetch checker state.pc) with
        | none => natFetch checker state.pc = haltWords
        | some op => NatAccessFits (rawIncidenceROM q full) 8 state op)

theorem safePoint_of_body (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (index : Nat) (hi : index < checker.length) (hpc : state.pc = 5 * index)
    (hr : RegistersBound full.length q state)
    (ha : NatAccessFits (rawIncidenceROM q full) 8 state (checker[index]'hi)) : SafePoint q full state := by
  refine ⟨hr, ?_, index, hi.le, hpc, ?_⟩
  · rw [hpc]
    rw [checker_length] at hi
    omega
  · intro _
    rw [hpc, natFetch_body checker index hi, decode_encode]
    exact ha

theorem safePoint_of_halt (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 630) (hr : RegistersBound full.length q state) : SafePoint q full state := by
  refine ⟨hr, hpc.le, 126, by rw [checker_length], hpc, ?_⟩
  intro _
  rw [hpc, show 630 = 5 * checker.length by rw [checker_length], natFetch_halt, decode_halt]

theorem raw_bit_le_one (q : Nat) (full : List (Finset (Fin q))) (row : Fin full.length) (tool : Fin q) :
    (rawIncidenceROM q full).semantic.read .input (2 + row.val * q + tool.val) ≤ 1 := by
  rw [raw_bit]
  simp only [bit]
  split_ifs <;> omega

theorem incidence_address_bound (N q row tool : Nat) (hr : row < N) (ht : tool < q) :
    2 + row * q + tool < N * q + 2 := by
  have hp := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hp
  omega

theorem natRun_segment_prefix (rom : PhysicalROM) (program lead : List PackingOp)
    (last : PackingOp) (start : Nat) (hbound : start + lead.length + 1 ≤ program.length)
    (hcode : ∀ position (hp : position < lead.length), program[start + position]'(by omega) = lead[position])
    (hlast : program[start + lead.length]'(by omega) = last)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (count : Nat) (hcount : count ≤ lead.length + 1) :
    natRun rom program count state = runOps rom ((lead ++ [last]).take count) state := by
  by_cases hc : count ≤ lead.length
  · have htake : ((lead ++ [last]).take count) = lead.take count := List.take_append_of_le_length hc
    rw [htake]
    have hl : (lead.take count).length = count := List.length_take_of_le hc
    conv_lhs => rw [← hl]
    apply natRun_of_straight_segment rom program (lead.take count) start (by omega) ?_ ?_ state hpc hactive
    · intro position hp
      have hp' : position < lead.length := by rw [hl] at hp; omega
      simpa only [List.getElem_take] using hcode position hp'
    · intro op ho
      exact hstraight op (List.mem_of_mem_take ho)
  · have heq : count = lead.length + 1 := by omega
    rw [heq, natRun_of_segment_last rom program lead last start hbound hcode hlast hstraight state hpc hactive,
      List.take_of_length_le (by simp), runOps_append]
    rfl

end PaperProofs.Structure.LaminarTree.RawIncidenceScanSafety
