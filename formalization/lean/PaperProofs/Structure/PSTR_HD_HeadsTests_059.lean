module

public import PaperProofs.Structure.PSTR_HD_HeadsProgram_058

/-! The three real tests of the heads tail. These are arithmetic/heap-read
instruction sequences, not query or rank oracles. Their exits prepare the
actual branch registers at the fixed terminal/advance/append labels. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

def terminalLead (origin : Nat) : List PackingOp :=
  [.base (.subtract .flag .index .old), .base (.base (.constant .total (5 * (origin + 104))))]

def finiteLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .total 3)), .base (.base (.add .flag .address .total)),
   .base (.base (.loadHeap .flag .flag)), .base (.base (.constant .total (5 * (origin + 56))))]

def guardLead (origin : Nat) : List PackingOp :=
  [.base (.base (.loadHeap .value .address))] ++ successorGuard ++
  [.base (.base (.constant .total (5 * (origin + 67))))]

theorem terminalLead_length (origin : Nat) : (terminalLead origin).length = 2 := rfl

theorem finiteLead_length (origin : Nat) : (finiteLead origin).length = 4 := rfl

theorem guardLead_length (origin : Nat) : (guardLead origin).length = 7 := rfl

theorem scanLead_split (origin : Nat) : scanLead origin =
    terminalLead origin ++ [.jumpIfZero .flag .total] ++ finiteLead origin ++
    [.jumpIfZero .flag .total] ++ guardLead origin ++ [.jumpIfZero .flag .total] := rfl

theorem terminalLead_straight (origin : Nat) : StraightProgram (terminalLead origin) := by
  simp [terminalLead, StraightProgram, StraightOp]

theorem finiteLead_straight (origin : Nat) : StraightProgram (finiteLead origin) := by
  simp [finiteLead, StraightProgram, StraightOp]

theorem guardLead_straight (origin : Nat) : StraightProgram (guardLead origin) := by
  simp [guardLead, successorGuard, StraightProgram, StraightOp]

theorem execute_terminalLead {bits : Nat} (rom : PhysicalROM) (origin current N : Nat) (state : WordState bits)
    (hN : Fits bits N) (hs : Fits bits current)
    (hi : state.register .index = BitVec.ofNat bits N) (ho : state.register .old = BitVec.ofNat bits current) :
    let after := executeOps rom (terminalLead origin) state
    after.register .flag = BitVec.ofNat bits (N - current) ∧
    after.register .total = BitVec.ofNat bits (5 * (origin + 104)) ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  have hNn : (BitVec.ofNat bits N).toNat = N := Nat.mod_eq_of_lt hN
  have hsn : (BitVec.ofNat bits current).toNat = current := Nat.mod_eq_of_lt hs
  simp +decide [terminalLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hi, ho, hNn, hsn]

theorem terminal_zero_iff {bits : Nat} (current N : Nat) (hs : current ≤ N) (hN : Fits bits N) :
    (BitVec.ofNat bits (N - current)).toNat = 0 ↔ current = N := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt hN)]
  omega

theorem execute_finiteLead {bits : Nat} (rom : PhysicalROM) (origin endpoint finiteFlag : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hslot : state.heap (BitVec.ofNat bits (endpoint + 3)) = BitVec.ofNat bits finiteFlag) :
    let after := executeOps rom (finiteLead origin) state
    after.register .flag = BitVec.ofNat bits finiteFlag ∧
    after.register .total = BitVec.ofNat bits (5 * (origin + 56)) ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  simp +decide [finiteLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hslot, BitVec.ofNat_add_ofNat]

theorem finiteFlag_zero_iff {bits : Nat} (q rank : Nat) (hr : rank ≤ q + 2) (hq : Fits bits (q + 2)) :
    (BitVec.ofNat bits (q + 2 - rank)).toNat = 0 ↔ rank = q + 2 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt hq)]
  omega

theorem execute_guardLead {bits : Nat} (rom : PhysicalROM) (origin endpoint rank bad : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hslot : state.heap (BitVec.ofNat bits endpoint) = BitVec.ofNat bits rank)
    (hbad : state.register .fresh = BitVec.ofNat bits bad) (hr : Fits bits rank) (hb : Fits bits (bad + 1)) :
    let after := executeOps rom (guardLead origin) state
    after.register .flag = BitVec.ofNat bits (gap (bad + 1) rank) ∧
    after.register .total = BitVec.ofNat bits (5 * (origin + 67)) ∧
    after.register .old = state.register .old ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  have hrn : (BitVec.ofNat bits rank).toNat = rank := Nat.mod_eq_of_lt hr
  have hbn : (BitVec.ofNat bits (bad + 1)).toNat = bad + 1 := Nat.mod_eq_of_lt hb
  simp +decide [guardLead, successorGuard, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hslot, hbad, BitVec.ofNat_add_ofNat, hrn, hbn, gap]

theorem terminalLead_prefix_access {bits : Nat} (rom : PhysicalROM) (origin heapWords : Nat)
    (state : WordState bits) (count : Nat) (hc : count < (terminalLead origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((terminalLead origin).take count) state) (terminalLead origin)[count] := by
  change count < 2 at hc
  interval_cases count <;> trivial

theorem finiteLead_prefix_access {bits : Nat} (rom : PhysicalROM) (origin endpoint heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hroom : endpoint + 3 < heapWords) (count : Nat) (hc : count < (finiteLead origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((finiteLead origin).take count) state) (finiteLead origin)[count] := by
  have hp3 : (BitVec.ofNat bits (endpoint + 3)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  change count < 4 at hc
  interval_cases count <;>
    simp_all +decide [finiteLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat]

theorem guardLead_prefix_access {bits : Nat} (rom : PhysicalROM) (origin endpoint heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hroom : endpoint < heapWords) (count : Nat) (hc : count < (guardLead origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((guardLead origin).take count) state) (guardLead origin)[count] := by
  have hp0 : (BitVec.ofNat bits endpoint).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  change count < 7 at hc
  interval_cases count <;>
    simp_all +decide [guardLead, successorGuard, executeOps,
      packingAccessFits, AccessFits]

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
