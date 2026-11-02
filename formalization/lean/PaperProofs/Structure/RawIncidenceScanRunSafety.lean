module

public import PaperProofs.Structure.RawIncidenceScanSafety
public import PaperProofs.Structure.RawIncidenceMacroSafety
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceScanSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM

def PrefixSafe (q : Nat) (full : List (Finset (Fin q))) (block : List PackingOp) (state : NatState) : Prop :=
  ∀ count ≤ block.length,
    RegistersBound full.length q (runOps (rawIncidenceROM q full) (block.take count) state) ∧
      (∀ hc : count < block.length, NatAccessFits (rawIncidenceROM q full) 8
        (runOps (rawIncidenceROM q full) (block.take count) state) (block[count]'hc))

theorem PrefixSafe.append (q : Nat) (full : List (Finset (Fin q))) (left right : List PackingOp)
    (state : NatState) (hl : PrefixSafe q full left state)
    (hr : PrefixSafe q full right (runOps (rawIncidenceROM q full) left state)) :
    PrefixSafe q full (left ++ right) state := by
  intro count hc
  by_cases hleft : count < left.length
  · have htake : (left ++ right).take count = left.take count := List.take_append_of_le_length hleft.le
    rw [htake]
    refine ⟨(hl count hleft.le).1, ?_⟩
    intro hcount
    rw [List.getElem_append_left hleft]
    exact (hl count hleft.le).2 hleft
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hleft)
    have he : extra ≤ right.length := by rw [List.length_append] at hc; omega
    have htake : (left ++ right).take (left.length + extra) = left ++ right.take extra := by
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    rw [htake, runOps_append]
    refine ⟨(hr extra he).1, ?_⟩
    intro hcount
    have hei : extra < right.length := by rw [List.length_append] at hcount; omega
    rw [List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using (hr extra he).2 hei

theorem readPairBit_heap (rom : PhysicalROM) (cell : Nat) (target : Register) (state : NatState) :
    (runOps rom (readPairBit cell target) state).heap = state.heap := rfl

theorem readPairBit_target (rom : PhysicalROM) (cell : Nat) (target : Register) (state : NatState) :
    (runOps rom (readPairBit cell target) state).register target =
      rom.semantic.read .input (state.heap cell * state.heap 1 + state.heap 4 + 2) := by
  simp [runOps, readPairBit, loadCell, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem readPairBit_prefix_registerBound (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (row : Fin full.length) (tool : Fin q)
    (target : Register) (state : NatState) (hreg : RegistersBound full.length q state)
    (hrow : state.heap cell = row.val) (hq : state.heap 1 = q) (hk : state.heap 4 = tool.val)
    (count : Nat) (hc : count ≤ 11) :
    RegistersBound full.length q (runOps (rawIncidenceROM q full) ((readPairBit cell target).take count) state) := by
  have h0 := hreg .address
  have h1 := hreg .index
  have h2 := hreg .value
  have h3 := hreg .total
  have h4 := hreg .old
  have h5 := hreg .fresh
  have h6 := hreg .flag
  have ha := incidence_address_bound full.length q row.val tool.val row.isLt tool.isLt
  have hb : (rawIncidenceROM q full).semantic.read .input (row.val * q + tool.val + 2) ≤ 1 := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using raw_bit_le_one q full row tool
  have hp : row.val * q ≤ full.length * q := Nat.mul_le_mul_right q row.isLt.le
  have hi := row.isLt
  have ht := tool.isLt
  unfold RegistersBound
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [readPairBit, loadCell, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      Function.update_apply, hrow, hq, hk, registerBound] <;>
    (try split_ifs) <;> simp_all only [registerBound] <;> omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem readPairBit_prefix_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (row : Fin full.length) (tool : Fin q)
    (target : Register) (state : NatState)
    (hrow : state.heap cell = row.val) (hq : state.heap 1 = q) (hk : state.heap 4 = tool.val)
    (count : Nat) (hc : count < 11) :
    NatAccessFits (rawIncidenceROM q full) 8
      (runOps (rawIncidenceROM q full) ((readPairBit cell target).take count) state)
      ((readPairBit cell target)[count]'(by change count < 11; exact hc)) := by
  have ha := incidence_address_bound full.length q row.val tool.val row.isLt tool.isLt
  interval_cases count <;>
    simp [NatAccessFits, AccessFits, readPairBit, loadCell, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, hrow, hq, hk, raw_input_length] <;> omega

theorem readPairBit_prefixSafe (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (row : Fin full.length) (tool : Fin q)
    (target : Register) (state : NatState) (hreg : RegistersBound full.length q state)
    (hrow : state.heap cell = row.val) (hq : state.heap 1 = q) (hk : state.heap 4 = tool.val) :
    PrefixSafe q full (readPairBit cell target) state := by
  intro count hc
  refine ⟨readPairBit_prefix_registerBound q full cell hcell row tool target state hreg hrow hq hk count hc, ?_⟩
  intro hlt
  exact readPairBit_prefix_accessFits q full cell hcell row tool target state hrow hq hk count hlt

def WitnessOperation (op : Op) : Prop :=
  op = .base (.minimum .flag .old .fresh) ∨
    op = .subtract .flag .old .fresh ∨ op = .subtract .flag .fresh .old

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem addWitness_prefix_registerBound (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (op : Op) (hop : WitnessOperation op)
    (state : NatState) (hreg : RegistersBound full.length q state)
    (hcounter : state.heap cell < q) (hleft : state.register .old ≤ 1) (hright : state.register .fresh ≤ 1)
    (count : Nat) (hc : count ≤ 5) :
    RegistersBound full.length q (runOps (rawIncidenceROM q full) ((addWitness cell op).take count) state) := by
  have h0 := hreg .address
  have h1 := hreg .index
  have h2 := hreg .value
  have h3 := hreg .total
  have h4 := hreg .old
  have h5 := hreg .fresh
  have h6 := hreg .flag
  unfold RegistersBound
  rcases hop with rfl | rfl | rfl <;> interval_cases count <;> intro reg <;> cases reg <;>
    simp [addWitness, runOps, natExecuteOp, Op.execute, Instruction.execute, registerBound] <;>
    simp_all [registerBound] <;> omega

set_option maxRecDepth 12000 in
theorem addWitness_prefix_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (op : Op) (hop : WitnessOperation op)
    (state : NatState) (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) 8
      (runOps (rawIncidenceROM q full) ((addWitness cell op).take count) state)
      ((addWitness cell op)[count]'(by change count < 5; exact hc)) := by
  rcases hop with rfl | rfl | rfl <;> interval_cases count <;>
    simp [NatAccessFits, AccessFits, addWitness, runOps, natExecuteOp, Op.execute, Instruction.execute] <;> omega

theorem addWitness_prefixSafe (q : Nat) (full : List (Finset (Fin q)))
    (cell : Nat) (hcell : cell < 8) (op : Op) (hop : WitnessOperation op)
    (state : NatState) (hreg : RegistersBound full.length q state)
    (hcounter : state.heap cell < q) (hleft : state.register .old ≤ 1) (hright : state.register .fresh ≤ 1) :
    PrefixSafe q full (addWitness cell op) state := by
  intro count hc
  exact ⟨addWitness_prefix_registerBound q full cell hcell op hop state hreg hcounter hleft hright count hc,
    fun hlt => addWitness_prefix_accessFits q full cell hcell op hop state count hlt⟩

theorem addWitness_bits (rom : PhysicalROM) (cell : Nat) (op : Op) (hop : WitnessOperation op) (state : NatState) :
    (runOps rom (addWitness cell op) state).register .old = state.register .old ∧
      (runOps rom (addWitness cell op) state).register .fresh = state.register .fresh := by
  rcases hop with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem addWitness_frame (rom : PhysicalROM) (cell : Nat) (op : Op) (hop : WitnessOperation op)
    (state : NatState) (address : Nat) (hne : address ≠ cell) :
    (runOps rom (addWitness cell op) state).heap address = state.heap address := by
  rcases hop with rfl | rfl | rfl <;>
    simp [runOps, addWitness, natExecuteOp, Op.execute, Instruction.execute, hne]

theorem PrefixSafe.endpoint (q : Nat) (full : List (Finset (Fin q))) (block : List PackingOp) (state : NatState)
    (h : PrefixSafe q full block state) : RegistersBound full.length q (runOps (rawIncidenceROM q full) block state) := by
  simpa only [List.take_length] using (h block.length le_rfl).1

theorem testCell_prefixSafe (q : Nat) (full : List (Finset (Fin q)))
    (bound counter exit : Nat) (state : NatState) (hr : RegistersBound full.length q state)
    (hb : bound < 8) (hc : counter < 8) (he : exit ≤ 126)
    (hv : state.heap bound ≤ registerBound full.length q) (hw : state.heap counter ≤ registerBound full.length q) :
    PrefixSafe q full (testCell bound counter exit) state := by
  intro count hcount
  exact ⟨RawIncidenceMacroSafety.testCell_prefix_registerBound full.length q (rawIncidenceROM q full)
    bound counter exit state hr hb hc he hv hw count hcount,
    fun hlt => RawIncidenceMacroSafety.testCell_prefix_accessFits (rawIncidenceROM q full)
      bound counter exit state hb hc count hlt⟩

theorem incrementCell_prefixSafe (q : Nat) (full : List (Finset (Fin q))) (cell : Nat) (state : NatState)
    (hr : RegistersBound full.length q state) (hc : cell < 8)
    (hv : state.heap cell + 1 ≤ registerBound full.length q) : PrefixSafe q full (incrementCell cell) state := by
  intro count hcount
  exact ⟨RawIncidenceMacroSafety.incrementCell_prefix_registerBound full.length q (rawIncidenceROM q full)
    cell state hr hc hv count hcount,
    fun hlt => RawIncidenceMacroSafety.incrementCell_prefix_accessFits (rawIncidenceROM q full) cell state hc count hlt⟩

theorem jumpTo_prefixSafe (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hr : RegistersBound full.length q state) (he : exit ≤ 126) : PrefixSafe q full (jumpTo exit) state := by
  intro count hcount
  exact ⟨RawIncidenceMacroSafety.jumpTo_prefix_registerBound full.length q (rawIncidenceROM q full)
    exit state hr he count hcount,
    fun hlt => RawIncidenceMacroSafety.jumpTo_prefix_accessFits (rawIncidenceROM q full) exit state count hlt⟩

theorem checkerSegment_safePoint (q : Nat) (full : List (Finset (Fin q)))
    (lead : List PackingOp) (last : PackingOp) (start : Nat)
    (hbound : start + lead.length + 1 ≤ checker.length)
    (hcode : ∀ position (hp : position < lead.length), checker[start + position]'(by omega) = lead[position])
    (hlast : checker[start + lead.length]'(by omega) = last)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hsafe : PrefixSafe q full (lead ++ [last]) state)
    (count : Nat) (hcount : count < lead.length + 1) :
    SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have hc : count ≤ lead.length := by omega
  have hi : start + count < checker.length := by omega
  rw [natRun_segment_prefix (rawIncidenceROM q full) checker lead last start hbound hcode hlast hstraight state hpc hactive count hcount.le]
  have htake : (lead ++ [last]).take count = lead.take count := List.take_append_of_le_length hc
  have hp : (runOps (rawIncidenceROM q full) ((lead ++ [last]).take count) state).pc = 5 * (start + count) := by
    rw [htake, runOps_pc _ _ _ (fun op ho => hstraight op (List.mem_of_mem_take ho)),
      List.length_take_of_le hc, hpc]
    omega
  have he : checker[start + count]'hi = (lead ++ [last])[count]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) := by
    by_cases hl : count < lead.length
    · rw [List.getElem_append_left hl]
      exact hcode count hl
    · have heq : count = lead.length := by omega
      subst count
      simpa using hlast
  apply safePoint_of_body q full _ (start + count) hi hp (hsafe count (by simp; omega)).1
  rw [he]
  exact (hsafe count (by simp; omega)).2 (by simp; omega)

theorem readRight_preserves_old (rom : PhysicalROM) (state : NatState) :
    (runOps rom (readPairBit 3 .fresh) state).register .old = state.register .old := rfl

set_option maxHeartbeats 1500000 in
theorem pairBitLoopBody_prefixSafe (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (tool : Fin q) (state : NatState)
    (hr : RegistersBound full.length q state) (hq : state.heap 1 = q)
    (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val) (hk : state.heap 4 = tool.val)
    (h5 : state.heap 5 ≤ tool.val) (h6 : state.heap 6 ≤ tool.val) (h7 : state.heap 7 ≤ tool.val) :
    PrefixSafe q full pairBitLoopBody state := by
  let rom := rawIncidenceROM q full
  let readL := runOps rom (readPairBit 2 .old) state
  let readR := runOps rom (readPairBit 3 .fresh) readL
  let op5 : Op := .base (.minimum .flag .old .fresh)
  let op6 : Op := .subtract .flag .old .fresh
  let op7 : Op := .subtract .flag .fresh .old
  have hop5 : WitnessOperation op5 := Or.inl rfl
  have hop6 : WitnessOperation op6 := Or.inr (Or.inl rfl)
  have hop7 : WitnessOperation op7 := Or.inr (Or.inr rfl)
  let w5 := runOps rom (addWitness 5 op5) readR
  let w6 := runOps rom (addWitness 6 op6) w5
  let w7 := runOps rom (addWitness 7 op7) w6
  let incr := runOps rom (incrementCell 4) w7
  have hsL := readPairBit_prefixSafe q full 2 (by decide) left tool .old state hr hl hq hk
  have hLHeap : readL.heap = state.heap := readPairBit_heap rom 2 .old state
  have hsR := readPairBit_prefixSafe q full 3 (by decide) right tool .fresh readL
    (PrefixSafe.endpoint q full _ state hsL) (by rw [hLHeap]; exact hj) (by rw [hLHeap]; exact hq) (by rw [hLHeap]; exact hk)
  have hRHeap : readR.heap = state.heap := (readPairBit_heap rom 3 .fresh readL).trans hLHeap
  have hLBit : readR.register .old ≤ 1 := by
    rw [readRight_preserves_old rom readL, readPairBit_target rom 2 .old state, hl, hq, hk]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using raw_bit_le_one q full left tool
  have hRBit : readR.register .fresh ≤ 1 := by
    rw [readPairBit_target rom 3 .fresh readL, hLHeap, hj, hq, hk]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using raw_bit_le_one q full right tool
  have hs5 := addWitness_prefixSafe q full 5 (by decide) op5 hop5 readR
    (PrefixSafe.endpoint q full _ readL hsR) (by rw [hRHeap]; exact h5.trans_lt tool.isLt) hLBit hRBit
  have h5Bits := addWitness_bits rom 5 op5 hop5 readR
  have hs6 := addWitness_prefixSafe q full 6 (by decide) op6 hop6 w5
    (PrefixSafe.endpoint q full _ readR hs5)
    (by rw [addWitness_frame rom 5 op5 hop5 readR 6 (by decide), hRHeap]; exact h6.trans_lt tool.isLt)
    (h5Bits.1.trans_le hLBit) (h5Bits.2.trans_le hRBit)
  have h6Bits := addWitness_bits rom 6 op6 hop6 w5
  have hs7 := addWitness_prefixSafe q full 7 (by decide) op7 hop7 w6
    (PrefixSafe.endpoint q full _ w5 hs6)
    (by rw [addWitness_frame rom 6 op6 hop6 w5 7 (by decide), addWitness_frame rom 5 op5 hop5 readR 7 (by decide), hRHeap]
        exact h7.trans_lt tool.isLt)
    (h6Bits.1.trans_le (h5Bits.1.trans_le hLBit)) (h6Bits.2.trans_le (h5Bits.2.trans_le hRBit))
  have hcounter : w7.heap 4 = tool.val := by
    rw [addWitness_frame rom 7 op7 hop7 w6 4 (by decide), addWitness_frame rom 6 op6 hop6 w5 4 (by decide),
      addWitness_frame rom 5 op5 hop5 readR 4 (by decide), hRHeap, hk]
  have hsI := incrementCell_prefixSafe q full 4 w7 (PrefixSafe.endpoint q full _ w6 hs7) (by decide)
    (by rw [hcounter]; dsimp [registerBound]; have := tool.isLt; omega)
  have hsJ := jumpTo_prefixSafe q full 39 incr (PrefixSafe.endpoint q full _ w7 hsI) (by decide)
  have tailI := PrefixSafe.append q full (incrementCell 4) (jumpTo 39) w7 hsI hsJ
  have tail7 := PrefixSafe.append q full (addWitness 7 op7) _ w6 hs7 tailI
  have tail6 := PrefixSafe.append q full (addWitness 6 op6) _ w5 hs6 tail7
  have tail5 := PrefixSafe.append q full (addWitness 5 op5) _ readR hs5 tail6
  have tailR := PrefixSafe.append q full (readPairBit 3 .fresh) _ readL hsR tail5
  have tailL := PrefixSafe.append q full (readPairBit 2 .old) _ state hsL tailR
  simpa only [pairBitLoopBody, pairBitKernel, List.append_assoc, op5, op6, op7] using tailL

set_option maxRecDepth 12000 in
theorem checker_bitTest_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false) (hr : RegistersBound full.length q state)
    (hq : state.heap 1 ≤ registerBound full.length q) (hk : state.heap 4 ≤ registerBound full.length q)
    (count : Nat) (hc : count ≤ 7) : SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have hs := testCell_prefixSafe q full 1 4 92 state hr (by decide) (by decide) (by decide) hq hk
  by_cases hlt : count < 7
  · let lead := (testCell 1 4 92).take 6
    have hlength : lead.length = 6 := rfl
    have hcode : ∀ position (hp : position < lead.length), checker[39 + position]'(by rw [checker_length]; rw [hlength] at hp; omega) = lead[position] := by
      intro position hp
      rw [hlength] at hp
      interval_cases position <;> rfl
    have hstraight : ∀ op ∈ lead, NoJump op := by simp [lead, testCell, loadCell, NoJump]
    apply checkerSegment_safePoint q full lead (.jumpIfZero .flag .index) 39
      (by rw [hlength, checker_length]; omega) hcode (by rfl) hstraight state hpc hactive
      (by exact hs) count
    rw [hlength]
    exact hlt
  · have heq : count = 7 := by omega
    rw [heq, natRun_checker_bitTest _ state hpc hactive]
    have hregs := PrefixSafe.endpoint q full _ state hs
    have hp := (runOps_testCell (rawIncidenceROM q full) 1 4 92 state).2.2.1
    by_cases hz : state.heap 1 - state.heap 4 = 0
    · have hp' : (runOps (rawIncidenceROM q full) (testCell 1 4 92) state).pc = 460 := by simpa only [hz, ite_true] using hp
      apply safePoint_of_body q full _ 92 (by rw [checker_length]; decide) hp' hregs
      exact True.intro
    · have hp' : (runOps (rawIncidenceROM q full) (testCell 1 4 92) state).pc = 230 := by simpa only [hz, ite_false, hpc] using hp
      apply safePoint_of_body q full _ 46 (by rw [checker_length]; decide) hp' hregs
      exact True.intro

set_option maxRecDepth 12000 in
theorem checker_body_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 230) (hactive : state.halted = false)
    (hs : PrefixSafe q full pairBitLoopBody state) (count : Nat) (hc : count ≤ 46) :
    SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  by_cases hlt : count < 46
  · have hcode : ∀ position (hp : position < pairBitStraight.length),
        checker[46 + position]'(by rw [checker_length]; rw [pairBitStraight_length] at hp; omega) = pairBitStraight[position] := by
      intro position hp
      rw [pairBitStraight_length] at hp
      interval_cases position <;> rfl
    have hstraight : ∀ op ∈ pairBitStraight, NoJump op := by
      simp [pairBitStraight, pairBitKernel, readPairBit, loadCell, addWitness, incrementCell, storeCell, jumpTo, NoJump]
    apply checkerSegment_safePoint q full pairBitStraight (.jumpIfZero .flag .index) 46
      (by rw [pairBitStraight_length, checker_length]; omega) hcode (by rfl) hstraight state hpc hactive
      (by simpa only [← pairBitLoopBody_split] using hs) count
    rw [pairBitStraight_length]
    exact hlt
  · have heq : count = 46 := by omega
    rw [heq, natRun_checker_pairBitLoopBody _ state hpc hactive]
    have hregs := PrefixSafe.endpoint q full _ state hs
    rcases runOps_pairBitLoopBody (rawIncidenceROM q full) state with ⟨_, _, _, _, _, _, hp, _⟩
    apply safePoint_of_body q full _ 39 (by rw [checker_length]; decide) hp hregs
    exact True.intro

set_option maxHeartbeats 1500000 in
theorem checker_pairIteration_safe (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hq : state.heap 1 = q) (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val) (hk : state.heap 4 = tool.val)
    (h5 : state.heap 5 ≤ tool.val) (h6 : state.heap 6 ≤ tool.val) (h7 : state.heap 7 ≤ tool.val)
    (hr : RegistersBound full.length q state) (count : Nat) (hc : count ≤ 53) :
    SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have hbq : state.heap 1 ≤ registerBound full.length q := by rw [hq]; dsimp [registerBound]; omega
  have hbk : state.heap 4 ≤ registerBound full.length q := by rw [hk]; dsimp [registerBound]; have := tool.isLt; omega
  by_cases hsmall : count ≤ 7
  · exact checker_bitTest_safe q full state hpc hactive hr hbq hbk count hsmall
  · let tested := runOps (rawIncidenceROM q full) (testCell 1 4 92) state
    have ht := runOps_testCell (rawIncidenceROM q full) 1 4 92 state
    have htHeap : tested.heap = state.heap := ht.1
    have htPc : tested.pc = 230 := by
      have hne : state.heap 1 - state.heap 4 ≠ 0 := by rw [hq, hk]; exact Nat.sub_ne_zero_of_lt tool.isLt
      simpa only [tested, hne, ite_false, hpc] using ht.2.2.1
    have htActive : tested.halted = false := ht.2.2.2.trans hactive
    have htRegs := PrefixSafe.endpoint q full _ state
      (testCell_prefixSafe q full 1 4 92 state hr (by decide) (by decide) (by decide) hbq hbk)
    have hbody := pairBitLoopBody_prefixSafe q full left right tool tested htRegs
      (by rw [htHeap]; exact hq) (by rw [htHeap]; exact hl) (by rw [htHeap]; exact hj) (by rw [htHeap]; exact hk)
      (by rw [htHeap]; exact h5) (by rw [htHeap]; exact h6) (by rw [htHeap]; exact h7)
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 7 ≤ count by omega)
    rw [heq, natRun_add, natRun_checker_bitTest _ state hpc hactive]
    exact checker_body_safe q full tested htPc htActive hbody extra (by omega)

structure ScanBoundary (N q i j count : Nat) (state : NatState) : Prop where
  dimension : state.heap 0 = N
  tools : state.heap 1 = q
  left : state.heap 2 = i
  right : state.heap 3 = j
  counter : state.heap 4 = count
  intersection : state.heap 5 ≤ count
  leftOnly : state.heap 6 ≤ count
  rightOnly : state.heap 7 ≤ count
  pc : state.pc = 195
  active : state.halted = false

theorem checker_pairScan_boundary (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hN : state.heap 0 = full.length) (hq : state.heap 1 = q)
    (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val)
    (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0) (h7 : state.heap 7 = 0)
    (count : Nat) (hc : count ≤ q) :
    ScanBoundary full.length q left.val right.val count (natRun (rawIncidenceROM q full) checker (53 * count) state) := by
  let rom := rawIncidenceROM q full
  have hL (offset : Nat) (ho : offset < count) : leftAt rom state offset ≤ 1 := by
    simpa only [leftAt, hl, hq, h4, Nat.add_zero] using raw_bit_le_one q full left ⟨offset, ho.trans_le hc⟩
  have hR (offset : Nat) (ho : offset < count) : rightAt rom state offset ≤ 1 := by
    simpa only [rightAt, hj, hq, h4, Nat.add_zero] using raw_bit_le_one q full right ⟨offset, ho.trans_le hc⟩
  have hs5 : (∑ offset ∈ Finset.range count, min (leftAt rom state offset) (rightAt rom state offset)) ≤ count := by
    calc
      _ ≤ ∑ _offset ∈ Finset.range count, (1 : Nat) := Finset.sum_le_sum (fun offset ho =>
        (Nat.min_le_left _ _).trans (hL offset (Finset.mem_range.mp ho)))
      _ = count := by simp
  have hs6 : (∑ offset ∈ Finset.range count, (leftAt rom state offset - rightAt rom state offset)) ≤ count := by
    calc
      _ ≤ ∑ _offset ∈ Finset.range count, (1 : Nat) := Finset.sum_le_sum (fun offset ho =>
        (Nat.sub_le _ _).trans (hL offset (Finset.mem_range.mp ho)))
      _ = count := by simp
  have hs7 : (∑ offset ∈ Finset.range count, (rightAt rom state offset - leftAt rom state offset)) ≤ count := by
    calc
      _ ≤ ∑ _offset ∈ Finset.range count, (1 : Nat) := Finset.sum_le_sum (fun offset ho =>
        (Nat.sub_le _ _).trans (hR offset (Finset.mem_range.mp ho)))
      _ = count := by simp
  have hp := natRun_checker_pairScan_partial rom state hpc hactive count (by rw [h4, hq]; omega)
  dsimp only at hp
  rw [h4, h5, h6, h7, Nat.zero_add] at hp
  simp only [Nat.zero_add] at hp
  rcases hp with ⟨hk, hp5, hp6, hp7, hf, _, hpp, hpa⟩
  refine ⟨(hf 0 (by decide) (by decide) (by decide) (by decide)).trans hN,
    (hf 1 (by decide) (by decide) (by decide) (by decide)).trans hq,
    (hf 2 (by decide) (by decide) (by decide) (by decide)).trans hl,
    (hf 3 (by decide) (by decide) (by decide) (by decide)).trans hj,
    hk, hp5.trans_le hs5, hp6.trans_le hs6, hp7.trans_le hs7, hpp, hpa⟩

set_option maxHeartbeats 1500000 in
theorem checker_pairScan_safe (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hN : state.heap 0 = full.length) (hq : state.heap 1 = q)
    (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val)
    (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0) (h7 : state.heap 7 = 0)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 53 * q + 7, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have hregs : ∀ count ≤ q, RegistersBound full.length q (natRun (rawIncidenceROM q full) checker (53 * count) state) := by
    intro count
    induction count with
    | zero => intro _; exact hr
    | succ count ih =>
      intro hc
      have hcount : count < q := by omega
      have hb := checker_pairScan_boundary q full left right state hpc hactive hN hq hl hj h4 h5 h6 h7 count hcount.le
      have hp := checker_pairIteration_safe q full left right ⟨count, hcount⟩
        (natRun (rawIncidenceROM q full) checker (53 * count) state)
        hb.pc hb.active hb.tools hb.left hb.right hb.counter hb.intersection hb.leftOnly hb.rightOnly
        (ih hcount.le) 53 le_rfl
      rw [Nat.mul_succ, natRun_add]
      exact hp.1
  intro count hc
  let whole := count / 53
  let rest := count % 53
  have hsplit : count = 53 * whole + rest := (Nat.div_add_mod count 53).symm
  have hrest : rest < 53 := Nat.mod_lt count (by decide)
  have hwhole : whole ≤ q := by omega
  have hb := checker_pairScan_boundary q full left right state hpc hactive hN hq hl hj h4 h5 h6 h7 whole hwhole
  rw [hsplit, natRun_add]
  by_cases hlt : whole < q
  · exact checker_pairIteration_safe q full left right ⟨whole, hlt⟩
      (natRun (rawIncidenceROM q full) checker (53 * whole) state)
      hb.pc hb.active hb.tools hb.left hb.right hb.counter hb.intersection hb.leftOnly hb.rightOnly
      (hregs whole hwhole) rest (by omega)
  · have hweq : whole = q := by omega
    have hrest7 : rest ≤ 7 := by omega
    apply checker_bitTest_safe q full _ hb.pc hb.active (hregs whole hwhole) ?_ ?_ rest hrest7
    · rw [hb.tools]
      dsimp [registerBound]
      omega
    · rw [hb.counter, hweq]
      dsimp [registerBound]
      omega

theorem natRun_halted_of_halted (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (hh : state.halted = true) (count : Nat) : (natRun rom program count state).halted = true := by
  induction count with
  | zero => exact hh
  | succ count ih => simpa only [natRun, natStep, hh, ite_true] using ih

theorem natRun_active_of_later_active (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (total : Nat) (hactive : (natRun rom program total state).halted = false) (count : Nat) (hc : count ≤ total) :
    (natRun rom program count state).halted = false := by
  cases hh : (natRun rom program count state).halted with
  | false => rfl
  | true =>
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hc
    have hf := natRun_halted_of_halted rom program (natRun rom program count state) hh extra
    rw [← natRun_add, ← heq, hactive] at hf
    cases hf

theorem natRun_decode_some_of_later_active (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (total : Nat) (hactive : (natRun rom program total state).halted = false) (count : Nat) (hc : count < total) :
    ∃ op, PackingOp.decode (natFetch program (natRun rom program count state).pc) = some op := by
  cases hd : PackingOp.decode (natFetch program (natRun rom program count state).pc) with
  | some op => exact ⟨op, rfl⟩
  | none =>
    have ha := natRun_active_of_later_active rom program state total hactive count hc.le
    have hn : (natRun rom program (count + 1) state).halted = true := by
      rw [natRun_succ]
      simp only [natStep, ha, Bool.false_eq_true, ite_false, hd]
    have hf := natRun_active_of_later_active rom program state total hactive (count + 1) (by omega)
    rw [hn] at hf
    cases hf

theorem checker_pairScan_fetch (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hq : state.heap 1 = q) (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val)
    (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0) (h7 : state.heap 7 = 0)
    (count : Nat) (hc : count ≤ 53 * q + 7) :
    (natRun (rawIncidenceROM q full) checker count state).halted = false ∧
      ∃ op, PackingOp.decode (natFetch checker (natRun (rawIncidenceROM q full) checker count state).pc) = some op := by
  rcases natRun_checker_pairScan_raw q full left right state hpc hactive hq hl hj h4 h5 h6 h7 with
    ⟨_, _, _, _, _, _, hfinalPc, hfinalActive⟩
  refine ⟨natRun_active_of_later_active _ _ _ _ hfinalActive count hc, ?_⟩
  by_cases hlt : count < 53 * q + 7
  · exact natRun_decode_some_of_later_active _ _ _ _ hfinalActive count hlt
  · have heq : count = 53 * q + 7 := by omega
    rw [heq, hfinalPc]
    have hi : 92 < checker.length := by rw [checker_length]; decide
    rw [show 460 = 5 * 92 from rfl, natFetch_body checker 92 hi, decode_encode]
    exact ⟨_, rfl⟩

theorem checker_pairScan_numeric_access (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hN : state.heap 0 = full.length) (hq : state.heap 1 = q)
    (hl : state.heap 2 = left.val) (hj : state.heap 3 = right.val)
    (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0) (h7 : state.heap 7 = 0)
    (hr : RegistersBound full.length q state) (count : Nat) (hc : count ≤ 53 * q + 7) :
    let result := natRun (rawIncidenceROM q full) checker count state
    RegistersBound full.length q result ∧ result.pc ≤ 630 ∧ result.halted = false ∧
      ∃ op, PackingOp.decode (natFetch checker result.pc) = some op ∧ NatAccessFits (rawIncidenceROM q full) 8 result op := by
  have hs := checker_pairScan_safe q full left right state hpc hactive hN hq hl hj h4 h5 h6 h7 hr count hc
  obtain ⟨ha, op, hd⟩ := checker_pairScan_fetch q full left right state hpc hactive hq hl hj h4 h5 h6 h7 count hc
  obtain ⟨index, _, _, haccess⟩ := hs.2.2
  have he := haccess ha
  rw [hd] at he
  exact ⟨hs.1, hs.2.1, ha, op, hd, he⟩

end PaperProofs.Structure.LaminarTree.RawIncidenceScanSafety
