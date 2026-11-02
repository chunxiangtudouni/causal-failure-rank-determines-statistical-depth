module

public import Structure.PSTR_BuildLower_LoopControl_012

/-! Direct actual Word countdown execution. Only the counter is interpreted as
a Nat. The embedded body may use the original modular BitVec arithmetic. Its
contract is restricted to the compiler's internal valid states, not arbitrary
heaps and not an extra original-caller qualification. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.WordLoop

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035a

variable {bits : Nat}

theorem head_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (ha : state.halted = false) :
    packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right) 5 state =
      executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state := by
  let lead := (relativeLoopHead counter (5 * (left.length + body.length + 14))).take 4
  have hlen : lead.length = 4 := rfl
  have hlb := relativeLoopBlock_length counter left.length body
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .value .fresh) left.length
    (by simp only [List.length_append, hlen, hlb]; omega) ?_ ?_ ?_ hcode hpcfit state hpc ha
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index left (relativeLoopHead counter (5 * (left.length + body.length + 14)))
      (body ++ relativeLoopTail counter (5 * left.length) ++ right) position (by change position < 5; omega)
    simpa only [relativeLoopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index left (relativeLoopHead counter (5 * (left.length + body.length + 14)))
      (body ++ relativeLoopTail counter (5 * left.length) ++ right) 4 (by change 4 < 5; decide)
    have hj : (relativeLoopHead counter (5 * (left.length + body.length + 14)))[4]'(by
        rw [relativeLoopHead_length]; omega) = PackingOp.jumpIfZero .value .fresh := rfl
    rw [hj] at hh
    simpa only [relativeLoopBlock, List.append_assoc, hlen] using hh
  · simp [lead, relativeLoopHead, relativeRead, StraightProgram, StraightOp]

theorem tail_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)))
    (ha : state.halted = false) :
    packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right) 9 state =
      executeOps rom (relativeLoopTail counter (5 * left.length)) state := by
  let lead := (relativeLoopTail counter (5 * left.length)).take 8
  have hlen : lead.length = 8 := rfl
  have hlb := relativeLoopBlock_length counter left.length body
  have hhead : (relativeLoopHead counter (5 * (left.length + body.length + 14))).length = 5 := rfl
  have hpref : (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body).length =
      left.length + 5 + body.length := by simp only [List.length_append, hhead]
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .flag .fresh)
    (left.length + 5 + body.length) (by simp only [List.length_append, hlen, hlb]; omega)
    ?_ ?_ ?_ hcode hpcfit state hpc ha
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body)
      (relativeLoopTail counter (5 * left.length)) right position (by change position < 9; omega)
    simp only [hpref] at hh
    simpa only [relativeLoopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index (left ++ relativeLoopHead counter (5 * (left.length + body.length + 14)) ++ body)
      (relativeLoopTail counter (5 * left.length)) right 8 (by change 8 < 9; decide)
    simp only [hpref] at hh
    have hj : (relativeLoopTail counter (5 * left.length))[8]'(by
        rw [relativeLoopTail_length]; omega) = PackingOp.jumpIfZero .flag .fresh := rfl
    rw [hj] at hh
    simpa only [relativeLoopBlock, List.append_assoc, hlen] using hh
  · simp [lead, relativeLoopTail, relativeRead, StraightProgram, StraightOp]

/-- One actual embedded-body run from a valid loop entry. The final conjunct
is the compiler's internal invariant after the actual tail, allowing source
counter/environment changes. Nothing is required of invalid input heaps. -/
def BodyExits (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat) : Prop :=
  ∀ state, valid state → state.pc = BitVec.ofNat bits (5 * left.length) → state.halted = false →
    (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0 →
    let tested := executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state
    let done := packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right) (bodySteps tested) tested
    done.pc = BitVec.ofNat bits (5 * (left.length + 5 + body.length)) ∧ done.halted = false ∧
      done.register .address = state.register .address ∧
      done.heap (state.register .address + BitVec.ofNat bits counter) =
        state.heap (state.register .address + BitVec.ofNat bits counter) ∧
      valid (executeOps rom (relativeLoopTail counter (5 * left.length)) done)

def cycleResult (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : WordState bits → Nat) (state : WordState bits) : WordState bits :=
  let tested := executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state
  executeOps rom (relativeLoopTail counter (5 * left.length))
    (packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right) (bodySteps tested) tested)

def cycleSteps (rom : PhysicalROM) (left body : List PackingOp) (counter : Nat)
    (bodySteps : WordState bits → Nat) (state : WordState bits) : Nat :=
  5 + bodySteps (executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state) + 9

private theorem tested_pc (rom : PhysicalROM) (left body : List PackingOp) (counter : Nat)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0) :
    (executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state).pc =
      BitVec.ofNat bits (5 * (left.length + 5)) := by
  rw [relativeLoopHead_word_pc, ite_eq_right hc, hpc, BitVec.ofNat_add_ofNat]
  congr 1

theorem cycle_run (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat)
    (hb : BodyExits valid rom left body right counter bodySteps)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (state : WordState bits) (hv : valid state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0) :
    packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right)
      (cycleSteps rom left body counter bodySteps state) state =
        cycleResult rom left body right counter bodySteps state := by
  have hd := hb state hv hpc ha hc
  dsimp only [cycleSteps]
  rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add,
    head_run rom left body right counter hcode hpcfit state hpc ha,
    tail_run rom left body right counter hcode hpcfit _ hd.1 hd.2.1]
  rfl

theorem cycle_control (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat)
    (hb : BodyExits valid rom left body right counter bodySteps)
    (state : WordState bits) (hv : valid state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0) :
    let done := cycleResult rom left body right counter bodySteps state
    done.pc = BitVec.ofNat bits (5 * left.length) ∧ done.halted = false ∧
      done.register .address = state.register .address ∧
      (done.heap (done.register .address + BitVec.ofNat bits counter)).toNat =
        (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat - 1 ∧ valid done := by
  have hd := hb state hv hpc ha hc
  have hcfit := (state.heap (state.register .address + BitVec.ofNat bits counter)).isLt
  have h1 : 1 < 2 ^ bits := lt_of_le_of_lt (by omega) hcfit
  have hone : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt h1
  have hsub : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat - 1 < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt hcfit
  dsimp only [cycleResult]
  refine ⟨relativeLoopTail_word_pc _ _ _ _, (executeOps_halted rom _ _).trans hd.2.1,
    (relativeLoopTail_word_base _ _ _ _).trans hd.2.2.1, ?_, hd.2.2.2.2⟩
  rw [relativeLoopTail_word_base, relativeLoopTail_word_heap, Function.update_self,
    hd.2.2.1, hd.2.2.2.1, hone, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub]

def loopResult (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : WordState bits → Nat) : Nat → WordState bits → WordState bits
  | 0, state => executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state
  | count + 1, state => loopResult rom left body right counter bodySteps count
      (cycleResult rom left body right counter bodySteps state)

def loopSteps (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : WordState bits → Nat) : Nat → WordState bits → Nat
  | 0, _ => 5
  | count + 1, state => cycleSteps rom left body counter bodySteps state +
      loopSteps rom left body right counter bodySteps count (cycleResult rom left body right counter bodySteps state)

theorem loop_run (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat)
    (hb : BodyExits valid rom left body right counter bodySteps)
    (hcode : WordsFit bits (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits bits (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length))
    (count : Nat) (state : WordState bits) (hv : valid state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat = count) :
    packingRun rom (left ++ relativeLoopBlock counter left.length body ++ right)
      (loopSteps rom left body right counter bodySteps count state) state =
        loopResult rom left body right counter bodySteps count state := by
  induction count generalizing state with
  | zero => exact head_run rom left body right counter hcode hpcfit state hpc ha
  | succ count ih =>
    have hn : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0 := by omega
    have ht := cycle_control valid rom left body right counter bodySteps hb state hv hpc ha hn
    rw [loopSteps, PSTRWordSegments.run_add,
      cycle_run valid rom left body right counter bodySteps hb hcode hpcfit state hv hpc ha hn]
    exact ih _ ht.2.2.2.2 ht.1 ht.2.1 (by rw [ht.2.2.2.1, hc]; omega)

theorem loopSteps_le (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat)
    (hb : BodyExits valid rom left body right counter bodySteps) (bodyBound : Nat)
    (hbound : ∀ state, valid state → state.pc = BitVec.ofNat bits (5 * left.length) → state.halted = false →
      (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0 →
      bodySteps (executeOps rom (relativeLoopHead counter (5 * (left.length + body.length + 14))) state) ≤ bodyBound)
    (count : Nat) (state : WordState bits) (hv : valid state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat = count) :
    loopSteps rom left body right counter bodySteps count state ≤ count * (bodyBound + 14) + 5 := by
  induction count generalizing state with
  | zero => simp only [loopSteps, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ count ih =>
    have hn : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0 := by omega
    have ht := cycle_control valid rom left body right counter bodySteps hb state hv hpc ha hn
    have hh := hbound state hv hpc ha hn
    have hi := ih _ ht.2.2.2.2 ht.1 ht.2.1 (by rw [ht.2.2.2.1, hc]; omega)
    rw [loopSteps]
    dsimp only [cycleSteps]
    nlinarith

theorem loop_control (valid : WordState bits → Prop) (rom : PhysicalROM)
    (left body right : List PackingOp) (counter : Nat) (bodySteps : WordState bits → Nat)
    (hb : BodyExits valid rom left body right counter bodySteps)
    (count : Nat) (state : WordState bits) (hv : valid state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat = count) :
    let done := loopResult rom left body right counter bodySteps count state
    done.pc = BitVec.ofNat bits (5 * (left.length + body.length + 14)) ∧ done.halted = false ∧
      done.register .address = state.register .address ∧
      (done.heap (done.register .address + BitVec.ofNat bits counter)).toNat = 0 := by
  induction count generalizing state with
  | zero =>
    dsimp only [loopResult]
    refine ⟨?_, (executeOps_halted rom _ state).trans ha,
      relativeLoopHead_word_base _ _ _ _, ?_⟩
    · rw [relativeLoopHead_word_pc, ite_eq_left hc]
    · rw [relativeLoopHead_word_base, relativeLoopHead_word_heap, hc]
  | succ count ih =>
    have hn : (state.heap (state.register .address + BitVec.ofNat bits counter)).toNat ≠ 0 := by omega
    have ht := cycle_control valid rom left body right counter bodySteps hb state hv hpc ha hn
    have hi := ih _ ht.2.2.2.2 ht.1 ht.2.1 (by rw [ht.2.2.2.1, hc]; omega)
    exact ⟨hi.1, hi.2.1, hi.2.2.1.trans ht.2.2.1, hi.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.WordLoop
