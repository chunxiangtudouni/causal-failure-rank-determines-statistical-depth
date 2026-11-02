module

public import PaperProofs.Structure.PA17_UniformGenerator_035c

/-! The real final forward copy uses only hardware registers after loading
its length. It remains correct when destination0 overwrites all low heap
scratch words, including the old cursor and counters. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035g

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035c

def copyInit (cursor source : Nat) : List PackingOp :=
  [.base (.base (.constant .index cursor)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index 0)), .base (.base (.constant .address source)),
   .base (.base (.constant .fresh 1)), .base (.base (.constant .flag 0))]

def copyHead (exit : Nat) : List PackingOp :=
  [.base (.base (.constant .old exit)), .jumpIfZero .total .old]

def copyTail (entry : Nat) : List PackingOp :=
  [.base (.base (.loadHeap .value .address)), .base (.base (.storeHeap .index .value)),
   .base (.base (.add .address .address .fresh)), .base (.base (.add .index .index .fresh)),
   .base (.subtract .total .total .fresh), .base (.base (.constant .old entry)), .jumpIfZero .flag .old]

def copyBlock (cursor source start : Nat) : List PackingOp :=
  copyInit cursor source ++ copyHead (5 * (start + 15)) ++ copyTail (5 * (start + 6))

theorem copyBlock_length (cursor source start : Nat) : (copyBlock cursor source start).length = 15 := rfl

theorem branch_segment_run (rom : PhysicalROM) (left lead right : List PackingOp) (last : PackingOp)
    (hl : ∀ op ∈ lead, NoJump op) (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ (lead ++ [last]) ++ right) (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  have hrun := natRun_of_segment_last rom (left ++ (lead ++ [last]) ++ right) lead last left.length
    (by simp only [List.length_append, List.length_singleton]; omega) ?_ ?_ hl state hpc ha
  · simpa only [runOps_append, runOps] using hrun
  · intro position hp
    have hh := segment_index left (lead ++ [last]) right position (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_left hp] using hh
  · have hh := segment_index left (lead ++ [last]) right lead.length (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] using hh

theorem init_run (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ copyBlock cursor source left.length ++ right) 6 state = runOps rom (copyInit cursor source) state := by
  have hlen : (copyInit cursor source).length = 6 := rfl
  have hh := natRun_of_straight_segment rom
    (left ++ copyInit cursor source ++ (copyHead (5 * (left.length + 15)) ++ copyTail (5 * (left.length + 6)) ++ right))
    (copyInit cursor source) left.length (by simp only [List.length_append]; omega)
    (segment_index left (copyInit cursor source) _) (by simp [copyInit, NoJump]) state hpc ha
  simpa only [copyBlock, List.append_assoc, hlen] using hh

theorem copy_head_run (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * (left.length + 6)) (ha : state.halted = false) :
    natRun rom (left ++ copyBlock cursor source left.length ++ right) 2 state =
      runOps rom (copyHead (5 * (left.length + 15))) state := by
  have hp : (left ++ copyInit cursor source).length = left.length + 6 := by simp [copyInit]
  have hh := branch_segment_run rom (left ++ copyInit cursor source)
    [.base (.base (.constant .old (5 * (left.length + 15))))]
    (copyTail (5 * (left.length + 6)) ++ right) (.jumpIfZero .total .old)
    (by simp [NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [copyBlock, copyHead, List.append_assoc, List.length_singleton, List.singleton_append] using hh

theorem copy_tail_run (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * (left.length + 8)) (ha : state.halted = false) :
    natRun rom (left ++ copyBlock cursor source left.length ++ right) 7 state =
      runOps rom (copyTail (5 * (left.length + 6))) state := by
  let lead := (copyTail (5 * (left.length + 6))).take 6
  have hp : (left ++ copyInit cursor source ++ copyHead (5 * (left.length + 15))).length = left.length + 8 := by
    simp [copyInit, copyHead]
  have hh := branch_segment_run rom (left ++ copyInit cursor source ++ copyHead (5 * (left.length + 15)))
    lead right (.jumpIfZero .flag .old) (by simp [lead, copyTail, NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [copyBlock, copyTail, lead, List.take_succ_cons, List.take_zero, List.append_assoc,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil] using hh

def copyHeap (original : Nat → Nat) (source count : Nat) : Nat → Nat :=
  fun address => if address < count then original (source + address) else original address

theorem copyHeap_source (original : Nat → Nat) (source count : Nat) :
    copyHeap original source count (source + count) = original (source + count) := by
  rw [copyHeap, ite_eq_right (by omega)]

theorem copyHeap_update (original : Nat → Nat) (source count : Nat) :
    Function.update (copyHeap original source count) count (original (source + count)) = copyHeap original source (count + 1) := by
  funext address
  by_cases he : address = count
  · subst address
    simp only [Function.update_self, copyHeap, Nat.lt_succ_self, ite_true]
  · rw [Function.update_of_ne he]
    have hh : address < count + 1 ↔ address < count := by omega
    simp only [copyHeap, hh]

def CopyInv (source : Nat) (original : Nat → Nat) (index remaining : Nat) (state : NatState) : Prop :=
  state.register .index = index ∧ state.register .address = source + index ∧
    state.register .total = remaining ∧ state.register .fresh = 1 ∧ state.register .flag = 0 ∧
    state.heap = copyHeap original source index

theorem init_inv (rom : PhysicalROM) (cursor source : Nat) (state : NatState) :
    CopyInv source state.heap 0 (state.heap cursor) (runOps rom (copyInit cursor source) state) := by
  refine ⟨rfl, by simp [copyInit, runOps, natExecuteOp, Op.execute, Instruction.execute], rfl, rfl, rfl, ?_⟩
  funext address
  simp [copyInit, runOps, natExecuteOp, Op.execute, Instruction.execute, copyHeap]

theorem head_inv (rom : PhysicalROM) (exit source index remaining : Nat) (original : Nat → Nat) (state : NatState)
    (hi : CopyInv source original index remaining state) :
    CopyInv source original index remaining (runOps rom (copyHead exit) state) := hi

theorem copy_head_pc (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    (runOps rom (copyHead exit) state).pc = if state.register .total = 0 then exit else state.pc + 10 := by
  simp [copyHead, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem copy_tail_pc (rom : PhysicalROM) (entry : Nat) (state : NatState) (hz : state.register .flag = 0) :
    (runOps rom (copyTail entry) state).pc = entry := by
  simp [copyTail, runOps, natExecuteOp, Op.execute, Instruction.execute, hz]

theorem tail_inv (rom : PhysicalROM) (entry source index remaining : Nat) (original : Nat → Nat) (state : NatState)
    (hi : CopyInv source original index remaining state) :
    CopyInv source original (index + 1) (remaining - 1) (runOps rom (copyTail entry) state) := by
  rcases hi with ⟨hindex, haddress, htotal, hfresh, hflag, hheap⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change state.register .index + state.register .fresh = index + 1
    rw [hindex, hfresh]
  · change state.register .address + state.register .fresh = source + (index + 1)
    rw [haddress, hfresh]
    omega
  · change state.register .total - state.register .fresh = remaining - 1
    rw [htotal, hfresh]
  · exact hfresh
  · exact hflag
  · change Function.update state.heap (state.register .index) (state.heap (state.register .address)) = _
    rw [hheap, hindex, haddress, copyHeap_source, copyHeap_update]

theorem copy_loop_run (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (original : Nat → Nat) (remaining index : Nat) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 6)) (ha : state.halted = false) (hi : CopyInv source original index remaining state) :
    let fresh := natRun rom (left ++ copyBlock cursor source left.length ++ right) (9 * remaining + 2) state
    CopyInv source original (index + remaining) 0 fresh ∧ fresh.pc = 5 * (left.length + 15) ∧ fresh.halted = false := by
  induction remaining generalizing index state with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, copy_head_run rom left right cursor source state hpc ha]
    refine ⟨?_, ?_, (runOps_halted rom _ state).trans ha⟩
    · simpa only [Nat.add_zero] using head_inv rom (5 * (left.length + 15)) source index 0 original state hi
    · rw [copy_head_pc, hi.2.2.1, ite_eq_left rfl]
  | succ remaining ih =>
    let tested := runOps rom (copyHead (5 * (left.length + 15))) state
    have htest := head_inv rom (5 * (left.length + 15)) source index (remaining + 1) original state hi
    have htpc : tested.pc = 5 * (left.length + 8) := by
      rw [copy_head_pc, hi.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
    let moved := runOps rom (copyTail (5 * (left.length + 6))) tested
    have hm : CopyInv source original (index + 1) remaining moved := by
      simpa only [Nat.add_sub_cancel] using tail_inv rom (5 * (left.length + 6)) source index (remaining + 1) original tested htest
    have hmpc : moved.pc = 5 * (left.length + 6) := copy_tail_pc rom _ tested htest.2.2.2.2.1
    have hma : moved.halted = false := (runOps_halted rom _ tested).trans hta
    have hr := ih (index + 1) moved hmpc hma hm
    have htime : 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) := by omega
    have hcycle : natRun rom (left ++ copyBlock cursor source left.length ++ right) (2 + 7) state = moved := by
      rw [natRun_add, copy_head_run rom left right cursor source state hpc ha,
        copy_tail_run rom left right cursor source tested htpc hta]
    rw [htime, natRun_add, hcycle]
    have hindex : index + (remaining + 1) = index + 1 + remaining := by omega
    rw [hindex]
    exact hr

theorem copy_run (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun rom (left ++ copyBlock cursor source left.length ++ right) (9 * state.heap cursor + 8) state
    CopyInv source state.heap (state.heap cursor) 0 fresh ∧ fresh.pc = 5 * (left.length + 15) ∧ fresh.halted = false := by
  let prepared := runOps rom (copyInit cursor source) state
  have hp : prepared.pc = 5 * (left.length + 6) := by
    rw [runOps_pc rom _ state (by simp [copyInit, NoJump]), hpc]
    rfl
  have hh := copy_loop_run rom left right cursor source state.heap (state.heap cursor) 0 prepared hp
    ((runOps_halted rom _ state).trans ha) (init_inv rom cursor source state)
  have htime : 9 * state.heap cursor + 8 = 6 + (9 * state.heap cursor + 2) := by omega
  rw [htime, natRun_add, init_run rom left right cursor source state hpc ha]
  simpa only [Nat.zero_add] using hh

theorem copy_stream (rom : PhysicalROM) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (words : List Nat) (hs : StreamRep cursor source words state.heap) :
    ∀ position (hp : position < words.length),
      (natRun rom (left ++ copyBlock cursor source left.length ++ right) (9 * words.length + 8) state).heap position = words[position] := by
  intro position hp
  have hh := copy_run rom left right cursor source state hpc ha
  rw [hs.1] at hh
  rw [hh.1.2.2.2.2.2, copyHeap, ite_eq_left hp]
  exact hs.2 position hp

theorem copy_halts (rom : PhysicalROM) (left : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ copyBlock cursor source left.length) (9 * state.heap cursor + 9) state =
      { natRun rom (left ++ copyBlock cursor source left.length) (9 * state.heap cursor + 8) state with halted := true } := by
  have hh := copy_run rom left [] cursor source state hpc ha
  simp only [List.append_nil] at hh
  have hlen : (left ++ copyBlock cursor source left.length).length = left.length + 15 := by
    rw [List.length_append, copyBlock_length]
  have htime : 9 * state.heap cursor + 9 = (9 * state.heap cursor + 8) + 1 := by omega
  rw [htime, natRun_succ]
  exact natStep_halt rom _ _ (hh.2.1.trans (congrArg (5 * ·) hlen.symm)) hh.2.2

theorem copy_word_stream (rom : PhysicalROM) (left : List PackingOp) (cursor source bits : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (words : List Nat) (hs : StreamRep cursor source words state.heap)
    (hcode : WordsFit bits (packingCode (left ++ copyBlock cursor source left.length)))
    (hsafe : ∀ count < 9 * words.length + 9,
      RegistersFit bits (natRun rom (left ++ copyBlock cursor source left.length) count state) ∧
        Fits bits (natRun rom (left ++ copyBlock cursor source left.length) count state).pc)
    (hwords : WordsFit bits words) (hlen : Fits bits words.length) :
    let fresh := packingRun rom (left ++ copyBlock cursor source left.length) (9 * words.length + 9) (state.toWord bits)
    fresh.halted = true ∧ ∀ position (hp : position < words.length),
      (fresh.heap (BitVec.ofNat bits position)).toNat = words[position] := by
  rw [natRun_toWord _ _ _ _ hcode hsafe]
  have halt := copy_halts rom left cursor source state hpc ha
  rw [hs.1] at halt
  rw [halt]
  refine ⟨rfl, ?_⟩
  intro position hp
  have hpfit : Fits bits position := lt_of_lt_of_le hp hlen.le
  change (BitVec.ofNat bits ((natRun rom (left ++ copyBlock cursor source left.length)
    (9 * words.length + 8) state).heap (BitVec.ofNat bits position).toNat)).toNat = _
  have hpnat : (BitVec.ofNat bits position).toNat = position := Nat.mod_eq_of_lt hpfit
  rw [hpnat]
  have hv := copy_stream rom left [] cursor source state hpc ha words hs position hp
  simp only [List.append_nil] at hv
  rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hwords _ (List.getElem_mem hp))]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035g
