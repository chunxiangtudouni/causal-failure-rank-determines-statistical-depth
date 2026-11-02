module

public import PaperProofs.Structure.PA17_UniformGenerator_035aa

/-! Whole forward-copy prefix safety. The copy may overwrite cursor and
all low scratch words: after initialization only hardware controls are used. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ab

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035g PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035aa

theorem copy_loop_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp) (cursor source length : Nat)
    (original : Nat → Nat) (hwords : ∀ position < length, original (source + position) ≤ B)
    (hsourceB : source + length ≤ B) (hsourceH : source + length ≤ heapWords)
    (hpcB : 5 * (left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right).length ≤ B)
    (remaining index : Nat) (state : NatState) (hsum : index + remaining = length)
    (hpc : state.pc = 5 * (left.length + 6)) (ha : state.halted = false) (hr : RegistersLE B state)
    (hi : CopyInv source original index remaining state) :
    RunSafe B heapWords rom (left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right) (9 * remaining + 2) state := by
  induction remaining generalizing index state with
  | zero =>
    have hp : (left ++ copyInit cursor source).length = left.length + 6 := by simp [copyInit]
    have hh := copyHead_safe rom B heapWords (left.length + 15) (left ++ copyInit cursor source)
      (copyTail (5 * (left.length + 6)) ++ right)
      (by simp only [List.length_append, PA17UniformGenerator035g.copyBlock_length] at hpcB; omega)
      (by
        have hhead : (copyHead (5 * (left.length + 15))).length = 2 := rfl
        have htail : (copyTail (5 * (left.length + 6))).length = 7 := rfl
        simp only [List.length_append, hp, hhead, htail]
        omega)
      state (by rw [hp]; exact hpc) ha hr
    simpa only [Nat.mul_zero, Nat.zero_add, PA17UniformGenerator035g.copyBlock, List.append_assoc] using hh
  | succ remaining ih =>
    let allCode := left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right
    let tested := runOps rom (copyHead (5 * (left.length + 15))) state
    have hshead : RunSafe B heapWords rom allCode 2 state := by
      have hp : (left ++ copyInit cursor source).length = left.length + 6 := by simp [copyInit]
      have hh := copyHead_safe rom B heapWords (left.length + 15) (left ++ copyInit cursor source)
        (copyTail (5 * (left.length + 6)) ++ right)
        (by simp only [List.length_append, PA17UniformGenerator035g.copyBlock_length] at hpcB; omega)
        (by
          have hhead : (copyHead (5 * (left.length + 15))).length = 2 := rfl
          have htail : (copyTail (5 * (left.length + 6))).length = 7 := rfl
          simp only [List.length_append, hp, hhead, htail]
          omega)
        state (by rw [hp]; exact hpc) ha hr
      simpa only [allCode, PA17UniformGenerator035g.copyBlock, List.append_assoc] using hh
    have hheadRun : natRun rom allCode 2 state = tested := copy_head_run rom left right cursor source state hpc ha
    have ht := head_inv rom (5 * (left.length + 15)) source index (remaining + 1) original state hi
    have htpc : tested.pc = 5 * (left.length + 8) := by
      rw [copy_head_pc, hi.2.2.1, ite_eq_right (by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
    have htreg : RegistersLE B tested := by
      have hh := (hshead.final _ _ _ _ _).1
      rw [hheadRun] at hh
      exact hh
    have hstail : RunSafe B heapWords rom allCode 7 tested := by
      let lead := left ++ copyInit cursor source ++ copyHead (5 * (left.length + 15))
      have hp : lead.length = left.length + 8 := by simp [lead, copyInit, copyHead]
      have hh := copyTail_safe rom B heapWords (left.length + 6) lead right
        (by simp only [List.length_append, PA17UniformGenerator035g.copyBlock_length] at hpcB; omega)
        (by simp only [List.length_append, hp]; change left.length + 6 ≤ left.length + 8 + 7 + right.length; omega)
        tested (by rw [hp]; exact htpc) hta htreg ht.2.2.2.2.1
        (by rw [ht.2.1, ht.2.2.2.2.2, copyHeap_source]; exact hwords index (by omega))
        (by rw [ht.2.1]; omega) (by rw [ht.1]; omega)
        (by rw [ht.2.1, ht.2.2.2.1]; omega) (by rw [ht.1, ht.2.2.2.1]; omega)
      simpa only [allCode, PA17UniformGenerator035g.copyBlock, lead, List.append_assoc] using hh
    let moved := runOps rom (copyTail (5 * (left.length + 6))) tested
    have htailRun : natRun rom allCode 7 tested = moved := copy_tail_run rom left right cursor source tested htpc hta
    have hm : CopyInv source original (index + 1) remaining moved := by
      simpa only [Nat.add_sub_cancel] using tail_inv rom (5 * (left.length + 6)) source index (remaining + 1) original tested ht
    have hmpc : moved.pc = 5 * (left.length + 6) := copy_tail_pc rom _ tested ht.2.2.2.2.1
    have hma : moved.halted = false := (runOps_halted rom _ tested).trans hta
    have hmreg : RegistersLE B moved := by
      have hh := (hstail.final _ _ _ _ _).1
      rw [htailRun] at hh
      exact hh
    have hremaining := ih (index + 1) moved (by omega) hmpc hma hmreg hm
    have hcycleRun : natRun rom allCode (2 + 7) state = moved := by rw [natRun_add, hheadRun, htailRun]
    have hfirst := RunSafe.add _ _ _ allCode 2 7 state hshead (by rw [hheadRun]; exact hstail)
    have hall := RunSafe.add _ _ _ allCode (2 + 7) (9 * remaining + 2) state hfirst (by rw [hcycleRun]; exact hremaining)
    have htime : 9 * (remaining + 1) + 2 = (2 + 7) + (9 * remaining + 2) := by omega
    rw [htime]
    exact hall

theorem copy_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp) (cursor source : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hcursor : cursor ≤ B) (hcursorH : cursor < heapWords) (hone : 1 ≤ B)
    (hsourceB : source + state.heap cursor ≤ B) (hsourceH : source + state.heap cursor ≤ heapWords)
    (hwords : ∀ position < state.heap cursor, state.heap (source + position) ≤ B)
    (hpcB : 5 * (left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right).length ≤ B) :
    RunSafe B heapWords rom (left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right) (9 * state.heap cursor + 8) state := by
  let allCode := left ++ PA17UniformGenerator035g.copyBlock cursor source left.length ++ right
  let prepared := runOps rom (copyInit cursor source) state
  have hinit := copyInit_numeric rom B heapWords cursor source hcursor hcursorH (by omega) hone state hr (by omega)
  have hinitSafe : RunSafe B heapWords rom allCode 6 state := by
    have hlen : (copyInit cursor source).length = 6 := rfl
    have hh := straight_segment_safe rom B heapWords left (copyInit cursor source)
      (copyHead (5 * (left.length + 15)) ++ copyTail (5 * (left.length + 6)) ++ right)
      (by simp [copyInit, NoJump]) state hpc ha hinit
    simpa only [allCode, PA17UniformGenerator035g.copyBlock, hlen, List.append_assoc] using hh
  have hinitRun : natRun rom allCode 6 state = prepared := init_run rom left right cursor source state hpc ha
  have hp : prepared.pc = 5 * (left.length + 6) := by
    rw [runOps_pc rom _ state (by simp [copyInit, NoJump]), hpc]
    rfl
  have hreg : RegistersLE B prepared := by
    have hh := (hinitSafe.final _ _ _ _ _).1
    rw [hinitRun] at hh
    exact hh
  have hlater := copy_loop_safe rom B heapWords left right cursor source (state.heap cursor) state.heap hwords hsourceB hsourceH
    hpcB (state.heap cursor) 0 prepared (by omega) hp ((runOps_halted rom _ state).trans ha) hreg (init_inv rom cursor source state)
  have htime : 9 * state.heap cursor + 8 = 6 + (9 * state.heap cursor + 2) := by omega
  rw [htime]
  exact RunSafe.add _ _ _ _ _ _ state hinitSafe (by rw [hinitRun]; exact hlater)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ab
