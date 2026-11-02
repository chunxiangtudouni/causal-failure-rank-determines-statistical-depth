module

public import Structure.PA06_A19Prepare_CompactArrays018
public import PaperProofs.Structure.RawCandidateOrderingWord

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual short scalar pieces of the fixed303-op count sorter, at B16,
full width32, and008 linearLimit.018 provides the true array macros and014
provides real workspace scalar macros. The Nat sorter/chunk code is reused;
no old-width caller bounds or huge workspace allocation is accepted. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Macros

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM RawIncidenceScanSafety

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

def MacroSafe (q : Nat) (full : List (Finset (Fin q))) (code : List PackingOp) (state : NatState) : Prop :=
  (∀ count ≤ code.length, RegistersFit (indexWidth 32 full.length q)
    (runOps (rawIncidenceROM q full) (code.take count) state)) ∧
  ∀ count < code.length, NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
    (runOps (rawIncidenceROM q full) (code.take count) state) (code.getD count paddingOp)

theorem MacroSafe.full {q : Nat} {full : List (Finset (Fin q))} {code : List PackingOp} {state : NatState}
    (h : MacroSafe q full code state) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) code state) := by
  have hh := h.1 code.length le_rfl
  rwa [List.take_length] at hh

theorem MacroSafe.append {q : Nat} {full : List (Finset (Fin q))} {first second : List PackingOp} {state : NatState}
    (hfirst : MacroSafe q full first state)
    (hsecond : MacroSafe q full second (runOps (rawIncidenceROM q full) first state)) :
    MacroSafe q full (first ++ second) state := by
  constructor
  · intro count hc
    by_cases hsmall : count ≤ first.length
    · rw [List.take_append_of_le_length hsmall]
      exact hfirst.1 count hsmall
    · rw [List.take_append, List.take_of_length_le (by omega), runOps_append]
      apply hsecond.1
      simp only [List.length_append] at hc
      omega
  · intro count hc
    by_cases hsmall : count < first.length
    · rw [List.take_append_of_le_length hsmall.le, List.getD_append _ _ _ _ hsmall]
      exact hfirst.2 count hsmall
    · rw [List.take_append, List.take_of_length_le (by omega), runOps_append,
        List.getD_append_right _ _ _ _ (by omega)]
      apply hsecond.2
      simp only [List.length_append] at hc
      omega

theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

theorem scalar_fits (N q value : Nat) (hv : value ≤ 4 * (N + q + 1) + 32) :
    Fits (indexWidth 32 N q) value := by
  have hlim : Fits (indexWidth 32 N q) (linearLimit N q) := PA06A19PrepareCompactArrays018.linearLimit_fits N q
  apply lt_of_le_of_lt _ hlim
  unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
  omega

theorem loadCell_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (cell : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hread : Fits (indexWidth 32 full.length q) (state.heap cell)) : MacroSafe q full (loadCell target cell) state := by
  have hfit := scalar_fits full.length q cell (by omega)
  have hlim : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 2 := hc
    interval_cases count
    · exact hf
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
    · change ∀ reg, Fits _ (Function.update (Function.update state.register .address cell) target (state.heap cell) reg)
      exact fits_update (fits_update hf .address cell hfit) target _ hread
  · intro count hc
    have hc' : count < 2 := hc
    interval_cases count <;>
      simp [loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hlim]

theorem storeCell_safe (q : Nat) (full : List (Finset (Fin q))) (source : Register) (cell : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state) :
    MacroSafe q full (storeCell source cell) state := by
  have hfit := scalar_fits full.length q cell (by omega)
  have hlim : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 2 := hc
    interval_cases count
    · exact hf
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
  · intro count hc
    have hc' : count < 2 := hc
    interval_cases count <;>
      simp [storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hlim]

theorem compareCards_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hleft : state.heap 1 ≤ q) (hright : state.heap 2 ≤ q) : MacroSafe q full compareCards state := by
  have hsmall (value : Nat) (hv : value ≤ 2 * q + 8) : Fits (indexWidth 32 full.length q) value :=
    scalar_fits full.length q value (by omega)
  have hlim (cell : Nat) (hc : cell ≤ 8) : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 15 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 15 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [compareCards_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (compareCards[count]'(by rw [compareCards_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [compareCards, loadCell, storeCell, List.getElem_append, List.getElem_cons_zero,
          List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals apply hsmall
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals omega
  · intro count hc
    have hc' : count < 15 := hc
    interval_cases count <;>
      simp [compareCards, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, hlim]

theorem compareIDs_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hj : state.heap (16 + 2) ≤ (full.length + q + 1))
    (hrank : state.heap (16 + 3) ≤ (full.length + q + 1))
    (h3 : state.heap 3 ≤ 1) (h4 : state.heap 4 ≤ 1) (h5 : state.heap 5 ≤ 1)
    (hvalue : state.register .value = 1) : MacroSafe q full compareIDs state := by
  have hlim : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hmin : min 1 (state.heap (16 + 1) - state.heap (16 + 2)) ≤ 1 := Nat.min_le_left _ _
  have hmul := Nat.mul_le_mul hmin h4
  have hsum : min 1 (state.heap (16 + 1) - state.heap (16 + 2)) *
      state.heap 4 + state.heap 5 ≤ 2 := by omega
  have hmul2 := Nat.mul_le_mul hsum h3
  rw [Nat.min_comm] at hmul hsum hmul2
  constructor
  · intro count hc
    have hc' : count ≤ 32 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 32 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [compareIDs_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (compareIDs[count]'(by rw [compareIDs_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [compareIDs, loadWorkspace, storeWorkspace, loadCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute, natArithmetic]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
      all_goals omega
  · intro count hc
    have hc' : count < 32 := hc
    interval_cases count <;>
      simp [compareIDs, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, natArithmetic, NatAccessFits, AccessFits, hptr, hcell]
    all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    all_goals omega

theorem setWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hv : Fits (indexWidth 32 full.length q) value) :
    MacroSafe q full (setWorkspace offset value) state :=
  ⟨fun count hc => PA06A19PrepareCompactMacros014.set_prefix_fit q full offset value hoffset state hf hptr hv count hc,
    fun count hc => PA06A19PrepareCompactMacros014.set_prefix_access q full offset value hoffset state hptr count hc⟩

theorem testWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (counter exit : Nat)
    (hoffset : counter ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hcount : Fits (indexWidth 32 full.length q) (state.heap 16))
    (hcounter : Fits (indexWidth 32 full.length q) (state.heap (16 + counter)))
    (hexit : Fits (indexWidth 32 full.length q) (5 * exit)) : MacroSafe q full (testWorkspace counter exit) state :=
  ⟨fun count hc => PA06A19PrepareCompactMacros014.test_prefix_fit q full counter exit hoffset state hf hptr hcount hcounter hexit count hc,
    fun count hc => PA06A19PrepareCompactMacros014.test_prefix_access q full counter exit hoffset state hptr count hc⟩

theorem incrementWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hinc : Fits (indexWidth 32 full.length q) (state.heap (16 + offset) + 1)) :
    MacroSafe q full (incrementWorkspace offset) state :=
  ⟨fun count hc => PA06A19PrepareCompactMacros014.increment_prefix_fit q full offset hoffset state hf hptr hinc count hc,
    fun count hc => PA06A19PrepareCompactMacros014.increment_prefix_access q full offset hoffset state hptr count hc⟩

theorem single_safe (q : Nat) (full : List (Finset (Fin q))) (op : PackingOp) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hnext : RegistersFit (indexWidth 32 full.length q) (natExecuteOp (rawIncidenceROM q full) op state))
    (hx : NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q) state op) :
    MacroSafe q full [op] state := by
  constructor
  · intro count hc
    have hc' : count ≤ 1 := hc
    interval_cases count
    · exact hf
    · exact hnext
  · intro count hc
    have hc' : count < 1 := hc
    interval_cases count
    exact hx

theorem constant_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (value : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) (hv : Fits (indexWidth 32 full.length q) value) :
    MacroSafe q full [.base (.base (.constant target value))] state := by
  apply single_safe q full _ state hf
  · exact fits_update hf target value hv
  · trivial

theorem setCell_safe (q : Nat) (full : List (Finset (Fin q))) (cell value : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hv : Fits (indexWidth 32 full.length q) value) : MacroSafe q full (setCell cell value) state := by
  have first := constant_safe q full .total value state hf hv
  exact first.append (storeCell_safe q full .total cell hcell _ first.full)

theorem initialize_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) : MacroSafe q full initCode state := by
  have first := setCell_safe q full 0 0 (by omega) state hf (scalar_fits _ _ _ (by omega))
  have hp : (runOps (rawIncidenceROM q full) (setCell 0 0) state).heap 8 = 16 := by
    simpa [setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hptr
  exact first.append (setWorkspace_safe q full 1 0 (by omega) _ first.full hp (scalar_fits _ _ _ (by omega)))

theorem rowInit_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) : MacroSafe q full rowInit state := by
  have first := setWorkspace_safe q full 2 0 (by omega) state hf hptr (scalar_fits _ _ _ (by omega))
  have hp : (runOps (rawIncidenceROM q full) (setWorkspace 2 0) state).heap 8 = 16 := by
    simp [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr,
      show 8 ≠ 16 + 2 by omega]
  exact first.append (setWorkspace_safe q full 3 0 (by omega) _ first.full hp (scalar_fits _ _ _ (by omega)))

theorem jump_safe (q : Nat) (full : List (Finset (Fin q))) (target : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (ht : Fits (indexWidth 32 full.length q) (5 * target)) : MacroSafe q full (jumpTo target) state := by
  have zero := scalar_fits full.length q 0 (by omega)
  constructor
  · intro count hc
    have hc' : count ≤ 3 := hc
    interval_cases count
    · exact hf
    · exact fits_update hf .flag 0 zero
    · exact fits_update (fits_update hf .flag 0 zero) .index (5 * target) ht
    · exact fits_update (fits_update hf .flag 0 zero) .index (5 * target) ht
  · intro count hc
    have hc' : count < 3 := hc
    interval_cases count <;> trivial

theorem tail_safe (q : Nat) (full : List (Finset (Fin q))) (counter target : Nat)
    (hoffset : counter ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hinc : Fits (indexWidth 32 full.length q) (state.heap (16 + counter) + 1))
    (ht : Fits (indexWidth 32 full.length q) (5 * target)) :
    MacroSafe q full (incrementWorkspace counter ++ jumpTo target) state := by
  have first := incrementWorkspace_safe q full counter hoffset state hf hptr hinc
  exact first.append (jump_safe q full target _ first.full ht)


end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Macros

