module

public import Structure.PA06_A19Prepare_CompactOrdering034Macros

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual B16/width32 array and data-update pieces for the original303-op
sorter.018 supplies every actual array prefix. Numeric compare/rank/inverse
values are bounded from the source cards/keep bits and real counters.
Original generic Nat frames, code lists and rank semantics are reused;
no whole sorted answer or hSafe is an input. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Data

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM RawIncidenceScanSafety
open PA06A19PrepareCompactOrdering034Macros
open RawCandidateOrderingWord (candidateCard_le bit_le_one inverseValueCode inverseValueCode_length
  storeCell_heap fetchOne fetchOne_heap fetched_heap_preserved)

def OrdFits (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ position < (full.length + q + 1),
    Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 2 position))

theorem OrdFits.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : OrdFits q full before) (hh : after.heap = before.heap) : OrdFits q full after := by
  intro position hp
  rw [hh]
  exact h position hp

theorem OrdFits.of_innerFrame {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : OrdFits q full before) (frame : InnerFrame 16 before after) : OrdFits q full after := by
  intro position hp
  rw [frame _ (by unfold arraySlot; omega) (by unfold arraySlot; omega)
    (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
    (by unfold arraySlot; omega) (by unfold arraySlot; omega)]
  exact h position hp

theorem rankCount_le (card : Nat → Nat) (keep : Nat → Bool) (candidate upto : Nat) :
    rankCount card keep candidate upto ≤ upto := by
  simpa only [rankCount, List.length_range] using List.length_filter_le
    (fun other => keep other && decide (Precedes card other candidate)) (List.range upto)

theorem comparison_middle_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hj : state.heap (16 + 2) ≤ (full.length + q + 1))
    (hrank : state.heap (16 + 3) ≤ (full.length + q + 1))
    (hleft : state.heap 1 ≤ q) (hright : state.heap 2 ≤ q) (hkeep : state.heap 3 ≤ 1) :
    MacroSafe q full (compareCards ++ compareIDs) state := by
  have first := compareCards_safe q full state hf hleft hright
  let compared := runOps (rawIncidenceROM q full) compareCards state
  have effects := compareCards_effect (rawIncidenceROM q full) state
  have hh : compared.heap = Function.update
      (Function.update state.heap 4 (1 - min 1 ((state.heap 1 - state.heap 2) + (state.heap 2 - state.heap 1))))
      5 (min 1 (state.heap 1 - state.heap 2)) := effects.1
  have frame (address : Nat) (h4 : address ≠ 4) (h5 : address ≠ 5) : compared.heap address = state.heap address := by
    rw [hh, Function.update_of_ne h5, Function.update_of_ne h4]
  apply first.append
  apply compareIDs_safe q full compared first.full
  · exact (frame 8 (by omega) (by omega)).trans hptr
  · rw [frame _ (by omega) (by omega)]
    exact hi
  · rw [frame _ (by omega) (by omega)]
    exact hj
  · rw [frame _ (by omega) (by omega)]
    exact hrank
  · rw [frame 3 (by omega) (by omega)]
    exact hkeep
  · rw [hh]
    simp only [Function.update_of_ne (by omega : 4 ≠ 5), Function.update_self]
    omega
  · rw [hh, Function.update_self]
    exact Nat.min_le_left _ _
  · exact effects.2

theorem loadWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hread : Fits (indexWidth 32 full.length q) (state.heap (16 + offset))) :
    MacroSafe q full (loadWorkspace target offset) state :=
  ⟨fun count hc => PA06A19PrepareCompactMacros014.load_prefix_fit q full target offset hoffset state hf hptr hread count hc,
    fun count hc => PA06A19PrepareCompactMacros014.load_prefix_access q full target offset hoffset state hptr count hc⟩

theorem inverseValueCode_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hrank : state.heap (16 + 3) ≤ (full.length + q + 1))
    (hkeep : state.heap 3 ≤ 1) : MacroSafe q full inverseValueCode state := by
  have hlim : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  have hmul := Nat.mul_le_mul (Nat.succ_le_succ hrank) hkeep
  have hoff : 16 + 3 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 10 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 10 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [inverseValueCode_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (inverseValueCode[count]'(by rw [inverseValueCode_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [inverseValueCode, loadWorkspace, loadCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute, natArithmetic]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
      all_goals omega
  · intro count hc
    have hc' : count < 10 := hc
    interval_cases count <;>
      simp [inverseValueCode, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hptr, hoff, hcell]

theorem addCount_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hcount : state.heap 0 ≤ (full.length + q + 1)) (hkeep : state.heap 3 ≤ 1) : MacroSafe q full addCount state := by
  have hlim : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 7 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 7 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 7; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (addCount[count]'(by change count < 7; exact hlt)) _)
      interval_cases count <;>
        simp only [addCount, loadCell, storeCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
      all_goals omega
  · intro count hc
    have hc' : count < 7 := hc
    interval_cases count <;>
      simp [addCount, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hcell]

theorem loadArray_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (hsource : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) factor (state.heap (16 + counter))))) :
    MacroSafe q full (loadArray target factor counter) state :=
  ⟨fun count hc => PA06A19PrepareCompactArrays018.loadArray_prefix_fit q full target factor counter hfactor hcounter state
      hf hptr hheader hindex hsource count (by rwa [loadArray_length] at hc),
    fun count hc => PA06A19PrepareCompactArrays018.loadArray_prefix_access q full target factor counter hfactor hcounter state
      hptr hheader hindex count (by rwa [loadArray_length] at hc)⟩

theorem storeArray_safe (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1)) :
    MacroSafe q full (storeArray factor counter) state :=
  ⟨fun count hc => PA06A19PrepareCompactArrays018.storeArray_prefix_fit q full factor counter hfactor hcounter state
      hf hptr hheader hindex count (by rwa [storeArray_length] at hc),
    fun count hc => PA06A19PrepareCompactArrays018.storeArray_prefix_access q full factor counter hfactor hcounter state
      hptr hheader hindex count (by rwa [storeArray_length] at hc)⟩

theorem fetchOne_safe (q : Nat) (full : List (Finset (Fin q))) (factor counter cell : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (hcell : cell ≤ 8) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (hsource : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) factor (state.heap (16 + counter))))) :
    MacroSafe q full (fetchOne factor counter cell) state := by
  have first := loadArray_safe q full .total factor counter hfactor hcounter state hf hptr hheader hindex hsource
  exact first.append (storeCell_safe q full .total cell hcell _ first.full)

theorem fetchComparison_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hj : state.heap (16 + 2) ≤ (full.length + q + 1))
    (hleft : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) 0 (state.heap (16 + 1)))))
    (hright : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) 0 (state.heap (16 + 2)))))
    (hkeep : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) 1 (state.heap (16 + 2))))) :
    MacroSafe q full fetchComparison state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  let one := runOps rom (fetchOne 0 1 1) state
  have f1 (address : Nat) (ha : 8 ≤ address) : one.heap address = state.heap address :=
    fetched_heap_preserved rom 0 1 1 address state (by omega)
  have s1 := fetchOne_safe q full 0 1 1 (by omega) (by omega) (by omega) state hf hptr hheader hi hleft
  have s2 := fetchOne_safe q full 0 2 2 (by omega) (by omega) (by omega) one s1.full
    ((f1 8 le_rfl).trans hptr) ((f1 B (by omega)).trans hheader) (by rw [f1 _ (by omega)]; exact hj)
    (by rw [f1 (B + 2) (by omega), f1 _ (by unfold arraySlot; omega)]; exact hright)
  let two := runOps rom (fetchOne 0 2 2) one
  have f2 (address : Nat) (ha : 8 ≤ address) : two.heap address = state.heap address :=
    (fetched_heap_preserved rom 0 2 2 address one (by omega)).trans (f1 address ha)
  have s3 := fetchOne_safe q full 1 2 3 (by omega) (by omega) (by omega) two s2.full
    ((f2 8 le_rfl).trans hptr) ((f2 B (by omega)).trans hheader) (by rw [f2 _ (by omega)]; exact hj)
    (by rw [f2 (B + 2) (by omega), f2 _ (by unfold arraySlot; omega)]; exact hkeep)
  have allSafe := (s1.append s2).append (by simpa only [runOps_append] using s3)
  simpa only [fetchComparison, fetchOne, List.append_assoc] using allSafe

theorem comparison_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hi : state.heap (16 + 1) < (full.length + q + 1))
    (hj : state.heap (16 + 2) < (full.length + q + 1))
    (hrank : state.heap (16 + 3) ≤ (full.length + q + 1))
    (htables : InputTables 16 (full.length + q + 1)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state) :
    MacroSafe q full comparison state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  have lc := htables.1 _ hi
  have rc := htables.1 _ hj
  have kc := htables.2 _ hj
  have lv : state.heap (arraySlot B M 0 (state.heap (B + 1))) ≤ q := by rw [lc]; exact candidateCard_le _ _ _
  have rv : state.heap (arraySlot B M 0 (state.heap (B + 2))) ≤ q := by rw [rc]; exact candidateCard_le _ _ _
  have kv : state.heap (arraySlot B M 1 (state.heap (B + 2))) ≤ 1 := by rw [kc]; exact bit_le_one _
  have qfit : Fits (indexWidth 32 full.length q) q := scalar_fits _ _ _ (by omega)
  have first := fetchComparison_safe q full state hf hptr hheader hi.le hj.le
    (lv.trans_lt qfit) (rv.trans_lt qfit) (kv.trans_lt (scalar_fits _ _ 1 (by omega)))
  let fetched := runOps rom fetchComparison state
  have hh := fetchComparison_heap rom state (by rw [hptr])
  change fetched.heap = Function.update (Function.update (Function.update state.heap 1 _) 2 _) 3 _ at hh
  rw [hptr, hheader] at hh
  have frame (address : Nat) (ha : 8 ≤ address) : fetched.heap address = state.heap address := by
    rw [hh]
    simp only [Function.update_of_ne (by omega : address ≠ 3),
      Function.update_of_ne (by omega : address ≠ 2), Function.update_of_ne (by omega : address ≠ 1)]
  rw [comparison, List.append_assoc]
  apply first.append
  apply comparison_middle_safe q full fetched first.full
  · exact (frame 8 le_rfl).trans hptr
  · rw [frame _ (by omega)]; exact hi.le
  · rw [frame _ (by omega)]; exact hj.le
  · rw [frame _ (by omega)]; exact hrank
  · rw [hh]; simpa using lv
  · rw [hh]; simpa using rv
  · rw [hh]; simpa using kv

theorem select_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) :
    MacroSafe q full [.base (.base (.select .total .flag .total .old))] state := by
  apply single_safe q full _ state hf
  · apply fits_update hf
    change Fits _ (if state.register .flag = 0 then state.register .old else state.register .total)
    split <;> exact hf _
  · trivial

theorem storeOrd_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hi : state.heap (16 + 1) < (full.length + q + 1))
    (hrank : state.heap (16 + 3) < (full.length + q + 1))
    (hkeep : state.heap (arraySlot 16 (full.length + q + 1) 1
      (state.heap (16 + 1))) ≤ 1)
    (horder : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) 2 (state.heap (16 + 3))))) :
    MacroSafe q full storeOrd state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  let loadedKeep := runOps rom (loadArray .flag 1 1) state
  have s1 := loadArray_safe q full .flag 1 1 (by omega) (by omega) state hf hptr hheader hi.le
    (scalar_fits _ _ _ (by omega))
  have h1 : loadedKeep.heap = state.heap := loadArray_heap rom .flag 1 1 state
  let saved := runOps rom (storeCell .flag 3) loadedKeep
  have s2 := storeCell_safe q full .flag 3 (by omega) loadedKeep s1.full
  have h2 : saved.heap = Function.update state.heap 3
      (state.heap (arraySlot B M 1 (state.heap (B + 1)))) := by
    rw [show saved = runOps rom (storeCell .flag 3) loadedKeep from rfl,
      storeCell_heap rom .flag 3 _ (by decide), h1, loadArray_value, hptr, hheader]
  have frame (address : Nat) (ha : 8 ≤ address) : saved.heap address = state.heap address := by
    rw [h2, Function.update_of_ne (by omega : address ≠ 3)]
  let loadedID := runOps rom (loadWorkspace .total 1) saved
  have s3 := loadWorkspace_safe q full .total 1 (by omega) saved s2.full ((frame 8 le_rfl).trans hptr)
    (by rw [frame _ (by omega)]; exact scalar_fits _ _ _ (by omega))
  have h3 : loadedID.heap = saved.heap := by
    change (runOps rom (loadWorkspace .total 1) saved).heap = saved.heap
    rw [loadWorkspace_runOps]
    rfl
  have idframe (address : Nat) (ha : 8 ≤ address) : loadedID.heap address = state.heap address :=
    (congrFun h3 address).trans (frame address ha)
  let oldOrd := runOps rom (loadArray .old 2 3) loadedID
  have s4 := loadArray_safe q full .old 2 3 (by omega) (by omega) loadedID s3.full
    ((idframe 8 le_rfl).trans hptr) ((idframe B (by omega)).trans hheader)
    (by rw [idframe _ (by omega)]; exact hrank.le)
    (by rw [idframe (B + 3) (by omega), idframe _ (by unfold arraySlot; omega)]; exact horder)
  have h4 : oldOrd.heap = loadedID.heap := loadArray_heap rom .old 2 3 loadedID
  have oldframe (address : Nat) (ha : 8 ≤ address) : oldOrd.heap address = state.heap address :=
    (congrFun h4 address).trans (idframe address ha)
  let selected := natExecuteOp rom (.base (.base (.select .total .flag .total .old))) oldOrd
  have s5 := select_safe q full oldOrd s4.full
  have sh : selected.heap = oldOrd.heap := rfl
  have s6 := storeArray_safe q full 2 3 (by omega) (by omega) selected s5.full
    ((congrFun sh 8).trans ((oldframe 8 le_rfl).trans hptr))
    ((congrFun sh B).trans ((oldframe B (by omega)).trans hheader))
    (by rw [sh, oldframe _ (by omega)]; exact hrank.le)
  have allSafe := s1.append (s2.append (s3.append (s4.append (s5.append s6))))
  simpa only [storeOrd, List.append_assoc] using allSafe

theorem storeInverse_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hi : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hrank : state.heap (16 + 3) ≤ (full.length + q + 1))
    (hkeep : state.heap 3 ≤ 1) : MacroSafe q full storeInverse state := by
  let rom := rawIncidenceROM q full
  let computed := runOps rom inverseValueCode state
  have first := inverseValueCode_safe q full state hf hptr hrank hkeep
  have hh : computed.heap = state.heap := by
    simp [computed, inverseValueCode, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  have second := storeArray_safe q full 3 1 (by omega) (by omega) computed first.full
    ((congrFun hh 8).trans hptr) ((congrFun hh _).trans hheader) (by rw [hh]; exact hi)
  simpa only [storeInverse, inverseValueCode, List.append_assoc] using first.append second

theorem finishRow_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hi : state.heap (16 + 1) < (full.length + q + 1))
    (hrank : state.heap (16 + 3) < (full.length + q + 1))
    (hkeep : state.heap (arraySlot 16 (full.length + q + 1) 1
      (state.heap (16 + 1))) ≤ 1)
    (horder : Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16
      (full.length + q + 1) 2 (state.heap (16 + 3)))))
    (hcount : state.heap 0 ≤ (full.length + q + 1)) : MacroSafe q full finishRow state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  let ordered := runOps rom storeOrd state
  have first := storeOrd_safe q full state hf hptr hheader hi hrank hkeep horder
  have ho := storeOrd_heap rom state (by rw [hptr])
  dsimp only at ho
  rw [hptr, hheader] at ho
  change ordered.heap = _ at ho
  have frame (address : Nat) (ha : address < B) (h3 : address ≠ 3) : ordered.heap address = state.heap address := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_of_ne h3]
  have controls (offset : Nat) (hoff : offset ≤ 3) : ordered.heap (B + offset) = state.heap (B + offset) := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_of_ne (by omega : B + offset ≠ 3)]
  have ok : ordered.heap 3 ≤ 1 := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_self]
    exact hkeep
  have second := storeInverse_safe q full ordered first.full ((frame 8 (by omega) (by omega)).trans hptr)
    (by simpa only [Nat.add_zero] using (controls 0 (by omega)).trans hheader)
    (by rw [controls 1 (by omega)]; exact hi.le) (by rw [controls 3 (by omega)]; exact hrank.le) ok
  let inversed := runOps rom storeInverse ordered
  have ih := storeInverse_heap rom ordered
  change inversed.heap = _ at ih
  have ib : ordered.heap 8 = B := (frame 8 (by omega) (by omega)).trans hptr
  have im : ordered.heap B = M := by simpa only [Nat.add_zero] using (controls 0 (by omega)).trans hheader
  rw [ib, im] at ih
  have ic : inversed.heap 0 ≤ M := by
    rw [ih, Function.update_of_ne (by unfold arraySlot; omega), frame 0 (by omega) (by omega)]
    exact hcount
  have ik : inversed.heap 3 ≤ 1 := by
    rw [ih, Function.update_of_ne (by unfold arraySlot; omega)]
    exact ok
  have third := addCount_safe q full inversed second.full ic ik
  have allSafe := first.append (second.append third)
  simpa only [finishRow, List.append_assoc] using allSafe

private theorem arrayBase_effect (q : Nat) (full : List (Finset (Fin q))) (factor : Nat) (state : NatState)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1) :
    (runOps (rawIncidenceROM q full) (arrayBase factor) state).register .address =
      16 + (full.length + q + 1) * factor + 4 ∧
      (runOps (rawIncidenceROM q full) (arrayBase factor) state).heap = state.heap := by
  simp [arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hptr, hheader]

theorem finishCode_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hcount : state.heap 0 ≤ (full.length + q + 1)) : MacroSafe q full finishCode state := by
  let rom := rawIncidenceROM q full
  have first := loadCell_safe q full .total 0 (by omega) state hf (scalar_fits _ _ _ (by omega))
  let loaded := runOps rom (loadCell .total 0) state
  have lh : loaded.heap = state.heap := rfl
  have bp : loaded.heap 8 = 16 := (congrFun lh 8).trans hptr
  have bm : loaded.heap 16 = (full.length + q + 1) := (congrFun lh _).trans hheader
  have base : MacroSafe q full (arrayBase 4) loaded :=
    ⟨fun count hc => PA06A19PrepareCompactArrays018.arrayBase_prefix_fit q full 4 (by omega) loaded first.full bp bm count
        (by rwa [arrayBase_length] at hc),
      fun count hc => PA06A19PrepareCompactArrays018.arrayBase_prefix_access q full 4 loaded bp count
        (by rwa [arrayBase_length] at hc)⟩
  let addressed := runOps rom (arrayBase 4) loaded
  have ba := arrayBase_effect q full 4 loaded bp bm
  have last : MacroSafe q full [.base (.base (.storeHeap .address .total))] addressed := by
    apply single_safe q full (.base (.base (.storeHeap .address .total))) addressed base.full
    · exact base.full
    · change addressed.register .address < linearLimit full.length q
      rw [ba.1]
      unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
      omega
  have allSafe := first.append (base.append last)
  simpa only [finishCode, List.append_assoc] using allSafe


end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactOrdering034Data

