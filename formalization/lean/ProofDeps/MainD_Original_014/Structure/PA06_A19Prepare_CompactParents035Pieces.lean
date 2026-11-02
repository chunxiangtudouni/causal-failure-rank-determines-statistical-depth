module

public import Structure.PA06_A19Prepare_CompactParents035Address
public import Structure.PA06_A19Prepare_CompactOrdering034Data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual small B16/full-width parent initialization, score and update
pieces. Source fields are ordinary card/keep/inverse/current-parent words
and loop counters. Original generic Nat heap/frame formulas are reused;
no supplied parent choice or completed execution safety is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Pieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM RawIncidenceScanSafety
open RawCandidateOrderingRAM (arrayBase arrayAddress arraySlot loadArray loadWorkspace storeWorkspace setWorkspace)
open PA06A19PrepareCompactOrdering034Macros
open PA06A19PrepareCompactOrdering034Data (loadArray_safe loadWorkspace_safe)
open PA06A19PrepareCompactParents035Address (parentAddress_prefix_fit outerTest_prefix_fit initializeBestCard_prefix_fit
  parentAddress_prefix_access outerTest_prefix_access initializeBestCard_prefix_access)

theorem parentAddress_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1)) :
    MacroSafe q full parentAddress state :=
  ⟨fun count hc => parentAddress_prefix_fit q full state hf hptr hheader hnode count
      (by rwa [parentAddress_length] at hc),
    fun count hc => parentAddress_prefix_access q full state hptr count (by rwa [parentAddress_length] at hc)⟩

theorem outerTest_safe (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hcount : state.heap (nodeCountAddress 16 (full.length + q + 1)) ≤ (full.length + q + 1))
    (hexit : Fits (indexWidth 32 full.length q) (5 * exit)) :
    MacroSafe q full (outerTest exit) state :=
  ⟨fun count hc => outerTest_prefix_fit q full exit state hf hptr hheader hnode hcount hexit count
      (by rwa [outerTest_length] at hc),
    fun count hc => outerTest_prefix_access q full exit state hptr hheader count (by rwa [outerTest_length] at hc)⟩

theorem initializeBestCard_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) : MacroSafe q full initializeBestCard state :=
  ⟨fun count hc => initializeBestCard_prefix_fit q full state hf hptr count
      (by rwa [initializeBestCard_length] at hc),
    fun count hc => initializeBestCard_prefix_access q full state hptr count (by rwa [initializeBestCard_length] at hc)⟩

theorem initializeParent_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1)) :
    MacroSafe q full initializeParent state := by
  let rom := rawIncidenceROM q full
  let zeroCode : List PackingOp := [.base (.base (.constant .total 0))]
  let zeroed := runOps rom zeroCode state
  have z := constant_safe q full .total 0 state hf (scalar_fits _ _ _ (by omega))
  have a := parentAddress_safe q full zeroed z.full hptr hheader hnode
  let addressed := runOps rom parentAddress zeroed
  have haddr : addressed.register .address =
      parentSlot 16 (full.length + q + 1)
        (state.heap (16 + 1)) := by
    simpa only [show zeroed.heap = state.heap from rfl, hptr, hheader] using parentAddress_value rom zeroed
  have hx : RawIncidenceScanSafety.NatAccessFits rom (linearLimit full.length q) addressed
      (.base (.base (.storeHeap .address .total))) := by
    change addressed.register .address < linearLimit full.length q
    rw [haddr]
    unfold parentSlot arraySlot linearLimit PA06A19PrepareCompactWord008.linearLimit
    omega
  have s := single_safe q full (.base (.base (.storeHeap .address .total))) addressed a.full a.full hx
  simpa only [initializeParent, List.append_assoc] using z.append (a.append s)

theorem initializeChild_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1)) :
    MacroSafe q full initializeChild state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  have b := initializeBestCard_safe q full state hf hptr
  let best := runOps rom initializeBestCard state
  have bh : best.heap = Function.update state.heap (B + 3) (q + 1) := by
    simpa only [hptr] using initializeBestCard_heap q full state
  have bp : best.heap 8 = B := by rw [bh]; simpa (disch := omega) using hptr
  have bc : best.heap B = M := by rw [bh]; simpa using hheader
  have bn : best.heap (B + 1) ≤ M := by rw [bh]; simpa using hnode
  have p := initializeParent_safe q full best b.full bp bc bn
  let parent := runOps rom initializeParent best
  have ph : parent.heap = Function.update best.heap (parentSlot B M (best.heap (B + 1))) 0 := by
    simpa only [bp, bc] using initializeParent_heap rom best
  have pp : parent.heap 8 = B := by
    rw [ph]
    simpa (disch := unfold parentSlot arraySlot; omega) using bp
  have last := setWorkspace_safe q full 2 0 (by omega) parent p.full pp (scalar_fits _ _ _ (by omega))
  simpa only [initializeChild, List.append_assoc] using b.append (p.append last)

theorem pairArguments_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hlater : state.heap (16 + 2) ≤ (full.length + q + 1))
    (horder : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 2
        (state.heap (16 + 1))))) :
    MacroSafe q full pairArguments state := by
  let rom := rawIncidenceROM q full
  let B := 16
  have hb : 16 ≤ B := le_rfl
  have a := loadArray_safe q full .value 2 1 (by omega) (by omega) state hf hptr hheader hnode horder
  let loaded := runOps rom (loadArray .value 2 1) state
  have ah : loaded.heap = state.heap := by dsimp only [loaded]; rw [RawCandidateOrderingRAM.loadArray_runOps]; rfl
  have s := storeCell_safe q full .value 1 (by omega) loaded a.full
  let stored := runOps rom (storeCell .value 1) loaded
  have sh : stored.heap = Function.update state.heap 1 (loaded.register .value) := by
    simp [stored, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, ah]
  have sp : stored.heap 8 = B := by rw [sh]; simpa using hptr
  have sl : Fits (indexWidth 32 full.length q) (stored.heap (B + 2)) := by
    rw [sh, Function.update_of_ne (by omega)]
    exact scalar_fits _ _ _ (hlater.trans (by omega))
  have l := loadWorkspace_safe q full .old 2 (by omega) stored s.full sp sl
  have e := storeCell_safe q full .old 2 (by omega) _ l.full
  simpa only [pairArguments, List.append_assoc] using a.append (s.append (l.append e))

private theorem selectOp_safe (q : Nat) (full : List (Finset (Fin q)))
    (target condition whenTrue whenFalse : Register) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) :
    MacroSafe q full [.base (.base (.select target condition whenTrue whenFalse))] state := by
  apply single_safe q full _ state hf
  · apply fits_update hf
    change Fits _ (if state.register condition = 0 then state.register whenFalse else state.register whenTrue)
    split <;> exact hf _
  · trivial

private theorem subtract_safe (q : Nat) (full : List (Finset (Fin q)))
    (target left right : Register) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) :
    MacroSafe q full [.base (.subtract target left right)] state := by
  apply single_safe q full _ state hf
  · apply fits_update hf
    exact (Nat.sub_le _ _).trans_lt (hf left)
  · trivial

private theorem minimum_safe (q : Nat) (full : List (Finset (Fin q)))
    (target left right : Register) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) :
    MacroSafe q full [.base (.base (.minimum target left right))] state := by
  apply single_safe q full _ state hf
  · apply fits_update hf
    exact (Nat.min_le_left _ _).trans_lt (hf left)
  · trivial

private theorem storeWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoff : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) : MacroSafe q full (storeWorkspace offset) state :=
  ⟨fun count hc => PA06A19PrepareCompactWord008.store_prefix_fit q full 16 offset state hf hptr
      (PA06A19PrepareCompactMacros014.small_constant_fits _ _ 8 (by decide))
      (PA06A19PrepareCompactMacros014.small_constant_fits _ _ 16 le_rfl)
      (PA06A19PrepareCompactMacros014.small_constant_fits _ _ offset (by omega))
      (PA06A19PrepareCompactMacros014.workspace_offset_fits _ _ offset hoff) count hc,
    fun count hc => PA06A19PrepareCompactWord008.store_prefix_access q full 16 offset (linearLimit full.length q) state hptr
      (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega)
      (PA06A19PrepareCompactMacros014.workspace_offset_lt_limit _ _ offset hoff) count hc⟩

theorem conditionScore_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hlater : state.heap (16 + 2) ≤ (full.length + q + 1))
    (h5 : Fits (indexWidth 32 full.length q) (state.heap 5))
    (h6 : Fits (indexWidth 32 full.length q) (state.heap 6))
    (hkeep : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 1
        (state.heap (16 + 2)))))
    (hcard : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 0
        (state.heap (16 + 2)))))
    (hbest : Fits (indexWidth 32 full.length q) (state.heap (16 + 3))) :
    MacroSafe q full conditionScore state := by
  let rom := rawIncidenceROM q full
  have a := loadCell_safe q full .old 5 (by omega) state hf h5
  let s1 := runOps rom (loadCell .old 5) state
  have b := loadCell_safe q full .total 6 (by omega) s1 a.full h6
  let s2 := runOps rom (loadCell .total 6) s1
  have c := constant_safe q full .flag 0 s2 b.full (scalar_fits _ _ _ (by omega))
  let s3 := runOps rom [.base (.base (.constant .flag 0))] s2
  have d := selectOp_safe q full .value .old .flag .total s3 c.full
  let s4 := runOps rom [.base (.base (.select .value .old .flag .total))] s3
  have e := loadArray_safe q full .old 1 2 (by omega) (by omega) s4 d.full hptr hheader hlater hkeep
  let s5 := runOps rom (loadArray .old 1 2) s4
  have f := constant_safe q full .flag 0 s5 e.full (scalar_fits _ _ _ (by omega))
  let s6 := runOps rom [.base (.base (.constant .flag 0))] s5
  have g := selectOp_safe q full .value .old .value .flag s6 f.full
  let s7 := runOps rom [.base (.base (.select .value .old .value .flag))] s6
  have h := loadArray_safe q full .total 0 2 (by omega) (by omega) s7 g.full hptr hheader hlater hcard
  let s8 := runOps rom (loadArray .total 0 2) s7
  have i := loadWorkspace_safe q full .old 3 (by omega) s8 h.full hptr hbest
  let s9 := runOps rom (loadWorkspace .old 3) s8
  have j := subtract_safe q full .flag .old .total s9 i.full
  let s10 := runOps rom [.base (.subtract .flag .old .total)] s9
  have k := minimum_safe q full .value .value .flag s10 j.full
  simpa only [conditionScore, List.append_assoc, List.cons_append, List.nil_append] using
    a.append (b.append (c.append (d.append (e.append (f.append (g.append (h.append (i.append (j.append k)))))))))

theorem saveBestCard_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) : MacroSafe q full saveBestCard state := by
  have a := selectOp_safe q full .total .value .total .old state hf
  have b := storeWorkspace_safe q full 3 (by omega) _ a.full hptr
  exact a.append b

theorem saveParent_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hlater : state.heap (16 + 2) ≤ (full.length + q + 1))
    (hinverse : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 3
        (state.heap (16 + 2)))))
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot 16 (full.length + q + 1)
        (state.heap (16 + 1))))) :
    MacroSafe q full saveParent state := by
  let rom := rawIncidenceROM q full
  have a := loadArray_safe q full .total 3 2 (by omega) (by omega) state hf hptr hheader hlater hinverse
  let loaded := runOps rom (loadArray .total 3 2) state
  have b := parentAddress_safe q full loaded a.full hptr hheader hnode
  let addressed := runOps rom parentAddress loaded
  have haddr : addressed.register .address = parentSlot 16 (full.length + q + 1)
      (state.heap (16 + 1)) := by
    simpa only [show loaded.heap = state.heap from rfl, hptr, hheader] using parentAddress_value rom loaded
  have haddrBound : addressed.register .address < linearLimit full.length q := by
    rw [haddr]
    unfold parentSlot arraySlot linearLimit PA06A19PrepareCompactWord008.linearLimit
    omega
  have c := single_safe q full (.base (.base (.loadHeap .old .address))) addressed b.full
    (by apply fits_update b.full; change Fits _ (addressed.heap (addressed.register .address)); rw [haddr]; exact hparent)
    (by exact haddrBound)
  let read := runOps rom [.base (.base (.loadHeap .old .address))] addressed
  have d := selectOp_safe q full .total .value .total .old read c.full
  let chosen := runOps rom [.base (.base (.select .total .value .total .old))] read
  have e := single_safe q full (.base (.base (.storeHeap .address .total))) chosen d.full d.full
    (by exact haddrBound)
  simpa only [saveParent, List.append_assoc, List.cons_append, List.nil_append] using a.append (b.append (c.append (d.append e)))

theorem innerTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hlater : state.heap (16 + 2) ≤ (full.length + q + 1))
    (h5 : Fits (indexWidth 32 full.length q) (state.heap 5))
    (h6 : Fits (indexWidth 32 full.length q) (state.heap 6))
    (hkeep : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 1
        (state.heap (16 + 2)))))
    (hcard : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 0
        (state.heap (16 + 2)))))
    (hbest : Fits (indexWidth 32 full.length q) (state.heap (16 + 3)))
    (hinverse : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) 3
        (state.heap (16 + 2)))))
    (hparent : Fits (indexWidth 32 full.length q)
      (state.heap (parentSlot 16 (full.length + q + 1)
        (state.heap (16 + 1)))))
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    MacroSafe q full (innerTail start) state := by
  let rom := rawIncidenceROM q full
  let B := 16
  let M := (full.length + q + 1)
  have hb : 16 ≤ B := le_rfl
  have a := conditionScore_safe q full state hf hptr hheader hlater h5 h6 hkeep hcard hbest
  let tested := runOps rom conditionScore state
  have b := saveBestCard_safe q full tested a.full hptr
  let saved := runOps rom saveBestCard tested
  have sh : saved.heap = Function.update state.heap (B + 3)
      (if tested.register .value = 0 then tested.register .old else tested.register .total) := by
    simpa only [show tested.heap = state.heap from rfl, hptr] using saveBestCard_heap rom tested
  have frame (address : Nat) (hne : address ≠ B + 3) : saved.heap address = state.heap address := by
    rw [sh]
    exact Function.update_of_ne hne _ _
  have sp : saved.heap 8 = B := (frame _ (by omega)).trans hptr
  have sc : saved.heap B = M := (frame _ (by omega)).trans hheader
  have sn : saved.heap (B + 1) = state.heap (B + 1) := frame _ (by omega)
  have sl : saved.heap (B + 2) = state.heap (B + 2) := frame _ (by omega)
  have si : Fits (indexWidth 32 full.length q) (saved.heap (arraySlot B M 3 (saved.heap (B + 2)))) := by
    rw [sl, frame _ (by unfold arraySlot; omega)]
    exact hinverse
  have sr : Fits (indexWidth 32 full.length q) (saved.heap (parentSlot B M (saved.heap (B + 1)))) := by
    rw [sn, frame _ (by unfold parentSlot arraySlot; omega)]
    exact hparent
  have p := saveParent_safe q full saved b.full sp sc
    (by rw [sn]; exact hnode) (by rw [sl]; exact hlater) si sr
  let parent := runOps rom saveParent saved
  have parentFrame (address : Nat) (hne : address ≠ parentSlot B M (saved.heap (B + 1))) :
      parent.heap address = saved.heap address := by
    change (runOps rom saveParent saved).heap address = _
    rw [saveParent_heap, sp, sc]
    exact Function.update_of_ne hne _ _
  have pp : parent.heap 8 = B :=
    (parentFrame _ (by unfold parentSlot arraySlot; omega)).trans sp
  have pl : parent.heap (B + 2) = state.heap (B + 2) :=
    (parentFrame _ (by unfold parentSlot arraySlot; omega)).trans sl
  have inc : Fits (indexWidth 32 full.length q) (parent.heap (B + 2) + 1) := by
    rw [pl]
    apply scalar_fits
    change state.heap (16 + 2) + 1 ≤ 4 * (full.length + q + 1) + 32
    omega
  have ht : Fits (indexWidth 32 full.length q) (5 * (start + 64)) := lt_of_le_of_lt (by omega) hend
  have t := PA06A19PrepareCompactOrdering034Macros.tail_safe q full 2 (start + 64) (by omega) parent p.full pp inc ht
  simpa only [innerTail, List.append_assoc] using a.append (b.append (p.append t))

theorem outerTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hnode : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 361))) :
    MacroSafe q full (outerTail start) state :=
  PA06A19PrepareCompactOrdering034Macros.tail_safe q full 1 (start + 6) (by omega) state hf hptr
    (scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend)


end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Pieces

