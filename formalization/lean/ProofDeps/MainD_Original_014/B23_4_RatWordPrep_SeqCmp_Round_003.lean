module

public import B23_4_RatWordPrep_SeqCmp_Paths_002
public import PSTR_WordBool_RatBinary_Run_005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMRatArithmeticParse002
open PSTRWordVM

variable {C : Type*}

def comparisonCap (background : RatInput.Stack → List Bool) (x y : Rat) (tail scratch : List Bool) : Nat :=
  let P := RatPair.space background x y tail scratch
  1024 * (16*P+1) + RatCmp.coefficient * (16*P+1)^4

def roundTime (background : RatInput.Stack → List Bool) (x y : Rat) (tail scratch : List Bool) : Nat :=
  9 * RatPair.fieldSize x y + comparisonCap background x y tail scratch + 94

theorem clean_eq (background : RatInput.Stack → List Bool) (source scratch : List Bool) :
    RatPair.Link.finalContents background source scratch [] = RatPair.Link.initial background source scratch := by
  funext slot; fin_cases slot <;> rfl

theorem cleaned_cmp (background before after : RatInput.Stack → List Bool)
    (source scratch raw finalSource : List Bool)
    (initial : before = RatPair.Link.finalContents background source scratch raw)
    (right : after 13 = []) (left : after 14 = [])
    (frame : ∀ slot, slot ≠ 3 → slot ≠ 13 → slot ≠ 14 → slot ≠ 15 → after slot = before slot) :
    RatDrop.cells after finalSource [] = RatPair.Link.initial background finalSource scratch := by
  funext slot
  fin_cases slot
  all_goals first
    | rfl
    | exact right
    | exact left
    | exact (frame _ (by decide) (by decide) (by decide) (by decide)).trans (by rw [initial]; rfl)

theorem actual_round (caller : Statement C) (second : Bool)
    (background : RatInput.Stack → List Bool) (memory : Store C)
    (x y : Rat) (tail scratch : List Bool) :
    ∃ final : State C, ∃ _segment : Segment caller (entry second background memory x y tail scratch) final
      (roundTime background x y tail scratch),
      final.l = some (nextLabel second) ∧
      registers final.var = writeResult second (decide (x ≤ y)) (registers memory) ∧
      final.stk = RatPair.Link.initial background tail scratch := by
  let old := (pairIso C).symm memory
  obtain ⟨pTrace,pFinal,pFacts⟩ := RatPair.actual_pair .halt background old.1.1.1 old.1.1.2.1 old.1.1.2.2
    old.1.2 old.2 x y tail scratch
  let pMemory := pairIso C pFinal.var
  obtain ⟨cTrace,cFinal,cFacts⟩ := RatCmp.actual_le .halt pMemory.1.1.1 pMemory.1.1.2 pMemory.2 pMemory.1.2 pFinal.stk x y
  have pStacks := RatPair.final_stacks pFacts
  have pPath := pair_path caller second pTrace _ pFinal pFacts.first pFacts.chain pFacts.last pFacts.active
  have cPath := cmp_path caller second cTrace _ cFinal cFacts.first cFacts.chain cFacts.last cFacts.active
  have shared := pair_cmp_shared second pFinal x y pFacts.active pStacks.1 pStacks.2.1
  have pFirst : (pTrace.map (pairCfg second)).head? = some (entry second background memory x y tail scratch) :=
    pPath.1.trans (congrArg some (entry_pair second background memory x y tail scratch))
  have cFirst : (cTrace.map (cmpCfg second)).head? = some (pairCfg second pFinal) :=
    cPath.1.trans (congrArg some shared)
  let P := RatPair.space background x y tail scratch
  have pMass : RatInput.occupied pFinal.stk ≤ 16*P :=
    (pFacts.boundaries pFinal (List.mem_of_getLast? pFacts.last)).2.1
  have outside := (RatBinary.outside_native_le pFinal.stk).trans pMass
  have inputLength : (encode [.rational x,.rational y]).length ≤ 16*P := by
    rw [←pStacks.1]
    exact (RatInput.Encoder.point_mass pFinal.stk 13).trans pMass
  have fourth := Nat.mul_le_mul_left RatCmp.coefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right inputLength 1) 4)
  have cBudget : RatCmp.scale RatCmp.coefficient RatCmp.degree pFinal.stk x y ≤
      comparisonCap background x y tail scratch := by
    rw [RatCmp.degree_eq_four]
    dsimp only [RatCmp.scale, comparisonCap]
    dsimp only [P] at outside fourth
    omega
  let front : Segment caller (entry second background memory x y tail scratch) (pairCfg second pFinal)
      (8*RatPair.fieldSize x y+80) :=
    ⟨pTrace.map (pairCfg second),pFirst,pPath.2.1,pPath.2.2,by simpa only [List.length_map] using pFacts.time⟩
  let cmp : Segment caller (pairCfg second pFinal) (cmpCfg second cFinal)
      (comparisonCap background x y tail scratch) :=
    ⟨cTrace.map (cmpCfg second),cFirst,cPath.2.1,cPath.2.2,
      by simpa only [List.length_map] using cFacts.time.trans cBudget⟩
  let result := decide (x ≤ y)
  have p3 : pFinal.stk 3 = [] := pStacks.2.2.2.2.1
  have c3 : cFinal.stk 3 = [result] := by rw [cFacts.result,p3]
  have cSource : cFinal.stk 15 = RatInput.Encoder.packet x (RatInput.Encoder.packet y tail) := by
    rw [cFacts.restored,pStacks.2.2.2.1]
    exact (RatPair.two_packet_format x y tail).symm
  let post : State C := ⟨some (.discard second 3),record second cFinal.var (some result),
    Function.update cFinal.stk 3 []⟩
  have capture : TM2.step (program caller) (cmpCfg second cFinal) = some post := by
    have e := capture_step caller second result cFinal.var cFinal.stk
    rw [←c3,Function.update_eq_self] at e
    have selected : cmpCfg second cFinal = ⟨some (.capture second),cFinal.var,cFinal.stk⟩ := by
      dsimp only [cmpCfg,LabelMap.configuration]
      rw [cFacts.active]
      simp only [Option.map_some,cmpLabel,ite_true]
    rw [selected]
    exact e
  let captured : Segment caller (cmpCfg second cFinal) post 2 :=
    ⟨[cmpCfg second cFinal,post],rfl,List.isChain_cons_cons.mpr ⟨capture,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let firstDrop := discard_packet caller second post.stk post.var.1 3 4 5 6 (by decide) (by decide) (by decide)
    rfl rfl rfl post.var.2 (sign x) (numeratorDigits x) (denominatorDigits x)
    (RatInput.Encoder.packet y tail)
  let lastDrop := discard_packet caller second post.stk post.var.1 6 7 8 9 (by decide) (by decide) (by decide)
    rfl rfl rfl (true,false) (sign y) (numeratorDigits y) (denominatorDigits y) tail
  let endState := discardCfg second (RatDrop.state post.stk 9 post.var.1 (true,false) tail [])
  let dropped := firstDrop.append lastDrop
  have dropShared : discardCfg second (RatDrop.state post.stk 3 post.var.1 post.var.2
      (RatInput.Encoder.packet x (RatInput.Encoder.packet y tail)) []) = post := by
    have h15 : post.stk 15 = RatInput.Encoder.packet x (RatInput.Encoder.packet y tail) := cSource
    have h3 : post.stk 3 = [] := by dsimp only [post]; rw [Function.update_self]
    change (⟨some (.discard second 3),post.var,
      RatDrop.cells post.stk (RatInput.Encoder.packet x (RatInput.Encoder.packet y tail)) []⟩ : State C) = post
    rw [RatBinary.cells_self post.stk _ h15 h3]
  let back : Segment caller post endState
      ((numeratorDigits x).length+(denominatorDigits x).length+6+
        ((numeratorDigits y).length+(denominatorDigits y).length+6)) :=
    ⟨dropped.trace,dropped.head.trans (congrArg some dropShared),dropped.chain,dropped.last,dropped.count⟩
  let whole := ((front.append cmp).append captured).append back
  have pRegs : registers pMemory = registers memory := by
    have h := congrArg (fun v : RatCmp.Store (Registers C) × Bool × Bool => v.1.1.1.1) pFacts.context_eq
    exact h
  have cRegs : registers cFinal.var = registers pMemory :=
    congrArg (fun v : RatPair.Store (Registers C) => v.1.1.1) cFacts.context_eq
  have finalRegs : registers endState.var = writeResult second result (registers memory) := by
    change writeResult second result (registers cFinal.var) = _
    rw [cRegs,pRegs]
  have finalContents : endState.stk = RatPair.Link.initial background tail scratch := by
    change RatDrop.cells (Function.update cFinal.stk 3 []) tail [] = _
    have cells : RatDrop.cells (Function.update cFinal.stk 3 []) tail [] = RatDrop.cells cFinal.stk tail [] := by
      funext slot; fin_cases slot <;> rfl
    rw [cells]
    exact cleaned_cmp background pFinal.stk cFinal.stk (RatPair.input x y tail) scratch
      (encode [.rational x,.rational y]) tail pFacts.contents cFacts.right cFacts.left cFacts.frame
  have count : whole.trace.length ≤ roundTime background x y tail scratch := by
    have h := whole.count
    have size := RatBinary.fieldSize_eq x y
    dsimp only [RatInput.Encoder.fieldSize] at size
    dsimp only [roundTime]
    omega
  exact ⟨endState,⟨whole.trace,whole.head,whole.chain,whole.last,count⟩,
    by simp only [endState,discardCfg,LabelMap.configuration,RatDrop.state,discardLabel,ite_true,Option.map_some],
    finalRegs,finalContents⟩

end B23_4_RatWordPrep.SeqCmp
