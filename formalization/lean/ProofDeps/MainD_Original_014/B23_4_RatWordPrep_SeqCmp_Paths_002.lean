module

public import B23_4_RatWordPrep_SeqCmp_Code_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

structure Segment (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
  have shape : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]; rfl
  refine ⟨front.trace ++ back.trace.tail, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append, List.length_tail]
    omega

theorem pair_path (caller : Statement C) (second : Bool)
    (trace : List (RatPair.State (RatCmp.Store (Registers C))))
    (before final : RatPair.State (RatCmp.Store (Registers C)))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatPair.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some RatPair.done) :
    (trace.map (pairCfg second)).head? = some (pairCfg second before) ∧
    (trace.map (pairCfg second)).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (trace.map (pairCfg second)).getLast? = some (pairCfg second final) := by
  let old := RatPair.program (C := RatCmp.Store (Registers C)) .halt
  let isoProgram := StoreIso.machine (pairIso C) old
  have iso := StoreIso.actual_path_on (pairIso C) old isoProgram trace before final first chain last
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram RatPair.done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on (pairLabel second) isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      exact program_pair caller second point (by intro same; subst point; exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (pairIso C))).map
      (LabelMap.configuration (pairLabel second)) = trace.map (pairCfg second) := by
    rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1, mapped.2.1, mapped.2.2.1⟩

theorem cmp_path (caller : Statement C) (second : Bool)
    (trace : List (RatCmp.State (RatPair.Store (Registers C))))
    (before final : RatCmp.State (RatPair.Store (Registers C)))
    (first : trace.head? = some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatCmp.program .halt) a = some b))
    (last : trace.getLast? = some final) (active : final.l = some RatCmp.done) :
    (trace.map (cmpCfg second)).head? = some (cmpCfg second before) ∧
    (trace.map (cmpCfg second)).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (trace.map (cmpCfg second)).getLast? = some (cmpCfg second final) := by
  have proper := NativeMulLink.no_early_halt_port (RatCmp.program .halt) RatCmp.done rfl trace final chain last active
  have mapped := LabelMap.actual_path_on (cmpLabel second) (RatCmp.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_cmp caller second point (by intro same; subst point; exact proper current member selected))
  exact ⟨mapped.1, mapped.2.1, mapped.2.2.1⟩

theorem field_proper {D : Type*} (background : RatInput.Stack → List Bool) (context : D)
    (point next : RatDrop.Label) (digits : List Bool) (memory : RatOutput.Store) (tail parked : List Bool) :
    ∀ current ∈ (RatDrop.fieldTrace false background context point next digits memory tail parked).dropLast,
      current.l = some point := by
  induction digits generalizing memory parked with
  | nil =>
    intro current member
    simp only [RatDrop.fieldTrace, List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
      List.not_mem_nil, or_false] at member
    subst current; rfl
  | cons bit rest ih =>
    rw [RatDrop.fieldTrace, List.dropLast_cons_of_ne_nil (RatDrop.field_nonempty _ _ _ _ _ _ _ _ _)]
    intro current member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · exact ih _ _ current later

def field_path (caller : Statement C) (second : Bool)
    (background : RatInput.Stack → List Bool) (context : DropContext C)
    (point next : RatDrop.Label) (not9 : point ≠ 9)
    (code : RatDrop.program (C := DropContext C) .halt point = RatDrop.fieldBody false point next)
    (digits : List Bool) (memory : RatOutput.Store) (tail : List Bool) :
    Segment caller
      (discardCfg second (RatDrop.state background point context memory
        (PSTRTMRawNat010.leftBlocks digits ++ false :: false :: tail) []))
      (discardCfg second (RatDrop.state background next context (true,false) tail []))
      (digits.length+2) := by
  let trace := RatDrop.fieldTrace false background context point next digits memory tail []
  have lifted := LabelMap.actual_path_on (discardLabel second) (RatDrop.program .halt) (program caller)
    trace _ _ (RatDrop.field_head _ _ _ _ _ _ _ _ _) (RatDrop.field_chain .halt _ _ _ _ _ code _ _ _ _)
    (RatDrop.field_last _ _ _ _ _ _ _ _ _) (by
      intro current member label selected
      have eqPoint := field_proper background context point next digits memory tail [] current member
      have same : label = point := Option.some.inj (selected.symm.trans eqPoint)
      subst label
      exact program_discard caller second point not9)
  refine ⟨trace.map (discardCfg second), lifted.1, lifted.2.1, ?_, ?_⟩
  · exact lifted.2.2.1
  · rw [List.length_map]
    exact (RatDrop.field_length _ _ _ _ _ _ _ _ _).le

def discard_packet (caller : Statement C) (second : Bool)
    (background : RatInput.Stack → List Bool) (context : DropContext C)
    (header numPoint denPoint next : RatDrop.Label) (not9 : header ≠ 9)
    (numNot9 : numPoint ≠ 9) (denNot9 : denPoint ≠ 9)
    (headerCode : RatDrop.program (C := DropContext C) .halt header = RatDrop.headerBody false numPoint)
    (numCode : RatDrop.program (C := DropContext C) .halt numPoint = RatDrop.fieldBody false numPoint denPoint)
    (denCode : RatDrop.program (C := DropContext C) .halt denPoint = RatDrop.fieldBody false denPoint next)
    (memory : RatOutput.Store) (negative : Bool) (num den tail : List Bool) :
    Segment caller
      (discardCfg second (RatDrop.state background header context memory
        (PSTRSymbolicRatExport.packet negative num den tail) []))
      (discardCfg second (RatDrop.state background next context (true,false) tail []))
      (num.length+den.length+6) := by
  let afterNum := PSTRTMRawNat010.leftBlocks den ++ false :: false :: tail
  let s0 := RatDrop.state background header context memory (PSTRSymbolicRatExport.packet negative num den tail) []
  let s1 := RatDrop.state background numPoint context (true,negative)
    (PSTRTMRawNat010.leftBlocks num ++ false :: false :: afterNum) []
  have edge := RatDrop.header_step (.halt : RatDrop.Statement (DropContext C)) false header numPoint
    headerCode background context memory negative
    (PSTRTMRawNat010.leftBlocks num ++ false :: false :: afterNum) []
  have mapped := LabelMap.step_configuration_on (discardLabel second) (RatDrop.program .halt)
    (program caller) s0 (by
      intro point selected
      have same : point = header := Option.some.inj selected.symm
      subst point
      exact program_discard caller second header not9)
  have headStep : TM2.step (program caller) (discardCfg second s0) = some (discardCfg second s1) := by
    change TM2.step (program caller) (LabelMap.configuration (discardLabel second) s0) = _
    rw [mapped]
    change (TM2.step (RatDrop.program .halt) s0).map _ = _
    rw [show TM2.step (RatDrop.program .halt) s0 = some s1 from edge]
    rfl
  let first : Segment caller (discardCfg second s0) (discardCfg second s1) 2 :=
    ⟨[discardCfg second s0, discardCfg second s1], rfl,
      List.isChain_cons_cons.mpr ⟨headStep, List.isChain_singleton _⟩, rfl, Nat.le_refl _⟩
  let middle := field_path caller second background context numPoint denPoint numNot9 numCode num (true,negative) afterNum
  let last := field_path caller second background context denPoint next denNot9 denCode den (true,false) tail
  let joined := (first.append middle).append last
  exact ⟨joined.trace, joined.head, joined.chain, joined.last, by have n := joined.count; omega⟩

end B23_4_RatWordPrep.SeqCmp
