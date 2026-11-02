module

public import Paid.PDROC_D27Prepare_Assembly_001
public import Paid.PDROC_D27Prepare_Dyadic_005
public import Paid.PDROC_D27Prepare_Tail_009
public import Paid.PDROC_D27Prepare_J_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

theorem search_to_preFinal_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : Search.SearchFinished P fee before) (empty : before.output = [])
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), PreFinalState P fee after ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      trace.length ≤ 400 + 129 * P.certificate.stages + 29 * P.bisectionBudget fee ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) := by
  obtain ⟨beforeZeta, lambdaTrace, lambdaPc, lambda, power, lambdaOutput, lambdaFresh,
    lambdaHead, lambdaLast, lambdaChain, lambdaLength, lambdaBounds, lambdaCarry⟩ :=
    Dyadic.original_lambda_trace P fee input before initial bounded
  have raw24 := raw_of_slots P fee before beforeZeta initial.raw lambdaFresh
    (by
      intro address read value old
      apply lambdaCarry address _ value old
      simp only [Dyadic.region, Finset.mem_insert, Finset.mem_singleton]
      omega)
  let memory24 := Search.currentMemory beforeZeta
  have matched24 : MemoryMatch beforeZeta memory24 := Search.currentMemory_match beforeZeta raw24.fresh
  have rawHas (address : ℕ) (value : Cell) (stored : Search.SlotHas beforeZeta address value) : Has memory24 address value :=
    has_of_match beforeZeta memory24 address value matched24 stored
  obtain ⟨beforeJ, memory32, matched32, zeta, zetaPc, zetaSegment⟩ := Tail.original_zeta_segment P fee input
    beforeZeta memory24 matched24 lambdaPc (lambdaBounds beforeZeta (List.mem_of_getLast? lambdaLast))
    (rawHas 0 _ raw24.stages) (rawHas 1 _ raw24.tools) (rawHas 5 _ raw24.feeValue)
    (rawHas 13 _ raw24.natZero) (rawHas 14 _ raw24.natOne) (rawHas 16 _ raw24.ratZero)
    (rawHas 17 _ raw24.ratOne) (rawHas 39 _ power)
  have raw32 := raw_of_slots P fee beforeZeta beforeJ raw24 zetaSegment.fresh
    (by
      intro address read value old
      apply Q.MemoryProgress.slot zetaSegment.final_frame address _ value old
      simp only [Tail.binomialRegion, Finset.mem_insert, Finset.mem_singleton]
      omega)
  have lambda32 := Q.MemoryProgress.slot zetaSegment.final_frame 11 (by decide) _ lambda
  have zeta32 := match_has beforeJ memory32 12 _ matched32 zeta
  obtain ⟨after, jTrace, jPc, jValue, jOutput, jFresh, jHead, jLast, jChain,
    jLength, jBounds, jCarry⟩ := J.original_budget_trace P fee input beforeJ raw32 zetaPc
      zetaSegment.final_bounds lambda32 zeta32
  have raw45 := raw_of_slots P fee beforeJ after raw32 jFresh
    (by
      intro address read value old
      apply jCarry address _ value old
      simp only [J.region, Finset.mem_insert, Finset.mem_singleton]
      omega)
  have carry (address : ℕ) (outsideDyadic : address ∉ Dyadic.region)
      (outsideZeta : address ∉ Tail.binomialRegion) (outsideJ : address ∉ J.region)
      (value : Cell) (old : Search.SlotHas before address value) : Search.SlotHas after address value :=
    jCarry address outsideJ value (Q.MemoryProgress.slot zetaSegment.final_frame address outsideZeta value
      (lambdaCarry address outsideDyadic value old))
  have cells : PreparedMemory P fee after := preparedMemory_of_fields P fee after raw45
    (carry 6 (by decide) (by decide) (by decide) _ initial.t0)
    (carry 7 (by decide) (by decide) (by decide) _ initial.M)
    (carry 8 (by decide) (by decide) (by decide) _ initial.E)
    (carry 9 (by decide) (by decide) (by decide) _ initial.Q) jValue
    (jCarry 11 (by decide) _ lambda32) (jCarry 12 (by decide) _ zeta32)
  have output : after.output = [] := jOutput.trans (zetaSegment.output.trans (lambdaOutput.trans empty))
  have preFinal : PreFinalState P fee after :=
    ⟨jPc, output, raw45.fresh, cells, jBounds after (List.mem_of_getLast? jLast)⟩
  obtain ⟨zetaTrace, zetaHead, zetaLast, zetaChain, zetaLength, zetaBounds, _⟩ := zetaSegment.witness
  let middle := joinTrace lambdaTrace zetaTrace
  have middleHead := joinTrace_head lambdaTrace zetaTrace before beforeZeta lambdaHead lambdaLast zetaHead
  have middleLast := joinTrace_last lambdaTrace zetaTrace beforeJ zetaLast
  have middleChain := joinTrace_chain program input lambdaTrace zetaTrace beforeZeta lambdaChain zetaChain lambdaLast zetaHead
  have middleBounds : ∀ state ∈ middle, StateBounds 64 (operandBudget P fee) state := by
    intro state member
    rcases List.mem_append.mp member with early | late
    · exact lambdaBounds state (List.mem_of_mem_dropLast early)
    · exact zetaBounds state late
  refine ⟨after, joinTrace middle jTrace, preFinal,
    joinTrace_head middle jTrace before beforeJ middleHead middleLast jHead,
    joinTrace_last middle jTrace after jLast,
    joinTrace_chain program input middle jTrace beforeJ middleChain jChain middleLast jHead, ?_, ?_⟩
  · simp only [middle, joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact middleBounds state (List.mem_of_mem_dropLast early)
    · exact jBounds state late

end PDROC.D27Prepare.Assembly
