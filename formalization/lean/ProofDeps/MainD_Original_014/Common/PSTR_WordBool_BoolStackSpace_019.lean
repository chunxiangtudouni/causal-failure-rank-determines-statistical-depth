module

public import Common.PSTR_WordBool_BoolStackRange_018

/-! Actual source work-stack occupancy from the SAME original visitedSpace.
The source starts with exact empty L and exact original input R. No length
certificate is inferred merely from Tape equality or elapsed time. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackSpace

open Turing BoolOnStacks BoolStackTrace BoolStackRange
open PaperProofs.Common.Native.RationalControllerComputation (displacement visitedSpace)

theorem all_left {α β : Type*} (relation : α → β → Prop) (property : α → Prop)
    {left : List α} {right : List β} (certificate : List.Forall₂ relation left right)
    (implies : ∀ item point, relation item point → property item) :
    ∀ item ∈ left, property item := by
  induction certificate with
  | nil => simp
  | cons edge tail ih =>
    intro item present
    rcases List.mem_cons.mp present with same | later
    · subst item
      exact implies _ _ edge
    · exact ih item later

variable {states : Nat}

theorem same_old_run (machine : TM0.Machine Bool (Fin (states + 1)))
    (input : List Bool) (oldTrace : List (TM0.Cfg Bool (Fin (states + 1))))
    (oldFinal : TM0.Cfg Bool (Fin (states + 1)))
    (first : oldTrace.head? = some (TM0.init input))
    (chain : oldTrace.IsChain (fun before after => TM0.step machine before = some after))
    (last : oldTrace.getLast? = some oldFinal) (halt : TM0.step machine oldFinal = none) :
    ∃ (trace : List (BoolOnStacks.State states)) (final : BoolOnStacks.State states),
      trace.head? = some (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := Store states) 0 input) ∧
      trace.IsChain (fun before after => TM2.step (program machine) before = some after) ∧
      trace.getLast? = some final ∧ TM2.step (program machine) final = none ∧
      representedState final = oldFinal ∧
      trace.map representedState = oldTrace ++ [oldFinal] ∧
      trace.length = oldTrace.length + 1 ∧
      ∀ state ∈ trace, (state.stk 1).length + (state.stk 0).length ≤
        visitedSpace machine input.length oldTrace := by
  cases oldTrace with
  | nil => simp at first
  | cons oldStart rest =>
    have initial : oldStart = TM0.init input := Option.some.inj first
    subst oldStart
    let start : BoolOnStacks.State states := TM2.init 0 input
    let lower := VisitedExtrema.low machine (TM0.init input :: rest)
    let upper := VisitedExtrema.high machine input.length (TM0.init input :: rest)
    have seeds := VisitedExtrema.seed_bounds machine input.length (TM0.init input :: rest)
    have leftLength : (start.stk 1).length = 0 := rfl
    have rightLength : (start.stk 0).length = input.length := rfl
    have initialGeometry : Geometry lower upper 0 start := by
      dsimp only [Geometry]
      rw [leftLength, rightLength]
      constructor <;> omega
    have ranges : ∀ point ∈ ((TM0.init input :: rest).map (displacement machine)).scanl (· + ·) 0,
        lower ≤ point ∧ point ≤ upper := by
      intro point present
      exact VisitedExtrema.position_bounds machine input.length (TM0.init input :: rest) point present
    obtain ⟨trace, final, sourceFirst, sourceChain, sourceLast, sourceHalt,
      finalRepresentation, mapping, geometry⟩ := synchronized_path machine start
        (TM0.init input) oldFinal rest 0 lower upper rfl (BoolOnStacks.initial_map input)
        chain last halt initialGeometry ranges
    have nonnegative : 0 ≤ upper - lower :=
      VisitedExtrema.range_nonnegative machine input.length (TM0.init input :: rest)
    have occupied : ∀ state ∈ trace, (state.stk 1).length + (state.stk 0).length ≤
        visitedSpace machine input.length (TM0.init input :: rest) := by
      refine all_left (fun state point => Geometry lower upper point state)
        (fun state => (state.stk 1).length + (state.stk 0).length ≤
          visitedSpace machine input.length (TM0.init input :: rest)) geometry ?_
      intro state point within
      change (state.stk 1).length + (state.stk 0).length ≤ (upper - lower).toNat + 1
      exact StackGeometry.mass_of_range point lower upper _ _ within.1 within.2 nonnegative
    refine ⟨trace, final, sourceFirst, sourceChain, sourceLast, sourceHalt,
      finalRepresentation, mapping, ?_, occupied⟩
    have lengths := congrArg List.length mapping
    simpa only [List.length_map, List.length_append, List.length_cons, List.length_nil] using lengths

end PaperProofs.Common.Native.PSTRWordBool.BoolStackSpace
