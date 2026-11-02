module

public import Common.PSTR_WordBool_LocatedNative_038
public import Common.PSTR_SYM_FiniteRelabel_007

/-! Convert actual native head coordinates to the ORIGINAL visitedSpace
scan/fold, retaining the final HALT's zero displacement. Finite relabeling
preserves exactly the same tape, actual transitions, length and space. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedSpace

open Turing StatementDisplacement LocatedNative
open PaperProofs.Common.Native.RationalControllerComputation

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]

theorem halt_shift (machine : Λ → TM1.Stmt Bool Λ σ) (final : StatementClock.NativeState machine)
    (halt : TM0.step (TM1to0.tr machine) final = none) : shift machine final = 0 := by
  cases instruction : (TM1to0.tr machine) final.q final.Tape.head with
  | none => simp only [shift, instruction]
  | some next =>
    have impossible := halt
    simp only [TM0.step, instruction, Option.map_some] at impossible
    cases impossible

theorem source_displacement (machine : Λ → TM1.Stmt Bool Λ σ) :
    PSTRSymbolicRelabel.sourceDisplacement (TM1to0.tr machine) = shift machine := by
  funext state
  unfold PSTRSymbolicRelabel.sourceDisplacement shift
  cases instruction : (TM1to0.tr machine) state.q state.Tape.head with
  | none => rfl
  | some next =>
    obtain ⟨label, statement⟩ := next
    cases statement with
    | move direction => cases direction <;> rfl
    | write bit => rfl

theorem full_positions (machine : Λ → TM1.Stmt Bool Λ σ) (first final : LocatedNative.Located machine)
    (rest : List (LocatedNative.Located machine))
    (chain : (first :: rest).IsChain (LocatedNative.Step machine))
    (last : (first :: rest).getLast? = some final) (zeroFinal : shift machine final.1 = 0) :
    ((first :: rest).map (fun point => shift machine point.1)).scanl (· + ·) first.2 =
      (first :: rest).map Prod.snd ++ [final.2] := by
  induction rest generalizing first with
  | nil =>
    have same : first = final := Option.some.inj last
    subst first
    simp only [List.map_cons, List.map_nil, List.scanl_cons, zeroFinal, Int.add_zero,
      List.scanl_nil, List.cons_append, List.nil_append]
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    have later := ih next tailChain last
    simp only [List.map_cons, List.scanl_cons, List.cons_append]
    rw [← edge.2]
    simpa only [List.map_cons, List.scanl_cons, List.cons_append] using
      congrArg (List.cons first.2) later

theorem fold_max_le (values : List Int) (seed bound : Int)
    (initial : seed ≤ bound) (bounded : ∀ value ∈ values, value ≤ bound) :
    values.foldl max seed ≤ bound := by
  induction values generalizing seed with
  | nil => exact initial
  | cons first rest ih =>
    exact ih (max seed first) (max_le initial (bounded first List.mem_cons_self))
      (fun value present => bounded value (List.mem_cons_of_mem _ present))

theorem le_fold_min (values : List Int) (bound seed : Int)
    (initial : bound ≤ seed) (bounded : ∀ value ∈ values, bound ≤ value) :
    bound ≤ values.foldl min seed := by
  induction values generalizing seed with
  | nil => exact initial
  | cons first rest ih =>
    exact ih (min seed first) (le_min initial (bounded first List.mem_cons_self))
      (fun value present => bounded value (List.mem_cons_of_mem _ present))

theorem source_space_le (machine : Λ → TM1.Stmt Bool Λ σ)
    (first final : LocatedNative.Located machine) (rest : List (LocatedNative.Located machine))
    (chain : (first :: rest).IsChain (LocatedNative.Step machine))
    (last : (first :: rest).getLast? = some final)
    (halt : TM0.step (TM1to0.tr machine) final.1 = none)
    (origin : first.2 = 0) (inputLength : Nat) (low high : Int)
    (lowZero : low ≤ 0) (inputHigh : (inputLength : Int) ≤ high)
    (bounded : ∀ point ∈ first :: rest, low ≤ point.2 ∧ point.2 ≤ high) :
    PSTRSymbolicRelabel.sourceVisitedSpace (TM1to0.tr machine) inputLength
      ((first :: rest).map Prod.fst) ≤ (high - low).toNat + 1 := by
  let positions := (((first :: rest).map Prod.fst).map
    (PSTRSymbolicRelabel.sourceDisplacement (TM1to0.tr machine))).scanl (· + ·) 0
  have exactPositions : positions = (first :: rest).map Prod.snd ++ [final.2] := by
    dsimp only [positions]
    rw [source_displacement, List.map_map, ← origin]
    exact full_positions machine first final rest chain last (halt_shift machine final.1 halt)
  have positionBounds : ∀ position ∈ positions, low ≤ position ∧ position ≤ high := by
    intro position present
    rw [exactPositions] at present
    rcases List.mem_append.mp present with earlier | terminal
    · obtain ⟨point, member, same⟩ := List.mem_map.mp earlier
      subst position
      exact bounded point member
    · have same := List.mem_singleton.mp terminal
      subst position
      exact bounded final (List.mem_of_getLast? last)
  have highBound := fold_max_le positions (inputLength : Int) high inputHigh
    (fun position present => (positionBounds position present).2)
  have lowBound := le_fold_min positions low 0 lowZero
    (fun position present => (positionBounds position present).1)
  change ((positions.foldl max (inputLength : Int)) - positions.foldl min 0).toNat + 1 ≤ _
  have difference : positions.foldl max (inputLength : Int) - positions.foldl min 0 ≤ high - low := by omega
  exact Nat.add_le_add_right (Int.toNat_le_toNat difference) 1

theorem finite_computes_of_located (machine : Λ → TM1.Stmt Bool Λ σ)
    (support : Finset (TM1to0.Λ' machine))
    (closed : TM0.Supports (TM1to0.tr machine) (support : Set (TM1to0.Λ' machine)))
    (input output : List Bool) (time : Nat) (low high : Int)
    (first final : LocatedNative.Located machine) (rest : List (LocatedNative.Located machine))
    (initial : first = (TM0.init input, 0))
    (chain : (first :: rest).IsChain (LocatedNative.Step machine))
    (last : (first :: rest).getLast? = some final)
    (halt : TM0.step (TM1to0.tr machine) final.1 = none)
    (result : final.1.Tape.right₀ = ListBlank.mk output)
    (clock : (first :: rest).length ≤ time) (lowZero : low ≤ 0)
    (inputHigh : (input.length : Int) ≤ high)
    (bounded : ∀ point ∈ first :: rest, low ≤ point.2 ∧ point.2 ≤ high) :
    computes (PSTRSymbolicRelabel.finiteMachine (TM1to0.tr machine) support)
      input output time ((high - low).toNat + 1) := by
  have nativeChain : ((first :: rest).map Prod.fst).IsChain
      (fun before after => TM0.step (TM1to0.tr machine) before = some after) :=
    List.isChain_map_of_isChain Prod.fst (fun _ _ edge => edge.1) chain
  have nativeLast : ((first :: rest).map Prod.fst).getLast? = some final.1 := by
    rw [List.getLast?_map, last, Option.map_some]
  have nativeFirst : ((first :: rest).map Prod.fst).head? = some (TM0.init input) := by
    simp only [List.map_cons, List.head?_cons, initial]
  have origin : first.2 = 0 := congrArg Prod.snd initial
  exact PSTRSymbolicRelabel.finite_computes_of_trace (TM1to0.tr machine) support closed
    input output time ((high - low).toNat + 1) ((first :: rest).map Prod.fst) final.1
    nativeFirst nativeChain nativeLast halt result (by simpa only [List.length_map] using clock)
    (source_space_le machine first final rest chain last halt origin input.length low high lowZero inputHigh bounded)

end PaperProofs.Common.Native.PSTRWordBool.LocatedSpace
