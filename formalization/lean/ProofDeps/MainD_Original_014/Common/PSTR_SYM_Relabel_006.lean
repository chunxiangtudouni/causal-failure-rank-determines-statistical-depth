module

public import PaperProofs.Common.RationalControllerComputation
public import Mathlib.Data.List.Chain

/-! Actual TM0 state relabeling. The alphabet and whole tape stay Bool;
there is one target transition for each source transition, including HALT.
No interpreter, input conversion, allocator or symbolic compiler is supplied. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel

open Turing

variable {Λ : Type*} [Inhabited Λ] {states : Nat}

def boolIdentity : PointedMap Bool Bool := ⟨id, rfl⟩

def relabelCfg (labels : Λ → Fin (states + 1)) (state : TM0.Cfg Bool Λ) :
    MachineState states := ⟨labels state.q, state.Tape⟩

def relabelMachine (machine : TM0.Machine Bool Λ)
    (labels : Λ → Fin (states + 1)) (decode : Fin (states + 1) → Λ) : Machine states :=
  machine.map boolIdentity boolIdentity labels decode

theorem listBlank_identity (tape : ListBlank Bool) : tape.map boolIdentity = tape := by
  apply ListBlank.ext
  intro position
  simp [boolIdentity]

theorem tape_identity (tape : Tape Bool) : tape.map boolIdentity = tape := by
  cases tape with
  | mk head left right =>
    change Tape.mk head (left.map boolIdentity) (right.map boolIdentity) = Tape.mk head left right
    rw [listBlank_identity, listBlank_identity]

omit [Inhabited Λ] in
theorem cfg_map_identity (labels : Λ → Fin (states + 1)) (state : TM0.Cfg Bool Λ) :
    state.map boolIdentity labels = relabelCfg labels state := by
  cases state
  simp [TM0.Cfg.map, relabelCfg, tape_identity]

/-- This is Mathlib's actual one-step Option equality, specialized to the
identity alphabet. A label decoder is only required on the fixed support. -/
theorem relabel_step (machine : TM0.Machine Bool Λ) (support : Set Λ)
    (labels : Λ → Fin (states + 1)) (decode : Fin (states + 1) → Λ)
    (inverse : ∀ q ∈ support, decode (labels q) = q)
    (state : TM0.Cfg Bool Λ) (supported : state.q ∈ support) :
    (TM0.step machine state).map (relabelCfg labels) =
      TM0.step (relabelMachine machine labels decode) (relabelCfg labels state) := by
  have mapFunction : TM0.Cfg.map boolIdentity labels = relabelCfg labels :=
    funext (cfg_map_identity labels)
  simpa only [mapFunction, relabelMachine] using
    machine.map_step boolIdentity boolIdentity labels decode
      (by intro value; rfl) inverse state supported

theorem trace_supported (machine : TM0.Machine Bool Λ) (support : Set Λ)
    (closed : TM0.Supports machine support) (input : List Bool)
    (trace : List (TM0.Cfg Bool Λ))
    (first : trace.head? = some (TM0.init input))
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after)) :
    ∀ state ∈ trace, state.q ∈ support := by
  apply chain.induction (fun state => state.q ∈ support) trace
  · intro before after step present
    exact TM0.step_supports machine closed step present
  · intro nonempty
    have head : trace.head nonempty = TM0.init input := by
      simpa [List.head?_eq_some_head nonempty] using first
    rw [head]
    exact closed.1

/-- Generic-label version of the ORIGINAL displacement definition. -/
def sourceDisplacement (machine : TM0.Machine Bool Λ) (state : TM0.Cfg Bool Λ) : Int :=
  match machine state.q state.Tape.head with
  | some (_, .move .left) => -1
  | some (_, .move .right) => 1
  | _ => 0

/-- The same scan/fold visited-cell measure as the original B23 definition.
For finite original labels this is definitionally the original measure. -/
def sourceVisitedSpace (machine : TM0.Machine Bool Λ) (inputLength : Nat)
    (trace : List (TM0.Cfg Bool Λ)) : Nat :=
  let positions := (trace.map (sourceDisplacement machine)).scanl (· + ·) 0
  let high := positions.foldl max (inputLength : Int)
  let low := positions.foldl min 0
  (high - low).toNat + 1

theorem source_original_space {sourceStates : Nat} (machine : Machine sourceStates)
    (inputLength : Nat) (trace : List (MachineState sourceStates)) :
    sourceVisitedSpace machine inputLength trace = visitedSpace machine inputLength trace := by
  have projection : sourceDisplacement machine = displacement machine := by
    funext state
    unfold sourceDisplacement displacement
    cases machine state.q state.Tape.head with
    | none => rfl
    | some action =>
      obtain ⟨next, instruction⟩ := action
      cases instruction with
      | write symbol => rfl
      | move direction => cases direction <;> rfl
  unfold sourceVisitedSpace visitedSpace
  rw [projection]

theorem relabel_displacement (machine : TM0.Machine Bool Λ)
    (labels : Λ → Fin (states + 1)) (decode : Fin (states + 1) → Λ)
    (state : TM0.Cfg Bool Λ) (inverse : decode (labels state.q) = state.q) :
    displacement (relabelMachine machine labels decode) (relabelCfg labels state) =
      sourceDisplacement machine state := by
  unfold displacement relabelMachine TM0.Machine.map relabelCfg sourceDisplacement
  simp only [boolIdentity, inverse, id_eq]
  cases machine state.q state.Tape.head with
  | none => rfl
  | some action =>
    obtain ⟨next, instruction⟩ := action
    cases instruction with
    | write symbol => rfl
    | move direction => cases direction <;> rfl

theorem relabel_visitedSpace (machine : TM0.Machine Bool Λ) (support : Set Λ)
    (labels : Λ → Fin (states + 1)) (decode : Fin (states + 1) → Λ)
    (inverse : ∀ q ∈ support, decode (labels q) = q)
    (inputLength : Nat) (trace : List (TM0.Cfg Bool Λ))
    (supported : ∀ state ∈ trace, state.q ∈ support) :
    visitedSpace (relabelMachine machine labels decode) inputLength (trace.map (relabelCfg labels)) =
      sourceVisitedSpace machine inputLength trace := by
  have movements : (trace.map (relabelCfg labels)).map
      (displacement (relabelMachine machine labels decode)) = trace.map (sourceDisplacement machine) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro state present
    exact relabel_displacement machine labels decode state (inverse _ (supported _ present))
  unfold visitedSpace sourceVisitedSpace
  rw [movements]

/-- Four real source trace fields imply the ORIGINAL target Runs, including
its eval-membership field. HALT is transported, never replaced by a reset. -/
theorem relabel_runs (machine : TM0.Machine Bool Λ) (support : Set Λ)
    (closed : TM0.Supports machine support)
    (labels : PointedMap Λ (Fin (states + 1))) (decode : Fin (states + 1) → Λ)
    (inverse : ∀ q ∈ support, decode (labels q) = q)
    (input : List Bool) (trace : List (TM0.Cfg Bool Λ)) (final : TM0.Cfg Bool Λ)
    (first : trace.head? = some (TM0.init input))
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after))
    (last : trace.getLast? = some final) (halt : TM0.step machine final = none) :
    Runs (relabelMachine machine labels decode) input (trace.map (relabelCfg labels))
      (relabelCfg labels final) := by
  have supported := trace_supported machine support closed input trace first chain
  have finalSupported : final.q ∈ support := supported final (List.mem_of_getLast? last)
  have firstMapped : (trace.map (relabelCfg labels)).head? = some (TM0.init input) := by
    simp only [List.head?_map, first, Option.map_some]
    congr 1
    have mappedInitial := TM0.map_init boolIdentity labels input
    exact (cfg_map_identity labels _).symm.trans (by simpa [boolIdentity] using mappedInitial)
  have chainMapped : (trace.map (relabelCfg labels)).IsChain
      (fun before after => TM0.step (relabelMachine machine labels decode) before = some after) := by
    apply (List.isChain_map _).mpr
    apply chain.imp_of_mem_imp
    intro before after present _ step
    rw [← relabel_step machine support labels decode inverse before (supported _ present), step]
    rfl
  have lastMapped : (trace.map (relabelCfg labels)).getLast? = some (relabelCfg labels final) := by
    simp only [List.getLast?_map, last, Option.map_some]
  have haltMapped : TM0.step (relabelMachine machine labels decode) (relabelCfg labels final) = none := by
    rw [← relabel_step machine support labels decode inverse final finalSupported, halt]
    rfl
  refine ⟨firstMapped, chainMapped, lastMapped, haltMapped, ?_⟩
  apply StateTransition.mem_eval.mpr
  refine ⟨?_, haltMapped⟩
  cases mapped : trace.map (relabelCfg labels) with
  | nil => simp [mapped] at firstMapped
  | cons initial rest =>
    have initialEq : initial = TM0.init input := by simpa [mapped] using firstMapped
    have finalEq : (initial :: rest).getLast (by simp) = relabelCfg labels final := by
      exact List.getLast_of_getLast?_eq_some (by simpa only [mapped] using lastMapped)
    subst initial
    exact List.relationReflTransGen_of_exists_isChain_cons rest
      (by simpa [mapped] using chainMapped) finalEq

/-- Relabeling an ORIGINAL finite-label computation preserves all original
input/output, time and space budgets EXACTLY; the maps are fixed before input. -/
theorem computes_relabel {sourceStates : Nat} (machine : Machine sourceStates) (support : Set (Fin (sourceStates + 1)))
    (closed : TM0.Supports machine support)
    (labels : PointedMap (Fin (sourceStates + 1)) (Fin (states + 1)))
    (decode : Fin (states + 1) → Fin (sourceStates + 1))
    (inverse : ∀ q ∈ support, decode (labels q) = q)
    (input output : List Bool) (time space : Nat)
    (actual : computes machine input output time space) :
    computes (relabelMachine machine labels decode) input output time space := by
  obtain ⟨trace, final, run, result, clock, cells⟩ := actual
  refine ⟨trace.map (relabelCfg labels), relabelCfg labels final,
    relabel_runs machine support closed labels decode inverse input trace final
      run.1 run.2.1 run.2.2.1 run.2.2.2.1, result, ?_, ?_⟩
  · simpa using clock
  · rw [relabel_visitedSpace machine support labels decode inverse input.length trace
      (trace_supported machine support closed input trace run.1 run.2.1)]
    rw [source_original_space]
    exact cells

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel
