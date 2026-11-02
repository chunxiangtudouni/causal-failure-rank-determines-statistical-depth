module

public import Common.PSTR_SYM_Relabel_006
public import Mathlib.Data.Fintype.EquivFin

/-! A fixed finite support supplies all label-map obligations of 006.
The finite table is chosen once, before the input. This is a mathematical
state-code choice, not a claimed time-bounded compiler for machine descriptions. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel

open Turing

variable {Λ : Type*} [Inhabited Λ]

/-- Reserve target label zero for the genuine source initial label. -/
noncomputable def finiteLabels (support : Finset Λ) : PointedMap Λ (Fin (support.card + 1)) := by
  classical
  exact ⟨fun q => if q = default then 0 else
    if present : q ∈ support then (support.equivFin ⟨q, present⟩).succ else 0, by simp⟩

noncomputable def finiteDecode (support : Finset Λ) : Fin (support.card + 1) → Λ :=
  Fin.cases default (fun label => (support.equivFin.symm label).val)

theorem finite_inverse (support : Finset Λ) (q : Λ) (present : q ∈ support) :
    finiteDecode support (finiteLabels support q) = q := by
  classical
  by_cases initial : q = default
  · subst q
    simp [finiteLabels, finiteDecode]
  · simp [finiteLabels, finiteDecode, initial, present]

/-- Actual Bool TM0 machine with finitely many labels. Source support and
the code table are fixed before every runtime input; no tape conversion occurs. -/
noncomputable def finiteMachine (machine : TM0.Machine Bool Λ) (support : Finset Λ) :
    Machine support.card :=
  relabelMachine machine (finiteLabels support) (finiteDecode support)

theorem finite_runs (machine : TM0.Machine Bool Λ) (support : Finset Λ)
    (closed : TM0.Supports machine (support : Set Λ))
    (input : List Bool) (trace : List (TM0.Cfg Bool Λ)) (final : TM0.Cfg Bool Λ)
    (first : trace.head? = some (TM0.init input))
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after))
    (last : trace.getLast? = some final) (halt : TM0.step machine final = none) :
    Runs (finiteMachine machine support) input (trace.map (relabelCfg (finiteLabels support)))
      (relabelCfg (finiteLabels support) final) :=
  relabel_runs machine support closed (finiteLabels support) (finiteDecode support)
    (finite_inverse support) input trace final first chain last halt

theorem finite_visitedSpace (machine : TM0.Machine Bool Λ) (support : Finset Λ)
    (closed : TM0.Supports machine (support : Set Λ))
    (input : List Bool) (trace : List (TM0.Cfg Bool Λ))
    (first : trace.head? = some (TM0.init input))
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after)) :
    visitedSpace (finiteMachine machine support) input.length
        (trace.map (relabelCfg (finiteLabels support))) = sourceVisitedSpace machine input.length trace :=
  relabel_visitedSpace machine support (finiteLabels support) (finiteDecode support)
    (finite_inverse support) input.length trace (trace_supported machine support closed input trace first chain)

/-- Same original output, same actual trace length, same original space.
The source can have an infinite label type but must have a fixed finite support.
This theorem supplies no source execution or source complexity bound. -/
theorem finite_computes_of_trace (machine : TM0.Machine Bool Λ) (support : Finset Λ)
    (closed : TM0.Supports machine (support : Set Λ))
    (input output : List Bool) (time space : Nat)
    (trace : List (TM0.Cfg Bool Λ)) (final : TM0.Cfg Bool Λ)
    (first : trace.head? = some (TM0.init input))
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after))
    (last : trace.getLast? = some final) (halt : TM0.step machine final = none)
    (result : final.Tape.right₀ = ListBlank.mk output)
    (clock : trace.length ≤ time) (cells : sourceVisitedSpace machine input.length trace ≤ space) :
    computes (finiteMachine machine support) input output time space := by
  refine ⟨trace.map (relabelCfg (finiteLabels support)), relabelCfg (finiteLabels support) final,
    finite_runs machine support closed input trace final first chain last halt, result, ?_, ?_⟩
  · simpa using clock
  · rw [finite_visitedSpace machine support closed input trace first chain]
    exact cells

theorem finite_computes {sourceStates : Nat} (machine : Machine sourceStates)
    (support : Finset (Fin (sourceStates + 1)))
    (closed : TM0.Supports machine (support : Set (Fin (sourceStates + 1))))
    (input output : List Bool) (time space : Nat)
    (actual : computes machine input output time space) :
    computes (finiteMachine machine support) input output time space :=
  computes_relabel machine support closed (finiteLabels support) (finiteDecode support)
    (finite_inverse support) input output time space actual

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel
