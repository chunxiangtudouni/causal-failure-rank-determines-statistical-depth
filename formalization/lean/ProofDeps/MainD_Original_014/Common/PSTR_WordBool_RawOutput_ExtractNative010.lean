module

public import Common.PSTR_WordBool_RawOutput_Loop009

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

noncomputable def extractSupport : Finset (TM1to0.Λ' Extract.sourceMachine) :=
  TM1to0.trStmts Extract.sourceMachine Finset.univ

noncomputable def extractStates : Nat := extractSupport.card

noncomputable def extractMachine : Machine extractStates :=
  PSTRSymbolicRelabel.finiteMachine (TM1to0.tr Extract.sourceMachine) extractSupport

noncomputable def extractBudget : Nat := SupportClock.clock Extract.sourceMachine Finset.univ
noncomputable def extractCoefficient : Nat := 32*(extractBudget+1)

noncomputable def extractHalt : Fin (extractStates+1) :=
  PSTRSymbolicRelabel.finiteLabels extractSupport (none,())

/-- The actual fixed finite Bool table expands every scan/move/write/goto
and HALT of the eleven-label source, on the same retained physical tape. -/
theorem extract_contract (bits : List Bool) :
    ∃ trace final, RunsFrom extractMachine
      ⟨0,Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) bits)⟩ trace final ∧
      final.q=extractHalt ∧
      final.Tape=Tape.mk₁ (PSTRTMIncrement009.blocks bits) ∧
      trace.length ≤ extractCoefficient*(bits.length+1)^2 := by
  let input := FiniteTrackCodec.encodedInput (0 : Fin 16) bits
  obtain ⟨sourceRest,sourceChain,sourceLast,sourceClock⟩ := Extract.source_path bits
  let sourceTrace := TM1.init (Γ := Bool) (Λ := Extract.Label) (σ := Unit) input :: sourceRest
  obtain ⟨native,first,chain,last,halt,clock⟩ := SupportClock.actual_native_trace
    Extract.sourceMachine Finset.univ Extract.source_closed input sourceTrace (Extract.finishCfg bits)
      rfl sourceChain sourceLast rfl
  let final := TM1to0.trCfg Extract.sourceMachine (Extract.finishCfg bits)
  have closed := TM1to0.tr_supports Extract.sourceMachine Extract.source_closed
  have actual := PSTRSymbolicRelabel.finite_runs (TM1to0.tr Extract.sourceMachine)
    extractSupport closed input native final first chain last halt
  refine ⟨native.map (PSTRSymbolicRelabel.relabelCfg (PSTRSymbolicRelabel.finiteLabels extractSupport)),
    PSTRSymbolicRelabel.relabelCfg (PSTRSymbolicRelabel.finiteLabels extractSupport) final,
      ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,rfl,rfl,?_⟩
  have sourceBound : sourceTrace.length ≤ 16*(bits.length+1)^2 := by
    simp only [sourceTrace,List.length_cons,sourceClock]
    nlinarith
  have times := Nat.mul_le_mul_left extractBudget sourceBound
  have square : 1 ≤ (bits.length+1)^2 := by nlinarith
  change native.length ≤ extractBudget*sourceTrace.length+1 at clock
  simp only [List.length_map]
  change native.length ≤ 32*(extractBudget+1)*(bits.length+1)^2
  nlinarith [Nat.zero_le (extractBudget*(bits.length+1)^2)]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput
