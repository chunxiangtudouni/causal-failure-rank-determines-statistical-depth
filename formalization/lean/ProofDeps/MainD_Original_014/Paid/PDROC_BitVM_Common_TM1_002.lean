module

public import Paid.PDROC_BitVM_Common_Trace_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.BitVM.Common

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool

variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

/-- Store values belong to a fixed finite type. Unbounded runtime words,
addresses, rationals and widths must remain actual Bool tape data. -/
noncomputable def tm1NativeSupport (machine : Λ → TM1.Stmt Bool Λ σ)
    (support : Finset Λ) : Finset (TM1to0.Λ' machine) :=
  TM1to0.trStmts machine support

/-- One fixed finite Bool machine, chosen from code and closed support
before any input or source execution is supplied. -/
noncomputable def tm1BitMachine (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ) :
    BitMachine (tm1NativeSupport machine support).card :=
  PSTRSymbolicRelabel.finiteMachine (TM1to0.tr machine) (tm1NativeSupport machine support)

theorem tm1NativeSupport_closed (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) :
    TM0.Supports (TM1to0.tr machine) (tm1NativeSupport machine support : Set (TM1to0.Λ' machine)) :=
  TM1to0.tr_supports machine closed

/-- A conditional compiler theorem for a genuine source path. The SAME
actual compiled path carries full final Tape, true HALT, original BitRuns,
time and visited space. It supplies no source interpreter or raw6 result. -/
theorem tm1_actual_bit_trace (machine : Λ → TM1.Stmt Bool Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) (input : List Bool)
    (sourceTrace : List (TM1.Cfg Bool Λ σ)) (sourceFinal : TM1.Cfg Bool Λ σ)
    (first : sourceTrace.head? = some (TM1.init input))
    (chain : sourceTrace.IsChain (fun before after => TM1.step machine before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM1.step machine sourceFinal = none) :
    ∃ trace final,
      BitRuns (tm1BitMachine machine support) input trace final ∧
      final.Tape = sourceFinal.Tape ∧
      trace.length ≤ SupportClock.clock machine support * sourceTrace.length + 1 ∧
      visitedBitSpace (tm1BitMachine machine support) input.length trace ≤
        input.length + 2 * (SupportClock.clock machine support * sourceTrace.length + 1) + 1 := by
  obtain ⟨nativeTrace, nativeFirst, nativeChain, nativeLast, nativeHalt, nativeBound⟩ :=
    SupportClock.actual_native_trace machine support closed input sourceTrace sourceFinal first chain last halt
  let labels := PSTRSymbolicRelabel.finiteLabels (tm1NativeSupport machine support)
  let final := PSTRSymbolicRelabel.relabelCfg labels (TM1to0.trCfg machine sourceFinal)
  let trace := nativeTrace.map (PSTRSymbolicRelabel.relabelCfg labels)
  have actual := PSTRSymbolicRelabel.finite_runs (TM1to0.tr machine)
    (tm1NativeSupport machine support) (tm1NativeSupport_closed machine support closed)
    input nativeTrace (TM1to0.trCfg machine sourceFinal) nativeFirst nativeChain nativeLast nativeHalt
  have bounded : trace.length ≤ SupportClock.clock machine support * sourceTrace.length + 1 := by
    simpa only [trace, List.length_map] using nativeBound
  refine ⟨trace, final, ?_, rfl, bounded, ?_⟩
  · exact (Link.CodecCandidate.bitRuns_iff_neutral _ _ _ _).mpr actual
  · exact visitedBitSpace_of_clock (tm1BitMachine machine support) input.length trace _ bounded

end PDROC.BitVM.Common
