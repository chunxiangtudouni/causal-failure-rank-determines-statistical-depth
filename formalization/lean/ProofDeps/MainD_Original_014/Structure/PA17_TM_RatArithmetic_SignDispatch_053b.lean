module
public import Structure.PA17_TM_RatArithmetic_SignDispatch_053a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignDispatch053
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticOutputFinish044
attribute [local implicit_reducible] outputCap dispatchCap

/-- The output trace is lifted into the ONE common phase, independent
of the incoming memory and of the already-observed sign-table value. -/
theorem body_runsFrom (j : Nat) (signTable : Fin 128→Bool)
    (first last : MachineState (outputCap j)) (trace : List (MachineState (outputCap j)))
    (run : PSTRTMSeq005.RunsFrom (outputFinishMachine j) first trace last) :
    PSTRTMSeq005.RunsFrom (dispatchMachine j signTable)
      (bodyState j first.q first.Tape) (trace.map (blockCfg (s:=outputCap j) (128 : Fin 129)))
      (bodyState j last.q last.Tape) := by
  have hf : PSTRTMSeq005.RunsFrom (dispatchFamily j (128 : Fin 129)) first trace last := by
    rw [family_body]
    exact run
  exact block_runsFrom (dispatchFamily j) (dispatchPorts j signTable) (128 : Fin 129) _ _ _ hf
    (ports_body j signTable _)

theorem dispatch_contract (j : Nat) (signTable : Fin 128→Bool) (memory : Fin 128)
    (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (nx dxTail ny dyTail : List Bool) (gap : Nat) (hgap : 3≤gap) (u v : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (dispatchMachine j signTable)
      ⟨dispatchEntry j memory,pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
      ⟨dispatchPort j,Tape.mk₁ (physicalWord (signTable memory) u v)⟩ ∧
      trace.length≤1+outputFee j first later nx dxTail ny dyTail gap u v ∧
      ∀ prefixLength chargedL, visitedSpace (dispatchMachine j signTable) chargedL (trace.take prefixLength)≤
        chargedL+2*(1+outputFee j first later nx dxTail ny dyTail gap u v)+1 := by
  let input := pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v
  obtain ⟨tailTrace,hr,ht⟩ := outputFinish_bounded j (signTable memory) first later hj sx nx dxTail ny dyTail gap hgap u v
  have hl := body_runsFrom j signTable _ _ _ hr
  let tailGlobal : List (MachineState (dispatchCap j)) := tailTrace.map (blockCfg (s:=outputCap j) (128 : Fin 129))
  have initial : Segment (dispatchMachine j signTable) (entryState j memory input)
      [entryState j memory input] (entryState j memory input) := ⟨rfl,by simp,rfl⟩
  have tailSegment : Segment (dispatchMachine j signTable) _ tailGlobal _ := ⟨hl.1,hl.2.1,hl.2.2.1⟩
  have combined := segment_append (dispatchMachine j signTable) _ _ _ _ [entryState j memory input] tailGlobal
    initial tailSegment (dispatch_step j signTable memory input)
  have full := segment_runsFrom (dispatchMachine j signTable) _ _ _ combined hl.2.2.2
  let trace := [entryState j memory input]++tailGlobal
  have length : trace.length=1+tailTrace.length := by simp only [trace,tailGlobal,List.length_append,List.length_singleton,List.length_map]
  have time : trace.length≤1+outputFee j first later nx dxTail ny dyTail gap u v := by rw [length];omega
  refine ⟨trace,full,time,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (dispatchMachine j signTable) chargedL (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

/-- This is an INTERNAL produced-resident/control contract. The native
producer proves hu/hv and the real058 observation proves hsign. They are
not extra inputs or qualifications of an original rational operation. -/
theorem dispatch_canonical_contract (j : Nat) (signTable : Fin 128→Bool) (memory : Fin 128)
    (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (nx dxTail ny dyTail : List Bool) (gap : Nat) (hgap : 3≤gap)
    (u v : Nat) (q : Rat) (hu : u=q.num.natAbs) (hv : v=q.den)
    (hsign : signTable memory=decide (q<0)) :
    ∃ trace, PSTRTMSeq005.RunsFrom (dispatchMachine j signTable)
      ⟨dispatchEntry j memory,pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
      ⟨dispatchPort j,Tape.mk₁ (encode [.rational q])⟩ ∧
      trace.length≤1+outputFee j first later nx dxTail ny dyTail gap u v ∧
      ∀ prefixLength chargedL, visitedSpace (dispatchMachine j signTable) chargedL (trace.take prefixLength)≤
        chargedL+2*(1+outputFee j first later nx dxTail ny dyTail gap u v)+1 := by
  have word : physicalWord (signTable memory) u v=encode [.rational q] := by
    rw [hu,hv,hsign]
    exact physicalWord_canonical q
  obtain ⟨trace,hr,ht,hs⟩ := dispatch_contract j signTable memory first later hj sx nx dxTail ny dyTail gap hgap u v
  rw [word] at hr
  exact ⟨trace,hr,ht,hs⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignDispatch053
