module
public import Structure.PA17_TM_RatArithmetic_OutputFinish_044b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044

open Turing
open PA17TMDivisionCompose006
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticFinalClean039

theorem outputCap_eq (j : Nat) : outputCap j=144*j+467 := by
  simp only [outputCap,totalStates,tailCap,finalCap_eq]
  omega

theorem outputFinish_contract (j : Nat) (negative : Bool) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail : List Bool)
    (gap : Nat) (hgap : 3≤gap) (u v : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (outputFinishMachine j)
        ⟨outputEntry j negative,pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
        ⟨outputPort j,Tape.mk₁ (physicalWord negative u v)⟩ ∧
      trace.length≤outputFee j first later nx dxTail ny dyTail gap u v ∧
      ∀ prefixLength chargedL, visitedSpace (outputFinishMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*outputFee j first later nx dxTail ny dyTail gap u v+1 := by
  obtain ⟨trace,hr,hl⟩ := outputFinish_bounded j negative first later hj sx nx dxTail ny dyTail gap hgap u v
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (outputFinishMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

theorem physicalWord_canonical (q : Rat) :
    physicalWord (decide (q<0)) q.num.natAbs q.den=encode [.rational q] :=
  PA17TMRatArithmeticPrefix020.prefix_canonical_word q

/-- This only links an ACTUALLY PRODUCED U/V tape and ACTUALLY SELECTED
control entry to the canonical codec. Their facts come from real arithmetic
and sign-controller runs; no answer/sign is added to the original input. -/
theorem outputFinish_canonical_contract (j : Nat) (negative : Bool)
    (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j) (sx : Bool)
    (nx dxTail ny dyTail : List Bool) (gap : Nat) (hgap : 3≤gap) (u v : Nat) (q : Rat)
    (hu : u=q.num.natAbs) (hv : v=q.den) (hsign : negative=decide (q<0)) :
    ∃ trace, PSTRTMSeq005.RunsFrom (outputFinishMachine j)
        ⟨outputEntry j negative,pairInput gap (latestLeft sx nx dxTail ny dyTail first later) u v⟩ trace
        ⟨outputPort j,Tape.mk₁ (encode [.rational q])⟩ ∧
      trace.length≤outputFee j first later nx dxTail ny dyTail gap u v ∧
      ∀ prefixLength chargedL, visitedSpace (outputFinishMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*outputFee j first later nx dxTail ny dyTail gap u v+1 := by
  have hw : physicalWord negative u v=encode [.rational q] := by
    rw [hu,hv,hsign]
    exact physicalWord_canonical q
  obtain ⟨trace,hr,hl,hspace⟩ := outputFinish_contract j negative first later hj sx nx dxTail ny dyTail gap hgap u v
  rw [hw] at hr
  exact ⟨trace,hr,hl,hspace⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOutputFinish044
