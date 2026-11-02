module
public import Structure.PA17_TM_RatArithmetic_NativeRecord_022a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022

open Turing

/-- Composition of genuine INTERNAL contracts: an already proved native
rawNat run, an actual produced blank window, and the frozen record writer.
The machine takes neither result n nor budget/slack as original input fields.
No original Rat machine is claimed until its real caller supplies this window. -/
theorem record_runsFrom {states : Nat} (machine : Machine states)
    (input : List Bool) (original : List (MachineState states)) (final : MachineState states)
    (n budget slack : Nat) (run : Runs machine input original final)
    (whole : final.Tape=Tape.mk₁ (encodeNat n))
    (timeBound : original.length≤budget)
    (inputBound : input.length≤slack) (outputBound : (encodeNat n).length≤slack)
    (reserve : 2≤slack) (archive : List Bool) :
    ∃ (left right : Nat) (trace : List (MachineState (5+(states+27+1)+1)))
        (last : MachineState (5+(states+27+1)+1)),
      PSTRTMSeq005.RunsFrom (recordMachine machine)
        (recordFirst machine (budget+slack) archive input) trace last ∧
      last.Tape=Tape.mk₂
        (PA17TMRatArithmeticStore019.recordLeft (List.replicate (left-2) false++archive) n) [true] ∧
      slack≤left ∧ slack≤right ∧ left+right=2*(budget+slack) ∧
      trace.length≤budget+32*(natBits n+1)^2+6 ∧
      ∀ prefixLength inputLength,
        visitedSpace (recordMachine machine) inputLength (trace.take prefixLength) ≤
          inputLength+2*(budget+32*(natBits n+1)^2+6)+1 := by
  obtain ⟨left,right,framed,framedRun,hl,hr,framedTime,_hmap,hsum,_hspace⟩ :=
    PA17TMRatArithmeticNatDivCall011.budget_framed machine input (encodeNat n)
      original final run whole budget slack timeBound inputBound outputBound archive []
  let nativeLast : MachineState states :=
    ⟨final.q,Tape.mk₂ (List.replicate left false++archive) (encodeNat n)⟩
  have nativeRun : PSTRTMSeq005.RunsFrom machine
      ⟨0,Tape.mk₂ (List.replicate (budget+slack) false++archive) input⟩ framed nativeLast := by
    simpa only [right_blank_reserve] using framedRun
  let recordArchive := List.replicate (left-2) false++archive
  have outputLeft : false::false::recordArchive = List.replicate left false++archive :=
    two_false_reserve left (by omega) archive
  have storeRun : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticStore019.storeMachine
      ⟨0,nativeLast.Tape⟩ (PA17TMRatArithmeticStore019.storeTrace recordArchive n)
      (PA17TMRatArithmeticStore019.storeFinal recordArchive n) := by
    simpa only [nativeLast,outputLeft] using PA17TMRatArithmeticStore019.store_runsFrom recordArchive n
  let innerTrace := framed.map (PSTRTMSeq005.leftCfg (b:=27)) ++
    (PA17TMRatArithmeticStore019.storeTrace recordArchive n).map (PSTRTMSeq005.rightCfg (a:=states))
  let innerLast := PSTRTMSeq005.rightCfg (a:=states)
    (PA17TMRatArithmeticStore019.storeFinal recordArchive n)
  have rawRun := PSTRTMSeq005.seq_runsFrom machine PA17TMRatArithmeticStore019.storeMachine
    ⟨0,Tape.mk₂ (List.replicate (budget+slack) false++archive) input⟩ nativeLast
    (PA17TMRatArithmeticStore019.storeFinal recordArchive n) framed
    (PA17TMRatArithmeticStore019.storeTrace recordArchive n) nativeRun storeRun
  let beforeArchive := List.replicate (budget+slack-2) false++archive
  have inputLeft : false::false::beforeArchive = List.replicate (budget+slack) false++archive :=
    two_false_reserve (budget+slack) (by omega) archive
  have ready : PSTRTMSeq005.RunsFrom (rawRecordMachine machine)
      ⟨0,(PA17TMRatArithmeticStore019.anchorState 5 (false::false::beforeArchive) input).Tape⟩
      innerTrace innerLast := by
    simpa only [rawRecordMachine,innerTrace,innerLast,PA17TMRatArithmeticStore019.anchorState,
      inputLeft,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using rawRun
  have fullRun := PSTRTMSeq005.seq_runsFrom clearAnchorMachine (rawRecordMachine machine)
    (PA17TMRatArithmeticStore019.anchorState 0 (false::true::beforeArchive) input)
    (PA17TMRatArithmeticStore019.anchorState 5 (false::false::beforeArchive) input)
    innerLast (clearAnchorTrace beforeArchive input) innerTrace
    (clearAnchor_runsFrom beforeArchive input) ready
  let fullTrace := (clearAnchorTrace beforeArchive input).map (PSTRTMSeq005.leftCfg (b:=states+27+1)) ++
    innerTrace.map (PSTRTMSeq005.rightCfg (a:=5))
  let fullLast := PSTRTMSeq005.rightCfg (a:=5) innerLast
  have innerLength : innerTrace.length=framed.length+
      (PA17TMRatArithmeticStore019.storeTrace recordArchive n).length := by
    simp only [innerTrace,List.length_append,List.length_map]
  have fullLength : fullTrace.length=6+innerTrace.length := by
    simp only [fullTrace,List.length_append,List.length_map,clearAnchor_length]
  have htime : fullTrace.length≤budget+32*(natBits n+1)^2+6 := by
    have hs := PA17TMRatArithmeticStore019.store_length_le recordArchive n
    omega
  refine ⟨left,right,fullTrace,fullLast,fullRun,rfl,hl,hr,hsum,htime,?_⟩
  intro prefixLength inputLength
  have hs := PSTRTMTrace002.visitedSpace_le (recordMachine machine) inputLength
    (fullTrace.take prefixLength)
  have hp : (fullTrace.take prefixLength).length≤fullTrace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeRecord022
