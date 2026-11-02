module

public import Common.PSTR_WordBool_RatInputComplementCode_096

/-! Actual original word input, actual prior provenance, actual raw
subtraction and the paid packet reader/cleanup, in one fixed Bool program. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement

open Turing PSTRWordVM RationalControllerComputation PaperProofs.Statistics
open PA17TMRatArithmeticAddSubController075 PA17TMRatArithmeticAddSubFull079

variable {C : Type*}

def frontBound (length : Nat) : Nat :=131072*(length+1)^2
def rawBound (length : Nat) : Nat :=addSubResourceCoefficient*(16*frontBound length+1)^4
def space (length : Nat) : Nat :=16*frontBound length+rawBound length+8

theorem outside_native_le (contents : RatInput.Stack→List Bool) :
    IsolatedRat.outside contents≤RatInput.occupied contents := by
  simp [IsolatedRat.outside,IsolatedRat.pulled,IsolatedRat.roles,Equiv.swap_apply_def,
    RatInput.occupied,Fin.sum_univ_succ,VirtualReturn.outside]
  omega

theorem internal_bound (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      ∀ slot,(node.2 slot).length≤bound+15) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤30*(bound+16) := by
  refine ⟨?_,?_⟩
  · intro node member slot
    exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
      (Nat.add_le_add_left (program_pushes point) bound)
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

theorem output_updates (contents background : RatInput.Stack→List Bool) (target : List Bool)
    (right : contents 13=[]) (left : contents 14=[]) (output : contents 15=target)
    (frames : ∀ slot,slot≠13→slot≠14→slot≠15→contents slot=background slot) :
    contents=Function.update (Function.update (Function.update background 13 []) 14 []) 15 target := by
  funext slot
  by_cases atR : slot=13
  · subst slot;exact right
  by_cases atL : slot=14
  · subst slot;exact left
  by_cases atT : slot=15
  · subst slot;exact output
  simp only [Function.update_of_ne atR,Function.update_of_ne atL,Function.update_of_ne atT]
  exact frames slot atR atL atT

theorem actual_original_complement (context : C) (nativeMemory : CalleeFlags) (readerMemory : Reader)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    let bits:=wordInput E target word
    let W:=space bits.length
    ∃ (trace : List (State C)) (final parsed : State C),
      trace.head?=some (initial context nativeMemory readerMemory bits) ∧
      trace.IsChain (fun a b=>TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧ final.l=some .done ∧
      final.var.1.1.1.1.1=context ∧
      final.stk=Encoder.bank parsed.stk
        (Encoder.packet (1-E.priorOne) (Encoder.packet E.priorOne [])) [] [] [] [] [] [] [] [] ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (PA17TMRatArithmeticParse002.bothLeft
          (false::PA17TMRatArithmeticParse002.sign E.priorOne::PSTRTMWordPriorFront215.priorBase E target word)
          (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
          (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)) (PSTRTMWordPriorFront215.afterPrior E target word) ∧
      trace.length≤4096*(bits.length+1)^2+4*W+20 ∧
      (∀ current∈trace,
        (∀ slot,(current.stk slot).length≤W) ∧ RatInput.occupied current.stk≤16*W) ∧
      (∀ current∈trace,∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
          ∀ slot,(node.2 slot).length≤W+15) ∧
        ScannerStatement.clock (program .halt point) current.var current.stk≤30*(W+16)) := by
  dsimp only
  let bits:=wordInput E target word
  let B:=frontBound bits.length
  let R:=rawBound bits.length
  let W:=space bits.length
  have wValue : W=16*B+R+8:=rfl
  obtain ⟨fPath,fFinal,fParsed,fFirst,fChain,fLast,parsedMember,fPort,fContext,fOutput,parsedTape,fTime,fBounds,_fNodes⟩:=
    Original.actual_original_pair ((context,nativeMemory),readerMemory) E target word
  have fFinalBounds:=fBounds fFinal (List.mem_of_getLast? fLast)
  have right : fFinal.stk 13=encode [.rational 1,.rational E.priorOne] :=by rw [fOutput];rfl
  have left : fFinal.stk 14=[]:=by rw [fOutput];rfl
  let middle:=frontConfiguration fFinal
  let background:=fFinal.stk
  let callerContext:Original.Store C:=(storeMap C fFinal.var).1.1
  let nativeFlags:CalleeFlags:=(storeMap C fFinal.var).1.2
  let readerFlags:Reader:=(storeMap C fFinal.var).2
  obtain ⟨nPath,nFinal,nFirst,nChain,nLast,nPort,nContext,nRight,nLeft,_nScratch,nOutput,nFrame,nTime,nBounds,_nProper⟩:=
    RatOutput.Link.actual_prior_output .halt callerContext readerFlags nativeFlags background E.priorOne
  have shared : nativeConfiguration (RatOutput.Link.nativeConfiguration
      (IsolatedRat.entry (callerContext,readerFlags) nativeFlags background (encode [.rational 1,.rational E.priorOne])))=middle := by
    cases fFinal with
    | mk position memory contents =>
      change position=some .done at fPort
      subst position
      dsimp [nativeConfiguration,frontConfiguration,LabelMap.configuration,StoreIso.configuration,
        RatOutput.Link.nativeConfiguration,IsolatedRat.entry,frontLabel,nativeLabel,
        callerContext,nativeFlags,readerFlags,middle,background]
      congr 1
      funext slot
      fin_cases slot <;> first | rfl | exact right.symm | exact left.symm
  have frontLift:=front_path (.halt:Statement C) fPath _ _ fFirst fChain fLast fPort
  have nativeLift:=native_path (.halt:Statement C) nPath _ _ nFirst nChain nLast nPort
  let front:=fPath.map frontConfiguration
  let back:=nPath.map nativeConfiguration
  let final:=nativeConfiguration nFinal
  let parsed:=frontConfiguration fParsed
  have frontLast : front.getLast?=some middle:=frontLift.2.2
  have backFirst : back.head?=some middle:=nativeLift.1.trans (congrArg some shared)
  have shape : middle::back.tail=back:=by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp backFirst
    rw [same];rfl
  have sameLength:=congrArg List.length shape
  simp only [List.length_cons] at sameLength
  have inputLength : (encode [.rational 1,.rational E.priorOne]).length≤16*B := by
    rw [←right]
    exact (Encoder.point_mass fFinal.stk 13).trans fFinalBounds.2
  have rawCap : IsolatedRat.rawBudget E.priorOne≤R := by
    exact Nat.mul_le_mul_left addSubResourceCoefficient
      (Nat.pow_le_pow_left (Nat.add_le_add_right inputLength 1) 4)
  have backgroundMass : RatInput.occupied background≤16*B:=fFinalBounds.2
  have nativeBudget : RatOutput.Link.budget background E.priorOne+8≤W := by
    have outside:=outside_native_le background
    change IsolatedRat.outside background+IsolatedRat.rawBudget E.priorOne+8≤W
    omega
  have nativeOutput : nFinal.stk 15=Encoder.packet (1-E.priorOne) (Encoder.packet E.priorOne []) := by
    rw [nOutput]
    have oldOutput : background 15=Encoder.packet E.priorOne []:=by dsimp only [background];rw [fOutput];rfl
    rw [oldOutput]
    rfl
  have finalOutput : nFinal.stk=Encoder.bank fParsed.stk
      (Encoder.packet (1-E.priorOne) (Encoder.packet E.priorOne [])) [] [] [] [] [] [] [] [] := by
    rw [output_updates nFinal.stk background _ nRight nLeft nativeOutput nFrame]
    dsimp only [background]
    rw [fOutput]
    funext slot
    fin_cases slot <;> rfl
  have allBounds : ∀ current∈front++back.tail,
      (∀ slot,(current.stk slot).length≤W) ∧ RatInput.occupied current.stk≤16*W := by
    intro current member
    rcases List.mem_append.mp member with early|later
    · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp early
      have bounds:=fBounds old oldMember
      have bSmall : B≤W:=by omega
      exact ⟨fun slot=>(bounds.1 slot).trans bSmall,bounds.2.trans (Nat.mul_le_mul_left 16 bSmall)⟩
    · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp (List.mem_of_mem_tail later)
      have mass : RatInput.occupied old.stk≤W:=((nBounds old oldMember).2.2).trans nativeBudget
      exact ⟨fun slot=>(Encoder.point_mass old.stk slot).trans mass,mass.trans (by omega)⟩
  refine ⟨front++back.tail,final,parsed,?_,?_,?_,?_,?_,?_,finalOutput,parsedTape,?_,allBounds,?_⟩
  · rw [List.head?_append,frontLift.1];rfl
  · exact NativeTrace.join_chain _ _ _ frontLast frontLift.2.1 (shape.symm ▸ nativeLift.2.1)
  · exact (NativeTrace.join_last _ _ _ frontLast).trans (shape.symm ▸ nativeLift.2.2)
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨fParsed,parsedMember,rfl⟩)
  · change nFinal.l.map nativeLabel=some .done
    rw [nPort];rfl
  · have fContext' : callerContext.1.1.1=context:=congrArg (fun value=>value.1.1) fContext
    exact (congrArg (fun value : Original.Store C=>value.1.1.1) nContext).trans fContext'
  · have frontLength : front.length=fPath.length:=List.length_map _
    have backLength : back.length=nPath.length:=List.length_map _
    change fPath.length≤4096*(bits.length+1)^2 at fTime
    change (front++back.tail).length≤4096*(bits.length+1)^2+4*W+20
    simp only [List.length_append]
    omega
  · intro current member point selected
    exact internal_bound current point W (allBounds current member).1

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement
