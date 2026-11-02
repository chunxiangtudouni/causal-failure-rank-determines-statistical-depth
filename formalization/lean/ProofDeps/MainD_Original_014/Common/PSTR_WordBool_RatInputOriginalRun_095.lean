module

public import Common.PSTR_WordBool_RatInputOriginalCode_094

/-! Original wordInput -> actual215 parser/archive -> actual093 signed
packet -> exact original pair input. No packet/empty-scratch/result premise
is added to the original experiment and stopped-word arguments. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Original

open Turing PSTRWordVM RationalControllerComputation PaperProofs.Statistics
open scoped BigOperators

variable {C : Type*}

theorem mass_eq (contents : RatInput.Stack→List Bool) :
    RatInput.occupied contents=VirtualReturn.occupiedSlots contents:=IsolatedRat.occupied_eq contents

theorem outside_le (contents : RatInput.Stack→List Bool) : Encoder.outside contents≤RatInput.occupied contents := by
  apply Finset.sum_le_sum
  intro slot member
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤15 := by
  cases point with
  | prior point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact (PSTRSymbolicRatExport.Joined.combined_actions point).trans (by decide)
  | encoder point =>
    rw [program,LabelMap.statement_actions]
    exact Encoder.program_actions point
  | done => exact Nat.zero_le _

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤15 := by
  cases point with
  | prior point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact (PSTRSymbolicRatExport.Joined.combined_pushes point).trans (by decide)
  | encoder point =>
    rw [program,LabelMap.statement_pushes]
    exact Encoder.program_pushes point
  | done => exact Nat.zero_le _

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

theorem actual_original_pair (context : C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    let bits:=wordInput E target word
    let bound:=131072*(bits.length+1)^2
    ∃ (trace : List (State C)) (final parsed : State C),
      trace.head?=some (initial context bits) ∧
      trace.IsChain (fun a b=>TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧
      final.l=some .done ∧ final.var.1.1.1=context ∧
      final.stk=Encoder.bank parsed.stk (Encoder.packet E.priorOne []) [] [] [] [] []
        (encode [.rational 1,.rational E.priorOne]) [] [] ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (PA17TMRatArithmeticParse002.bothLeft
          (false::PA17TMRatArithmeticParse002.sign E.priorOne::PSTRTMWordPriorFront215.priorBase E target word)
          (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
          (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)) (PSTRTMWordPriorFront215.afterPrior E target word) ∧
      trace.length≤4096*(bits.length+1)^2 ∧
      (∀ current∈trace,
        (∀ slot,(current.stk slot).length≤bound) ∧ RatInput.occupied current.stk≤16*bound) ∧
      (∀ current∈trace,∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
          ∀ slot,(node.2 slot).length≤bound+15) ∧
        ScannerStatement.clock (program .halt point) current.var current.stk≤30*(bound+16)) := by
  dsimp only
  let bits:=wordInput E target word
  let sq:=(bits.length+1)^2
  let P:=VirtualReturn.outside (fun _ : RatInput.Stack=>[])+128*sq
  let B:=131072*sq
  have sqPositive : 1≤sq :=Nat.pow_le_pow_left (show 1≤bits.length+1 by omega) 2
  have outZero : VirtualReturn.outside (fun _ : RatInput.Stack=>[])=0:=rfl
  have pValue : P=128*sq:=by dsimp only [P];rw [outZero];omega
  obtain ⟨oldPath,oldFinal,oldParsed,oldFirst,oldChain,oldLast,parsedMember,parsedPort,parsedTape,
    oldPort,oldContext,oldOutput,parsedFrame,oldTime,oldResources,_oldNodes⟩:=
    PSTRSymbolicRatExport.Joined.actual_original_word_prior (context,(false,false)) (fun _=>[]) E target word
  have oldMass : ∀ current∈oldPath,RatInput.occupied current.stk≤3*P+15 := by
    intro current member
    rw [mass_eq]
    exact (oldResources current member).2.2
  have parsedMass:=oldMass oldParsed parsedMember
  have finalMass:=oldMass oldFinal (List.mem_of_getLast? oldLast)
  have parsedEmpty : ∀ slot,Encoder.Work slot → oldParsed.stk slot=[] := by
    intro slot owned
    have noInput:=work_ne_input slot owned
    exact parsedFrame slot noInput.1 noInput.2
  have oldPacket : oldFinal.stk 15=Encoder.packet E.priorOne [] := by
    rw [oldOutput,Function.update_self]
    rfl
  have packetMass : (Encoder.packet E.priorOne []).length≤3*P+15 := by
    rw [←oldPacket]
    exact (Encoder.point_mass oldFinal.stk 15).trans finalMass
  have size : Encoder.fieldSize E.priorOne≤3*P+15 := by
    rw [Encoder.packet_length] at packetMass
    simp only [List.length_nil,Nat.add_zero] at packetMass
    omega
  let eContext:=(oldFinal.var.1.1.1,oldFinal.var.1.2)
  obtain ⟨ePath,eFinal,eFirst,eChain,eLast,ePort,eContextFinal,eOutput,eTime,eBounds,_eNodes⟩:=
    Encoder.actual_pair .halt oldParsed.stk eContext oldFinal.var.2 oldFinal.var.1.1.2 E.priorOne [] []
  have shared : encoderConfiguration (Encoder.entry oldParsed.stk eContext oldFinal.var.2 oldFinal.var.1.1.2 E.priorOne [] [])=
      priorConfiguration oldFinal := by
    cases oldFinal with
    | mk position memory contents =>
      change position=some 5 at oldPort
      subst position
      dsimp [encoderConfiguration,Encoder.entry,priorConfiguration,LabelMap.configuration,StoreIso.configuration,
        storeMap,priorLabel,encoderLabel,eContext]
      rw [bank_from_empty oldParsed.stk _ parsedEmpty]
      congr 1
      exact oldOutput.symm
  have oldLift:=prior_path (.halt:Statement C) oldPath _ _ oldFirst oldChain oldLast oldPort
  have eLift:=encoder_path (.halt:Statement C) ePath _ _ eFirst eChain eLast ePort
  let front:=oldPath.map priorConfiguration
  let back:=ePath.map encoderConfiguration
  let middle:=priorConfiguration oldFinal
  let parsed:=priorConfiguration oldParsed
  let final:=encoderConfiguration eFinal
  have frontLast : front.getLast?=some middle:=oldLift.2.2
  have backFirst : back.head?=some middle:=eLift.1.trans (congrArg some shared)
  have shape : middle::back.tail=back:=by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp backFirst
    rw [same];rfl
  have sameLength:=congrArg List.length shape
  simp only [List.length_cons] at sameLength
  have eSpace : Encoder.space oldParsed.stk E.priorOne [] []≤B := by
    have outside:=outside_le oldParsed.stk
    dsimp only [Encoder.space]
    simp only [List.length_nil,Nat.add_zero]
    dsimp only [B]
    omega
  have allBounds : ∀ current∈front++back.tail,
      (∀ slot,(current.stk slot).length≤B) ∧ RatInput.occupied current.stk≤16*B := by
    intro current member
    rcases List.mem_append.mp member with early|later
    · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp early
      have mass:=oldMass old oldMember
      have massBound : RatInput.occupied old.stk≤B:=by dsimp only [B];omega
      exact ⟨fun slot=>(Encoder.point_mass old.stk slot).trans massBound,massBound.trans (by omega)⟩
    · obtain ⟨old,oldMember,rfl⟩:=List.mem_map.mp (List.mem_of_mem_tail later)
      have bounds:=eBounds old oldMember
      exact ⟨fun slot=>(bounds.1 slot).trans eSpace,bounds.2.1.trans (Nat.mul_le_mul_left 16 eSpace)⟩
  refine ⟨front++back.tail,final,parsed,?_,?_,?_,?_,?_,?_,?_,parsedTape,?_,allBounds,?_⟩
  · rw [List.head?_append,oldLift.1];rfl
  · exact NativeTrace.join_chain _ _ _ frontLast oldLift.2.1 (shape.symm ▸ eLift.2.1)
  · exact (NativeTrace.join_last _ _ _ frontLast).trans (shape.symm ▸ eLift.2.2)
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨oldParsed,parsedMember,rfl⟩)
  · change eFinal.l.map encoderLabel=some .done
    rw [ePort];rfl
  · exact (congrArg Prod.fst eContextFinal).trans (congrArg Prod.fst oldContext)
  · exact eOutput
  · have frontLength : front.length=oldPath.length:=List.length_map _
    have backLength : back.length=ePath.length:=List.length_map _
    change oldPath.length≤33*sq+3*P+9 at oldTime
    change ePath.length≤8*Encoder.fieldSize E.priorOne+34 at eTime
    change (front++back.tail).length≤4096*sq
    simp only [List.length_append]
    omega
  · intro current member point selected
    exact internal_bound current point B (allBounds current member).1

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Original
