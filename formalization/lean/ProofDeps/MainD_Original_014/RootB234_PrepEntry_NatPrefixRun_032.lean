module

public import RootB234_PrepEntry_NatPrefixCode_031

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPrefix

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

/-- The list is only the specification of the original natural Datums.
The fixed source actually reads their tags and stops at the first Rat;
neither this list nor its length is a runtime input or register. -/
theorem actual (caller : Statement C) (numbers : List Nat) (context : C)
    (memory : Alpha.NativeMemory) (bank : RatInput.Stack → List Bool)
    (left : List Bool) (x : Rat) (suffix : List Bool)
    (physical : tape bank=Tape.mk₂ left (naturals numbers++encodeDatum (.rational x)++suffix)) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (⟨some .check,(context,memory),bank⟩ : State C) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      tape final.stk=Tape.mk₂ (archived left numbers) (encodeDatum (.rational x)++suffix) ∧
      final.var.1=context ∧ trace.length≤workTime numbers ∧
      ∀ current∈trace,current.var.1=context ∧
        ∀ slot,slot≠0→slot≠1→current.stk slot=bank slot := by
  induction numbers generalizing memory bank left with
  | nil =>
    let before : State C:=⟨some .check,(context,memory),bank⟩
    let final : State C:=⟨some .done,(context,(0,true)),bank⟩
    have edge:=rational_step caller context memory bank left x suffix (by simpa only [naturals,
      List.flatMap_nil,List.nil_append] using physical)
    refine ⟨[before,final],final,rfl,
      List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,rfl,?_,rfl,?_,?_⟩
    · simpa only [final,archived,List.foldl_nil,naturals,List.flatMap_nil,List.nil_append] using physical
    · exact Nat.le_refl _
    · intro current member
      rcases List.mem_cons.mp member with same|later
      · subst current; exact ⟨rfl,fun _ _ _ => rfl⟩
      · have same:=List.mem_singleton.mp later
        subst current; exact ⟨rfl,fun _ _ _ => rfl⟩
  | cons number numbers ih =>
    let before : State C:=⟨some .check,(context,memory),bank⟩
    let aStart : Alpha.State C:=⟨some 0,(context,(0,false)),bank⟩
    let tail:=naturals numbers++encodeDatum (.rational x)++suffix
    have initial : tape bank=Tape.mk₂ left (encodeDatum (.natural number)++tail) := by
      simpa only [naturals,List.flatMap_cons,tail,List.append_assoc] using physical
    have edge:=natural_step caller context memory bank left number tail initial
    have alphaPhysical : tape bank=Tape.mk₂ left (false::(encodeNat number++tail)) := by
      simpa only [encodeDatum,List.cons_append] using initial
    obtain ⟨aTrace,aFinal,aFirst,aChain,aLast,aActive,aTape,aCount,aContext,aFrames⟩:=
      Alpha.actual context (0,false) bank left number tail rfl alphaPhysical
    have aPath:=parse_path caller aTrace aStart aFinal aFirst aChain aLast aActive
    let front:=before::(aTrace.map parseCfg)
    have frontChain : front.IsChain (fun a b => TM2.step (program caller) a=some b) := by
      obtain ⟨rest,shape⟩:=List.head?_eq_some_iff.mp aPath.1
      have chain:=aPath.2.1
      rw [shape] at chain
      change (before::aTrace.map parseCfg).IsChain _
      rw [shape]
      exact List.isChain_cons_cons.mpr ⟨edge,chain⟩
    have frontLast : front.getLast?=some (parseCfg aFinal) := by
      obtain ⟨rest,shape⟩:=List.head?_eq_some_iff.mp aPath.1
      have last:=aPath.2.2
      rw [shape] at last
      change (before::aTrace.map parseCfg).getLast?=_
      rw [shape]
      exact last
    have shared : parseCfg aFinal=(⟨some .check,(context,aFinal.var.2),aFinal.stk⟩ : State C) := by
      rw [←aContext]
      cases aFinal with
      | mk point registers contents =>
        change point=some 1 at aActive
        subst point
        rfl
    have remaining : tape aFinal.stk=Tape.mk₂ (Alpha.nextLeft left number)
        (naturals numbers++encodeDatum (.rational x)++suffix) := aTape
    obtain ⟨bTrace,bFinal,bFirst,bChain,bLast,bActive,bTape,bContext,bCount,bFrames⟩:=
      ih aFinal.var.2 aFinal.stk (Alpha.nextLeft left number) remaining
    have bHead : bTrace.head?=some (parseCfg aFinal) := bFirst.trans (congrArg some shared.symm)
    have bShape : parseCfg aFinal::bTrace.tail=bTrace := by
      obtain ⟨rest,shape⟩:=List.head?_eq_some_iff.mp bHead
      rw [shape]; rfl
    let trace:=front++bTrace.tail
    have first : trace.head?=some before := by
      rw [List.head?_append]
      rfl
    have chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b) :=
      NativeTrace.join_chain _ _ _ frontLast frontChain (bShape.symm ▸ bChain)
    have last : trace.getLast?=some bFinal :=
      (NativeTrace.join_last _ _ _ frontLast).trans (bShape.symm ▸ bLast)
    refine ⟨trace,bFinal,first,chain,last,bActive,?_,bContext,?_,?_⟩
    · exact bTape
    · have tailCount : bTrace.tail.length≤workTime numbers := by rw [List.length_tail]; omega
      change (front++bTrace.tail).length≤workTime (number::numbers)
      simp only [front,List.length_append,List.length_cons,List.length_map,workTime,
        List.map_cons,List.sum_cons] at ⊢
      have sumTail : (numbers.map (fun n => (PSTRTMNatValue017.rawPayload n).length^2+
          9*(PSTRTMNatValue017.rawPayload n).length+7)).sum+2=workTime numbers := rfl
      omega
    · intro current member
      rcases List.mem_append.mp member with early|later
      · rcases List.mem_cons.mp early with same|parsed
        · subst current; exact ⟨rfl,fun _ _ _ => rfl⟩
        · obtain ⟨small,present,rfl⟩:=List.mem_map.mp parsed
          exact aFrames small present
      · have frame:=bFrames current (List.mem_of_mem_tail later)
        refine ⟨frame.1,?_⟩
        intro slot notZero notOne
        exact (frame.2 slot notZero notOne).trans
          ((aFrames aFinal (List.mem_of_getLast? aLast)).2 slot notZero notOne)

theorem payload_positive (number : Nat) : 1≤(PSTRTMNatValue017.rawPayload number).length := by
  have nonempty:=PSTRSymbolicLaneArchive.rawPayload_nonempty number
  cases shape : PSTRTMNatValue017.rawPayload number with
  | nil => exact False.elim (nonempty shape)
  | cons bit later => simp only [List.length_cons]; omega

theorem workTime_le (numbers : List Nat) : workTime numbers≤32*(payloadMass numbers+1)^2 := by
  induction numbers with
  | nil => norm_num [workTime,payloadMass]
  | cons number numbers ih =>
    have positive:=payload_positive number
    simp only [workTime,payloadMass,List.map_cons,List.sum_cons] at ih ⊢
    nlinarith only [ih,positive,Nat.zero_le ((numbers.map (fun n =>
      (PSTRTMNatValue017.rawPayload n).length)).sum)]

theorem payloadMass_le (numbers : List Nat) : payloadMass numbers≤(naturals numbers).length := by
  induction numbers with
  | nil => exact Nat.le_refl _
  | cons number numbers ih =>
    have field : (PSTRTMNatValue017.rawPayload number).length≤(encodeDatum (.natural number)).length := by
      simp only [PSTRSymbolicLocator.rawPayload_length,encodeDatum,encodeNat,List.length_cons,
        List.length_append,List.length_replicate,List.length_ofFn]
      omega
    simpa only [payloadMass,naturals,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
      using Nat.add_le_add field ih

theorem workTime_wire_le (numbers : List Nat) : workTime numbers≤32*((naturals numbers).length+1)^2 :=
  (workTime_le numbers).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right
    (payloadMass_le numbers) 1) 2))

end RootB234.PrepEntry.NatPrefix
