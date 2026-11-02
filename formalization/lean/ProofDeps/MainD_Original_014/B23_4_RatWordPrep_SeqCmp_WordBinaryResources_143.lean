module

public import B23_4_RatWordPrep_SeqCmp_WordResourceJoin_142

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

universe u v
variable {C : Type u}

/-- Resource-preserving installation of a frozen concrete RatBinary
callee. All bounds concern the same actual mapped Segment witness. -/
theorem actual_binary_resources {D : Type v} (states : Nat) (machine : Machine states) (coefficient : Nat)
    (operation : Rat → Rat → Rat) (realCall : RatMulDiv.CalleeClaims.{v} machine coefficient 4 operation)
    (iso : RatBinary.Store D states ≃ Store C) (rename : RatBinary.Label → Label)
    (caller : Statement C) (before : State C) (x y : Rat) (tail : List Bool)
    (active : before.l=some (rename default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[])
    (same : ∀ point,point≠.done→program caller (rename point)=
      LabelMap.statement rename (StoreIso.statement iso (RatBinary.program machine .halt point))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (rename .done) ∧
      (iso.symm final.var).1.1.1.1.1=(iso.symm before.var).1.1.1.1.1 ∧
      final.stk=binaryBank before.stk (operation x y) tail ∧
      RunBounds caller run (RatBinary.time coefficient before.stk x y tail (before.stk 7))
        (RatBinary.space coefficient before.stk x y tail (before.stk 7)+32)
        (64*(RatBinary.space coefficient before.stk x y tail (before.stk 7)+33)) := by
  let memory := iso.symm before.var
  let old := RatBinary.program (C := D) machine .halt
  obtain ⟨trace,final,facts⟩ := RatBinary.actual_binary machine coefficient operation realCall before.stk
    memory.1.1.1.1.1 memory.1.1.1.1.2.1 memory.1.1.1.1.2.2
      memory.1.1.1.2 memory.1.1.2 memory.1.2 memory.2 x y tail (before.stk 7)
  have path := single_port_path iso rename old caller .done rfl trace _ final
    facts.first facts.chain facts.last facts.active same
  let run : Segment caller before (mappedCfg iso rename final) :=
    ⟨trace.map (mappedCfg iso rename),path.1.trans
      (congrArg some (binary_shared states iso rename before x y tail active source owned)),path.2.1,path.2.2⟩
  refine ⟨mappedCfg iso rename final,run,?_,?_,?_,?_⟩
  · change final.l.map rename=some (rename .done)
    rw [facts.active]
    rfl
  · change (iso.symm (iso final.var)).1.1.1.1.1=memory.1.1.1.1.1
    rw [Equiv.symm_apply_apply]
    exact facts.context_eq
  · change final.stk=binaryBank before.stk (operation x y) tail
    rw [facts.contents]
    funext slot
    fin_cases slot <;> rfl
  · constructor
    · simpa only [run,List.length_map] using facts.count
    · intro current member slot
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      have bound := (facts.boundaries original present).2.1 slot
      exact bound.trans (by omega)
    · intro current member point selected node inside slot
      change current∈(trace.map (mappedCfg iso rename)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map rename=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      have different : oldPoint≠.done := by intro equal; subst oldPoint; exact facts.proper original present oldActive
      have body := same oldPoint different
      rw [←renamed] at inside
      change node∈AuxWorkspace.nodes (program caller (rename oldPoint)) (iso original.var) original.stk at inside
      rw [mapped_nodes iso rename old caller oldPoint original.var original.stk body] at inside
      obtain ⟨oldNode,oldInside,rfl⟩ := List.mem_map.mp inside
      exact ((facts.internal original (List.mem_of_mem_dropLast present) oldPoint oldActive).1 oldNode oldInside).1 slot
    · intro current member point selected
      change current∈(trace.map (mappedCfg iso rename)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map rename=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      have different : oldPoint≠.done := by intro equal; subst oldPoint; exact facts.proper original present oldActive
      have body := same oldPoint different
      rw [←renamed]
      change ScannerStatement.clock (program caller (rename oldPoint)) (iso original.var) original.stk≤_
      rw [body,clock_labelMap,clock_storeIso]
      exact (facts.internal original (List.mem_of_mem_dropLast present) oldPoint oldActive).2

theorem actual_division_resources (caller : Statement C) (high : Bool) (before : State C)
    (x y : Rat) (tail : List Bool)
    (active : before.l=some (.divide high default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet (if high then .parkHigh else .parkLow) 0) ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk=binaryBank before.stk (x/y) tail ∧
      RunBounds caller run (RatBinary.time RatMulDiv.divCoefficient before.stk x y tail (before.stk 7))
        (RatBinary.space RatMulDiv.divCoefficient before.stk x y tail (before.stk 7)+32)
        (64*(RatBinary.space RatMulDiv.divCoefficient before.stk x y tail (before.stk 7)+33)) := by
  obtain ⟨final,run,port,context,output,bounds⟩ := actual_binary_resources RatMulDiv.divStates
    RatMulDiv.divSource RatMulDiv.divCoefficient (fun x y => x/y)
      (by intro D next context reader native background a b; exact RatMulDiv.actual_div next context reader native background a b)
    (FullStore.divIso C) (divLabel high) caller before x y tail active source owned
      (by intro point different; simp only [divLabel,different,ite_false,program])
  exact ⟨final,run,port,congrArg (fun memory : FullStore.DivContext C => memory.2.2.2) context,output,bounds⟩

theorem actual_subtraction_resources (caller : Statement C) (before : State C)
    (x y : Rat) (tail : List Bool)
    (active : before.l=some (.subtract default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .parkComplement 0) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=binaryBank before.stk (x-y) tail ∧
      RunBounds caller run (RatBinary.time RatAddSub.addSubCoefficient before.stk x y tail (before.stk 7))
        (RatBinary.space RatAddSub.addSubCoefficient before.stk x y tail (before.stk 7)+32)
        (64*(RatBinary.space RatAddSub.addSubCoefficient before.stk x y tail (before.stk 7)+33)) := by
  obtain ⟨final,run,port,context,output,bounds⟩ := actual_binary_resources RatAddSub.addSubStates
    RatAddSub.subSource RatAddSub.addSubCoefficient (fun x y => x-y)
      (by intro D next context reader native background a b; exact RatAddSub.actual_sub next context reader native background a b)
    (FullStore.subIso C) subLabel caller before x y tail active source owned
      (by intro point different; simp only [subLabel,different,ite_false,program])
  exact ⟨final,run,port,congrArg (fun memory : FullStore.SubContext C => memory.2.2.2) context,output,bounds⟩

end B23_4_RatWordPrep.WordFinish.Resources
