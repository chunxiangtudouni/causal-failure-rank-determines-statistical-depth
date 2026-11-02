module

public import B23_4_RatWordPrep_SeqCmp_WordFinishPaths_127

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

universe u v
variable {C : Type u}

def Owned (slot : RatInput.Stack) : Prop :=
  slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=8 ∨ slot=9 ∨ slot=12 ∨ slot=13 ∨ slot=14

instance ownedDecidable (slot : RatInput.Stack) : Decidable (Owned slot) := by unfold Owned; infer_instance

theorem binary_shared {D : Type v} (states : Nat) (iso : RatBinary.Store D states ≃ Store C)
    (rename : RatBinary.Label → Label) (before : State C) (x y : Rat) (tail : List Bool)
    (active : before.l=some (rename default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    let memory := iso.symm before.var
    (fun current => LabelMap.configuration rename (StoreIso.configuration iso current)) (RatBinary.entry before.stk memory.1.1.1.1.1 memory.1.1.1.1.2.1 memory.1.1.1.1.2.2
      memory.1.1.1.2 memory.1.1.2 memory.1.2 memory.2 x y tail (before.stk 7))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (rename default) at active
    subst point
    have rebuild (m : RatBinary.Store (D) states) :
        RatBinary.pairStoreMap (D) states
          (((((m.1.1.1.1.1,m.1.2),m.2),m.1.1.1.1.2.1,m.1.1.1.1.2.2),m.1.1.1.2),m.1.1.2)=m := by
      rcases m with ⟨⟨⟨⟨⟨context,flags⟩,rat⟩,formatter⟩,native⟩,reader⟩
      rfl
    let old := iso.symm memory
    let initial := RatBinary.entry slots old.1.1.1.1.1 old.1.1.1.1.2.1 old.1.1.1.1.2.2
      old.1.1.1.2 old.1.1.2 old.1.2 old.2 x y tail (slots 7)
    have oldMemory : initial.var=old := by
      change RatBinary.pairStoreMap (D) states
        (((((old.1.1.1.1.1,old.1.2),old.2),old.1.1.1.1.2.1,old.1.1.1.1.2.2),old.1.1.1.2),old.1.1.2)=old
      exact rebuild old
    change (⟨some (rename default),iso initial.var,initial.stk⟩ : State C)=
      ⟨some (rename default),memory,slots⟩
    rw [oldMemory,Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot
    all_goals first
    | rfl
    | exact (RatPair.two_packet_format x y tail).trans source.symm
    | exact (owned _ (by decide)).symm

def binaryCfg {D : Type v} {states : Nat} (iso : RatBinary.Store D states ≃ Store C)
    (rename : RatBinary.Label → Label) (before : RatBinary.State D states) : State C :=
  LabelMap.configuration rename (StoreIso.configuration iso before)

theorem actual_binary {D : Type v} (states : Nat) (machine : Machine states) (coefficient : Nat)
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
      final.stk 15=RatInput.Encoder.packet (operation x y) tail ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      (∀ slot,¬RatPair.Link.Work slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤RatBinary.time coefficient before.stk x y tail (before.stk 7) := by
  let memory := iso.symm before.var
  obtain ⟨trace,final,facts⟩ := RatBinary.actual_binary machine coefficient operation realCall before.stk
    memory.1.1.1.1.1 memory.1.1.1.1.2.1 memory.1.1.1.1.2.2
      memory.1.1.1.2 memory.1.1.2 memory.1.2 memory.2 x y tail (before.stk 7)
  have path := single_port_path iso rename _ caller .done rfl trace _ final facts.first facts.chain facts.last facts.active same
  let run : Segment caller before (binaryCfg iso rename final) :=
    ⟨trace.map (binaryCfg iso rename),path.1.trans
      (congrArg some (binary_shared states iso rename before x y tail active source owned)),path.2.1,path.2.2⟩
  refine ⟨binaryCfg iso rename final,run,?_,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map rename=some (rename .done)
    rw [facts.active]
    rfl
  · change (iso.symm (iso final.var)).1.1.1.1.1=memory.1.1.1.1.1
    rw [Equiv.symm_apply_apply]
    exact facts.context_eq
  · change final.stk 15=_
    rw [facts.contents]
    rfl
  · change final.stk 7=_
    rw [facts.contents]
    rfl
  · intro slot selected
    change final.stk slot=[]
    rw [facts.contents]
    fin_cases slot <;> first | rfl | simp [Owned] at selected
  · exact (facts.boundaries final (List.mem_of_getLast? facts.last)).2.2
  · simpa only [run,List.length_map] using facts.count

def binaryBank (before : RatInput.Stack → List Bool) (result : Rat) (tail : List Bool) : RatInput.Stack → List Bool :=
  fun slot => if slot=15 then RatInput.Encoder.packet result tail else
    if slot=7 then before 7 else if Owned slot then [] else before slot

theorem binaryBank_eq {before final : State C} {result : Rat} {tail : List Bool}
    (output : final.stk 15=RatInput.Encoder.packet result tail) (scratch : final.stk 7=before.stk 7)
    (owned : ∀ slot,Owned slot→final.stk slot=[])
    (frame : ∀ slot,¬RatPair.Link.Work slot→final.stk slot=before.stk slot) :
    final.stk=binaryBank before.stk result tail := by
  funext slot
  fin_cases slot <;> first
  | exact output
  | exact scratch
  | exact owned _ (by decide)
  | exact frame _ (by decide)

theorem actual_division (caller : Statement C) (high : Bool) (before : State C)
    (x y : Rat) (tail : List Bool)
    (active : before.l=some (.divide high default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet (if high then .parkHigh else .parkLow) 0) ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk=binaryBank before.stk (x/y) tail ∧
      run.trace.length≤RatBinary.time RatMulDiv.divCoefficient before.stk x y tail (before.stk 7) := by
  obtain ⟨final,run,port,context,output,scratch,ownedFinal,frame,time⟩ := actual_binary RatMulDiv.divStates
    RatMulDiv.divSource RatMulDiv.divCoefficient (fun x y => x/y)
      (by intro D next context reader native background a b; exact RatMulDiv.actual_div next context reader native background a b)
    (FullStore.divIso C) (divLabel high) caller before x y tail active source owned
      (by intro point different; simp only [divLabel,different,ite_false,program])
  exact ⟨final,run,port,congrArg (fun v : FullStore.DivContext C => v.2.2.2) context,
    binaryBank_eq output scratch ownedFinal frame,time⟩

theorem actual_subtraction (caller : Statement C) (before : State C)
    (x y : Rat) (tail : List Bool)
    (active : before.l=some (.subtract default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.packet .parkComplement 0) ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk=binaryBank before.stk (x-y) tail ∧
      run.trace.length≤RatBinary.time RatAddSub.addSubCoefficient before.stk x y tail (before.stk 7) := by
  obtain ⟨final,run,port,context,output,scratch,ownedFinal,frame,time⟩ := actual_binary RatAddSub.addSubStates
    RatAddSub.subSource RatAddSub.addSubCoefficient (fun x y => x-y)
      (by intro D next context reader native background a b; exact RatAddSub.actual_sub next context reader native background a b)
    (FullStore.subIso C) subLabel caller before x y tail active source owned
      (by intro point different; simp only [subLabel,different,ite_false,program])
  exact ⟨final,run,port,congrArg (fun v : FullStore.SubContext C => v.2.2.2) context,
    binaryBank_eq output scratch ownedFinal frame,time⟩

end B23_4_RatWordPrep.WordFinish
