module

public import B23_4_RatWordPrep_SeqCmp_OddsInitPaths_112

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def Owned (slot : RatInput.Stack) : Prop :=
  slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=8 ∨ slot=9 ∨ slot=12 ∨ slot=13 ∨ slot=14

instance ownedDecidable (slot : RatInput.Stack) : Decidable (Owned slot) := by unfold Owned; infer_instance

theorem divide_shared (before : State C) (x y : Rat) (tail : List Bool)
    (active : before.l=some (.divide default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    let memory := (FullStore.divIso C).symm before.var
    divideCfg (RatBinary.entry before.stk memory.1.1.1.1.1 memory.1.1.1.1.2.1 memory.1.1.1.1.2.2
      memory.1.1.1.2 memory.1.1.2 memory.1.2 memory.2 x y tail (before.stk 7))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.divide default) at active
    subst point
    have rebuild (m : RatBinary.Store (FullStore.DivContext C) RatMulDiv.divStates) :
        RatBinary.pairStoreMap (FullStore.DivContext C) RatMulDiv.divStates
          (((((m.1.1.1.1.1,m.1.2),m.2),m.1.1.1.1.2.1,m.1.1.1.1.2.2),m.1.1.1.2),m.1.1.2)=m := by
      rcases m with ⟨⟨⟨⟨⟨context,flags⟩,rat⟩,formatter⟩,native⟩,reader⟩
      rfl
    let old := (FullStore.divIso C).symm memory
    let initial := RatBinary.entry slots old.1.1.1.1.1 old.1.1.1.1.2.1 old.1.1.1.1.2.2
      old.1.1.1.2 old.1.1.2 old.1.2 old.2 x y tail (slots 7)
    have oldMemory : initial.var=old := by
      change RatBinary.pairStoreMap (FullStore.DivContext C) RatMulDiv.divStates
        (((((old.1.1.1.1.1,old.1.2),old.2),old.1.1.1.1.2.1,old.1.1.1.1.2.2),old.1.1.1.2),old.1.1.2)=old
      exact rebuild old
    change (⟨some (.divide default),FullStore.divIso C initial.var,initial.stk⟩ : State C)=
      ⟨some (.divide default),memory,slots⟩
    rw [oldMemory,Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot
    all_goals first
    | rfl
    | exact (RatPair.two_packet_format x y tail).trans source.symm
    | exact (owned _ (by decide)).symm

/-- The concrete frozen division contract is discharged before operands.
Its normalized packet is produced by real pair/native/reader/disposal
execution; no nonzero, width, fuel or result-packet hypothesis is added. -/
theorem actual_divide (caller : Statement C) (before : State C) (x y : Rat) (tail : List Bool)
    (active : before.l=some (.divide default)) (source : before.stk 15=RatPair.input x y tail)
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .done ∧ final.var.2=before.var.2 ∧
      final.stk 15=RatInput.Encoder.packet (x/y) tail ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      (∀ slot,¬RatPair.Link.Work slot→final.stk slot=before.stk slot) ∧
      run.trace.length≤RatBinary.time RatMulDiv.divCoefficient before.stk x y tail (before.stk 7) := by
  let memory := (FullStore.divIso C).symm before.var
  obtain ⟨trace,final,facts⟩ := RatBinary.actual_binary RatMulDiv.divSource RatMulDiv.divCoefficient
    (fun x y => x/y) (by
      intro D next context reader native background a b
      exact RatMulDiv.actual_div next context reader native background a b)
    before.stk memory.1.1.1.1.1 memory.1.1.1.1.2.1 memory.1.1.1.1.2.2
      memory.1.1.1.2 memory.1.1.2 memory.1.2 memory.2 x y tail (before.stk 7)
  have path := single_port_path (FullStore.divIso C) divideLabel _ caller .done rfl trace _ final
    facts.first facts.chain facts.last facts.active
      (by intro point different; simp only [divideLabel,different,ite_false,program])
  let run : Segment caller before (divideCfg final) :=
    ⟨trace.map divideCfg,path.1.trans (congrArg some (divide_shared before x y tail active source owned)),path.2.1,path.2.2⟩
  refine ⟨divideCfg final,run,?_,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map divideLabel=some .done
    rw [facts.active]
    rfl
  · exact congrArg (fun context : FullStore.DivContext C => context.2) facts.context_eq
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

end B23_4_RatWordPrep.OddsInit
