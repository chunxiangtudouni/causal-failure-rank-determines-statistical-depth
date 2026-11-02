module

public import B23_4_RatWordPrep_SeqCmp_WholeCopyResources_044

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.WholeCopy

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def coefficient : Nat := 4096

def inputScale (background : RatInput.Stack → List Bool) (input backup scratch : List Bool) : Nat :=
  RatInput.occupied (bank background input backup scratch)+1

theorem resource_envelope (background : RatInput.Stack → List Bool) (input backup scratch : List Bool) :
    let M:=RatInput.occupied (bank background input backup scratch)
    let S:=M+16*(2*input.length+4)
    let K:=inputScale background input backup scratch
    2*input.length+4 ≤ coefficient*K ∧ 16*S ≤ coefficient*K ∧
      S+16 ≤ coefficient*K ∧ 32*(S+17) ≤ coefficient*K := by
  have sourceBound:=RatInput.Encoder.point_mass (bank background input backup scratch) 0
  change input.length ≤ RatInput.occupied (bank background input backup scratch) at sourceBound
  dsimp only [inputScale,coefficient]
  omega

structure Facts (source : Label → Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (input backup scratch : List Bool) (run : List (State C)) : Prop where
  first : run.head?=some (state background .boot memory input backup scratch)
  chain : run.IsChain (fun before after => TM2.step source before=some after)
  last : run.getLast?=some (state background .done (memory.1,true,true) input (input.reverse++backup) scratch)
  count : run.length=2*input.length+4
  time : run.length ≤ coefficient*inputScale background input backup scratch
  boundaries : ∀ current∈run,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length ≤ coefficient*inputScale background input backup scratch) ∧
    RatInput.occupied current.stk ≤ coefficient*inputScale background input backup scratch ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈run.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        node.1.1=memory.1 ∧
        (∀ slot,(node.2 slot).length ≤ coefficient*inputScale background input backup scratch) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk ≤ coefficient*inputScale background input backup scratch

theorem actual_bounded (background : RatInput.Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) :
    ∃ run,Facts (program .halt) background memory input backup scratch run := by
  obtain ⟨run,first,chain,last,count⟩:=actual .halt background memory input backup scratch
  let before:=state background .boot memory input backup scratch
  let M:=RatInput.occupied before.stk
  let S:=M+16*(2*input.length+4)
  have frames : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot untouched
    have n0 : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    have n2 : slot≠2 := by intro same; subst slot; exact untouched (by decide)
    have n3 : slot≠3 := by intro same; subst slot; exact untouched (by decide)
    simp only [before,state,bank,n0,n2,n3,ite_false]
  have bounds:=trace_resources run before background M first chain (RatInput.Encoder.point_mass before.stk) frames
  have contexts:=trace_context run before first chain
  have bounded : ∀ current∈run,∀ slot,(current.stk slot).length ≤ S := by
    intro current member slot
    have bound:=(bounds current member).1 slot
    rw [count] at bound
    exact bound
  have caps:=resource_envelope background input backup scratch
  have proper:=NativeMulLink.no_early_halt_port (program .halt) .done rfl run
    (state background .done (memory.1,true,true) input (input.reverse++backup) scratch) chain last rfl
  refine ⟨run,⟨first,chain,last,count,count ▸ caps.1,?_,?_⟩⟩
  · intro current member
    refine ⟨contexts current member,?_,?_,(bounds current member).2⟩
    · intro slot
      exact (bounded current member slot).trans
        ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk S (bounded current member)).trans caps.2.1
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have internal:=internal_resources current point S (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    exact ⟨((internal.1 node inside).1).trans (contexts current (List.mem_of_mem_dropLast member)),
      fun slot => ((internal.1 node inside).2.1 slot).trans caps.2.2.1,
      fun slot untouched => ((internal.1 node inside).2.2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)⟩

def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

def traceClockSum (source : Label → Statement C) (run : List (State C)) : Nat :=
  (run.dropLast.map (statementClock source)).sum

def chargedCost (source : Label → Statement C) (run : List (State C)) : Nat :=
  run.length+traceClockSum source run

theorem traceClockSum_le {source : Label → Statement C} {background : RatInput.Stack → List Bool}
    {memory : Store C} {input backup scratch : List Bool} {run : List (State C)}
    (facts : Facts source background memory input backup scratch run) :
    traceClockSum source run ≤ coefficient^2*(inputScale background input backup scratch)^2 := by
  let cap:=coefficient*inputScale background input backup scratch
  have termwise : ∀ value∈run.dropLast.map (statementClock source),value ≤ cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum source run ≤ run.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.dropLast.map (statementClock source)) cap termwise
  have count : run.dropLast.length ≤ cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.length 1).trans facts.time
  calc
    traceClockSum source run ≤ cap*cap := sum.trans (Nat.mul_le_mul_right cap count)
    _ = _ := by dsimp only [cap]; ring

theorem chargedCost_le {source : Label → Statement C} {background : RatInput.Stack → List Bool}
    {memory : Store C} {input backup scratch : List Bool} {run : List (State C)}
    (facts : Facts source background memory input backup scratch run) :
    chargedCost source run ≤ (coefficient^2+coefficient)*(inputScale background input backup scratch)^2 := by
  have base : 1 ≤ inputScale background input backup scratch := by dsimp only [inputScale]; omega
  have powers : inputScale background input backup scratch ≤ (inputScale background input backup scratch)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : (1:Nat) ≤ 2)
  have count:=facts.time.trans (Nat.mul_le_mul_left coefficient powers)
  have sum:=traceClockSum_le facts
  calc
    chargedCost source run ≤ coefficient*(inputScale background input backup scratch)^2+
        coefficient^2*(inputScale background input backup scratch)^2 := Nat.add_le_add count sum
    _ = _ := by ring

namespace Public

theorem initial_default {C : Type*} [Inhabited C] (input : List Bool) :
    state (fun _ => []) .boot (default : Store C) input [] []=
      TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 input := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_stmt {C : Type*} (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports {C : Type*} : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

/-- Source and coefficients precede all real cells, auxiliary stores and tails. -/
theorem fixed_source (C : Type*) :
    ∃ source : Label → Statement C,source .done=.halt ∧
      ∀ background memory input backup scratch,
      ∃ run,Facts source background memory input backup scratch run ∧
        traceClockSum source run ≤ coefficient^2*(inputScale background input backup scratch)^2 ∧
        chargedCost source run ≤ (coefficient^2+coefficient)*(inputScale background input backup scratch)^2 := by
  refine ⟨program .halt,rfl,?_⟩
  intro background memory input backup scratch
  obtain ⟨run,facts⟩:=actual_bounded background memory input backup scratch
  exact ⟨run,facts,traceClockSum_le facts,chargedCost_le facts⟩

end Public
end B23_4_RatWordPrep.WholeCopy
