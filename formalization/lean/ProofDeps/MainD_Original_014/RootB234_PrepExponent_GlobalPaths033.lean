module

public import RootB234_PrepExponent_GlobalCode032

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def state (point : Label) (memory : Store C) (contents : Stack → List Bool) : State C := ⟨some point,memory,contents⟩

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.edge {caller : Statement C} {before final : State C}
    (step : TM2.step (program caller) before=some final) : Segment caller before final :=
  ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨step,List.isChain_singleton _⟩,rfl⟩

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) : Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same];rfl
  exact ⟨front.trace++back.trace.tail,by rw [List.head?_append,front.first];rfl,
    NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain),
    (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)⟩

theorem Segment.append_length {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length ≤ front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length ≤ _
  simp only [List.length_append,List.length_tail]
  omega

theorem label_path {Λ : Type*} (mapping : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ (Store C)) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (trace : List (TM2.Cfg RatInput.Alphabet Λ (Store C)))
    (before final : TM2.Cfg RatInput.Alphabet Λ (Store C))
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (mapping point)=LabelMap.statement mapping (old point)) :
    (trace.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping before) ∧
    (trace.map (LabelMap.configuration mapping)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) := by
  have proper := NativeMulLink.no_early_halt_port old port atPort trace final chain last active
  have path := LabelMap.actual_path_on mapping old (program caller) trace before final first chain last
    (by intro current member point selected;exact same point (by intro equal;subst point;exact proper current member selected))
  exact ⟨path.1,path.2.1,path.2.2.1⟩

theorem q_state (point : QLoop.Label) (memory : Store C) (contents : Stack → List Bool) :
    LabelMap.configuration qLabel (QLoop.state point memory contents)=state (qLabel point) memory contents := rfl

/-- The accepted complete Q producer is now an actual prefix of the
single full exponent source, ending at its real next packet-call label. -/
theorem q_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state (.packet .copyQ 0) afterMemory
        (QLoop.bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ QLoop.fullCoefficient*(QLoop.fullScale background tail budget number)^5 ∧
      RatInput.occupied
        (QLoop.bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []) ≤
        512*QLoop.fullScale background tail budget number := by
  obtain ⟨afterMemory,part,context,flags,bounds,_proper,finalMass⟩ := QLoop.Public.actual background memory tail budget number input
  have path := label_path qLabel (QLoop.program .halt) caller .done rfl part.trace _ _ part.first part.chain part.last rfl
    (by intro point different;simp only [qLabel,different,ite_false,program])
  have startName : qLabel (default : QLoop.Label)=(default : Label) := rfl
  have endName : qLabel .done=.packet .copyQ 0 := rfl
  refine ⟨afterMemory,⟨part.trace.map (LabelMap.configuration qLabel),?_,path.2.1,?_⟩,context,flags,?_,finalMass⟩
  · simpa only [q_state,startName] using path.1
  · simpa only [q_state,endName] using path.2.2
  · simpa only [List.length_map] using bounds.count

end RootB234.PrepExponent.Global
