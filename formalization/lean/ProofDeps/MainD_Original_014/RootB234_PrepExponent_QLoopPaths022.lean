module

public import RootB234_PrepExponent_QLoopCode021
public import RootB234_PrepExponent_NCountPublic019

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def bank (background : Stack → List Bool) (cache counter input trash : List Bool) : Stack → List Bool :=
  fun slot => if slot=7 then cache else if slot=11 then counter else if slot=15 then input else if slot=12 then trash
    else if slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=10 ∨ slot=13 ∨ slot=14 then [] else background slot

def state (point : Label) (memory : Store C) (contents : Stack → List Bool) : State C := ⟨some point,memory,contents⟩
def rootContext (memory : Store C) : C := memory.1.1.1.2

theorem label_path {Λ : Type*} (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ (Store C)) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (run : List (TM2.Cfg RatInput.Alphabet Λ (Store C)))
    (before final : TM2.Cfg RatInput.Alphabet Λ (Store C))
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (rename point)=LabelMap.statement rename (old point)) :
    (run.map (LabelMap.configuration rename)).head?=some (LabelMap.configuration rename before) ∧
    (run.map (LabelMap.configuration rename)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (LabelMap.configuration rename)).getLast?=some (LabelMap.configuration rename final) := by
  have proper := NativeMulLink.no_early_halt_port old port atPort run final chain last active
  have path := LabelMap.actual_path_on rename old (program caller) run before final first chain last
    (by intro current member point selected;exact same point (by intro equal;subst point;exact proper current member selected))
  exact ⟨path.1,path.2.1,path.2.2.1⟩

theorem store_label_path {σ Λ : Type*} (iso : σ ≃ Store C) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (run : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (rename point)=LabelMap.statement rename (StoreIso.statement iso (old point))) :
    let cfg := fun current => LabelMap.configuration rename (StoreIso.configuration iso current)
    (run.map cfg).head?=some (cfg before) ∧
    (run.map cfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map cfg).getLast?=some (cfg final) := by
  let changed := StoreIso.machine iso old
  have stored := StoreIso.actual_path_on iso old changed run before final first chain last
    (by intro current member point selected;rfl)
  have atPort' : changed port=.halt := by change StoreIso.statement iso (old port)=_;rw [atPort];rfl
  have path := label_path rename changed caller port atPort' _ _ _ stored.1 stored.2.1 stored.2.2.1 active same
  simp only [List.map_map,Function.comp_def] at path
  exact path

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.edge {caller : Statement C} {before final : State C}
    (step : TM2.step (program caller) before=some final) : Segment caller before final :=
  ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨step,List.isChain_singleton _⟩,rfl⟩

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

theorem Segment.append_length {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length ≤ front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length ≤ _
  simp only [List.length_append,List.length_tail]
  omega

theorem packet_actual (caller : Statement C) (roles : Stack ≃ Stack) (copy : Bool)
    (mapping : RatPacketTransport.Label → Label)
    (agrees : ∀ point,point≠4→program caller (mapping point)=
      LabelMap.statement mapping (RatPacketTransport.atProgram roles copy point))
    (background : Stack → List Bool) (context : PacketUnary.Store (Arithmetic.Aux×C))
    (flags : RatOutput.Store) (value : Rat) (source target : List Bool) :
    ∃ part : Segment caller
      (LabelMap.configuration mapping (RatPacketTransport.atState roles background 0 context flags
        (RatInput.Encoder.packet value source) [] target))
      (LabelMap.configuration mapping (RatPacketTransport.atState roles background 4 context (false,false)
        (if copy then RatInput.Encoder.packet value source else source) [] (RatInput.Encoder.packet value target))),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨run,facts⟩ := RatPacketTransport.at_actual roles copy background context flags value source target
  have path := label_path mapping (RatPacketTransport.atProgram roles copy) caller 4 rfl
    run _ _ facts.first facts.chain facts.last rfl agrees
  exact ⟨⟨run.map (LabelMap.configuration mapping),path.1,path.2.1,path.2.2⟩,
    by simpa only [List.length_map] using facts.count⟩

theorem literalQ_step (caller : Statement C) (memory : Store C) (before : Stack → List Bool) :
    TM2.step (program caller) (state .literalQ memory before)=
      some (state (.count default) memory (Function.update before 7 (RatInput.Encoder.packet (12 : Rat) []++before 7))) := by
  change some (TM2.stepAux (prepend 7 _ _) memory before)=_
  rw [prepend_step]
  rfl

theorem literalTwo_step (caller : Statement C) (memory : Store C) (before : Stack → List Bool) :
    TM2.step (program caller) (state .literalTwo memory before)=
      some (state (.mul default) memory (Function.update before 15 (RatInput.Encoder.packet (2 : Rat) []++before 15))) := by
  change some (TM2.stepAux (prepend 15 _ _) memory before)=_
  rw [prepend_step]
  rfl

theorem count_path (caller : Statement C) (run : List (NCount.State (Arithmetic.Aux×C)))
    (before final : NCount.State (Arithmetic.Aux×C))
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step (NCount.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map (LabelMap.configuration countLabel)).head?=some (LabelMap.configuration countLabel before) ∧
    (run.map (LabelMap.configuration countLabel)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (LabelMap.configuration countLabel)).getLast?=some (LabelMap.configuration countLabel final) := by
  exact label_path countLabel (NCount.program .halt) caller .done rfl run before final first chain last active
    (by intro point different;simp only [countLabel,different,ite_false,program])

theorem mul_path (caller : Statement C) (run : List (Arithmetic.State (PacketUnary.Store C)))
    (before final : Arithmetic.State (PacketUnary.Store C))
    (first : run.head?=some before) (chain : run.IsChain (fun a b => TM2.step Arithmetic.mulProgram a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    let cfg := fun current => LabelMap.configuration mulLabel (StoreIso.configuration (arithmeticIso C) current)
    (run.map cfg).head?=some (cfg before) ∧
    (run.map cfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map cfg).getLast?=some (cfg final) := by
  exact store_label_path (arithmeticIso C) mulLabel Arithmetic.mulProgram caller .done rfl run before final
    first chain last active (by intro point different;simp only [mulLabel,different,ite_false,program])

end RootB234.PrepExponent.QLoop
