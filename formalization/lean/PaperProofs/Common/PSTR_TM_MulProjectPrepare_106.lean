module
public import PaperProofs.Common.PSTR_TM_MulProjectUnit_102
public import PaperProofs.Common.PSTR_TM_PairRewind_105
public import PaperProofs.Common.PSTR_TM_MulAppendTrace_087

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectPrepare106
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulProjectCode100
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns

def quad (digits : List Bool) : List Bool := digits.flatMap (fun c => [c,false,false,false])
theorem quad_append (first second : List Bool) : quad (first++second)=quad first++quad second := by
  simp only [quad,List.flatMap_append]
theorem quad_length (digits : List Bool) : (quad digits).length=4*digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change (quad later).length+4=4*(later.length+1)
    rw [ih]
    omega
theorem quad_cBits (triples : List Triple) : quad (cBits triples)=quadBits triples := by
  induction triples with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    change c::false::false::false::quad (cBits later)=c::false::false::false::quadBits later
    rw [ih]

theorem rewind_chain (trace : List (MachineState 3))
    (old : trace.IsChain (fun x y => Turing.TM0.step PSTRTMMulRewind085.rewindMachine x=some y)) :
    (trace.map PSTRTMMulProjectLift101.liftRewind).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  apply (List.isChain_map _).mpr
  apply old.imp
  intro before after hs
  rw [PSTRTMMulProjectLift101.rewind_step,hs]
  rfl

def finishTrace (previous : List Bool) : List (MachineState 114) :=
  [state 0 (PSTRTMRawNat010.leftBlocks (quad previous).reverse) [],state 1 (false::PSTRTMRawNat010.leftBlocks (quad previous).reverse) []] ++
    (PSTRTMPairRewind105.fullTrace [] (quad previous).reverse []).map PSTRTMMulProjectLift101.liftRewind
theorem finish_head (previous : List Bool) :
    (finishTrace previous).head?=some (state 0 (PSTRTMRawNat010.leftBlocks (quad previous).reverse) []) := rfl
theorem finish_last (previous : List Bool) :
    (finishTrace previous).getLast?=some (state 113 [false] (PSTRTMIncrement009.blocks (quad previous))) := by
  simp only [finishTrace,List.getLast?_append,List.getLast?_map,PSTRTMPairRewind105.full_last,
    List.reverse_reverse,List.append_nil,Option.map_some,Option.some_or]
  rfl
theorem finish_length (previous : List Bool) : (finishTrace previous).length=8*previous.length+5 := by
  simp only [finishTrace,List.length_append,List.length_cons,List.length_nil,List.length_map,
    PSTRTMPairRewind105.full_length,List.length_reverse,quad_length]
  omega
theorem finish_chain (previous : List Bool) :
    (finishTrace previous).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  unfold finishTrace
  apply List.IsChain.append
  · simp [List.isChain_cons_cons,Turing.TM0.step,prepareMachine,state,Turing.Tape.mk₂]
  · exact rewind_chain _ (PSTRTMPairRewind105.full_chain [] (quad previous).reverse [])
  · intro before hb after ha
    simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
    simp only [List.head?_map,PSTRTMPairRewind105.full_head,Option.map_some,Option.mem_some_iff] at ha
    subst before
    subst after
    simp [Turing.TM0.step,prepareMachine,state,PSTRTMMulProjectLift101.liftRewind,liftOld,oldLabel,
      PSTRTMMulExpandCode095.liftRewind,PSTRTMMulExpandCode095.rewindLabel,PSTRTMMulRewind085.state,
      Turing.Tape.mk₂,PSTRTMRawNat010.blank_append_false,PSTRTMRawNat010.blank_single_false]

def unitTrace (previous : List Bool) (c a b : Bool) (later : List Triple) : List (MachineState 114) :=
  [state 0 (PSTRTMRawNat010.leftBlocks (quad previous).reverse) (c::true::a::true::b::true::cols later),
    state 1 (c::PSTRTMRawNat010.leftBlocks (quad previous).reverse) (true::a::true::b::true::cols later)] ++
    PSTRTMMulProjectUnit102.unitTrace (quad previous++[c]) a b (cols later)
theorem unit_head (previous : List Bool) (c a b : Bool) (later : List Triple) :
    (unitTrace previous c a b later).head?=some (state 0 (PSTRTMRawNat010.leftBlocks (quad previous).reverse) (cols ((c,a,b)::later))) := rfl
theorem unit_last (previous : List Bool) (c a b : Bool) (later : List Triple) :
    (unitTrace previous c a b later).getLast?=some (state (oldLabel 107)
      (false::true::false::true::false::PSTRTMRawNat010.leftBlocks (quad previous++[c]).reverse) (true::cols later)) := by
  simp only [unitTrace,List.getLast?_append,PSTRTMMulProjectUnit102.unit_last,Option.some_or]
theorem unit_chain (previous : List Bool) (c a b : Bool) (later : List Triple) :
    (unitTrace previous c a b later).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  unfold unitTrace
  apply List.IsChain.append
  · simp [List.isChain_cons_cons,Turing.TM0.step,prepareMachine,state,Turing.Tape.mk₂]
  · exact PSTRTMMulProjectUnit102.unit_chain (quad previous++[c]) a b (cols later)
  · intro before hb after ha
    simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
    simp only [PSTRTMMulProjectUnit102.unit_head,Option.mem_some_iff] at ha
    subst before
    subst after
    simp [Turing.TM0.step,prepareMachine,state,liftOld,oldLabel,PSTRTMMulExpandCode095.state,Turing.Tape.mk₂,
      PSTRTMRawNat010.leftBlocks,List.reverse_append]
theorem unit_length (previous : List Bool) (c a b : Bool) (later : List Triple) :
    (unitTrace previous c a b later).length=48*previous.length+40 := by
  simp only [unitTrace,List.length_append,List.length_cons,List.length_nil,PSTRTMMulProjectUnit102.unit_length,quad_length]
  omega

def loopTrace (previous : List Bool) : List Triple → List (MachineState 114)
  | [] => finishTrace previous
  | (c,a,b)::later => unitTrace previous c a b later++loopTrace (previous++[c]) later
theorem loop_head (previous : List Bool) (later : List Triple) :
    (loopTrace previous later).head?=some (state 0 (PSTRTMRawNat010.leftBlocks (quad previous).reverse) (cols later)) := by
  cases later with
  | nil => exact finish_head previous
  | cons triple later => obtain ⟨c,a,b⟩ := triple; simp only [loopTrace,List.head?_append,unit_head,Option.some_or]
theorem loop_last (previous : List Bool) (later : List Triple) :
    (loopTrace previous later).getLast?=some (state 113 [false] (PSTRTMIncrement009.blocks (quad (previous++cBits later)))) := by
  induction later generalizing previous with
  | nil => simpa only [loopTrace,cBits,List.map_nil,List.append_nil] using finish_last previous
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [loopTrace,List.getLast?_append,ih,Option.some_or,cBits,List.map_cons,List.append_assoc,List.singleton_append]
theorem loop_chain (previous : List Bool) (later : List Triple) :
    (loopTrace previous later).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  induction later generalizing previous with
  | nil => exact finish_chain previous
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [loopTrace]
    apply (unit_chain previous c a b later).append (ih (previous++[c]))
    intro before hb after ha
    rw [unit_last] at hb
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp hb
    have hf := Option.mem_some_iff.mp ha
    subst before
    subst after
    have hq : quad (previous++[c])=(quad previous++[c])++[false,false,false] := by
      rw [quad_append]
      simp only [quad,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,List.append_assoc]
    rw [hq]
    exact PSTRTMMulProjectUnit102.restore_advance (quad previous++[c]) (cols later)
theorem loop_length_le (previous : List Bool) (later : List Triple) :
    (loopTrace previous later).length ≤ 128*(previous.length+later.length+1)*(later.length+1) := by
  induction later generalizing previous with
  | nil => simp only [loopTrace,finish_length,List.length_nil]; omega
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    have hn := ih (previous++[c])
    simp only [List.length_append,List.length_cons,List.length_nil] at hn
    simp only [loopTrace,List.length_append,unit_length,List.length_cons]
    nlinarith

def prepareTrace (triples : List Triple) : List (MachineState 114) := loopTrace [] triples
def prepareFinal (triples : List Triple) : MachineState 114 := state 113 [false] (PSTRTMIncrement009.blocks (quad (cBits triples)))

theorem prepare_runs (triples : List Triple) :
    Runs prepareMachine (cols triples) (prepareTrace triples) (prepareFinal triples) := by
  apply PSTRTMTrace002.runs_of_chain
  · have hd : (default : Fin 115)=0 := rfl
    simpa only [prepareTrace,quad,List.flatMap_nil,List.reverse_nil,PSTRTMRawNat010.leftBlocks,state,Turing.TM0.init,Turing.Tape.mk₁,hd] using
      loop_head [] triples
  · exact loop_chain [] triples
  · simpa only [prepareTrace,prepareFinal,List.nil_append] using loop_last [] triples
  · exact prepare_halt _ _

theorem prepare_final_tape (triples : List Triple) :
    (prepareFinal triples).Tape=Turing.Tape.mk₁ (PSTRTMBinaryAdd024.resultColumns (PSTRTMCompactUnit048.paddedDigits (cBits triples))) := by
  have ht : (prepareFinal triples).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (quad (cBits triples))) := by
    simp only [prepareFinal,state,Turing.Tape.mk₁,Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht,quad_cBits,quad_format]
theorem prepare_length_le (triples : List Triple) : (prepareTrace triples).length ≤ 128*(triples.length+1)^2 := by
  have hl := loop_length_le [] triples
  simpa only [prepareTrace,List.length_nil,Nat.zero_add,pow_two,Nat.mul_assoc] using hl

/-- Real C-preserving/A,B-erasing8-cell preparation, with full Tape and
physical rewind. Its whole-tape result is exactly the isolated input ABI
of the FIRST frozen051 compactor, not merely equality of visible right₀. -/
theorem prepare_computes (triples : List Triple) :
    computes prepareMachine (cols triples)
      (PSTRTMBinaryAdd024.resultColumns (PSTRTMCompactUnit048.paddedDigits (cBits triples)))
      (128*(triples.length+1)^2) (512*(triples.length+1)^2) := by
  refine ⟨prepareTrace triples,prepareFinal triples,prepare_runs triples,?_,prepare_length_le triples,?_⟩
  · rw [prepare_final_tape]
    simp [Turing.Tape.mk₁,Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le prepareMachine (cols triples).length (prepareTrace triples)
    have ht := prepare_length_le triples
    rw [PSTRTMMulAppendTrace087.columns_length] at hs ⊢
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectPrepare106
