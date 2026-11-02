module
public import PaperProofs.Common.PSTR_TM_MulExpandUnit_097
public import PaperProofs.Common.PSTR_TM_BinaryAdd_024

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandRun098
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulExpandCode095 PSTRTMMulExpandUnit097
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns
local notation "operandCols" => PSTRTMBinaryAdd024.operandColumns

def prefixDigits (pairs : List (Bool×Bool)) : List Bool := pairs.flatMap (fun (a,b) => [false,a,b])

theorem prefix_append (first second : List (Bool×Bool)) : prefixDigits (first++second)=prefixDigits first++prefixDigits second := by
  simp only [prefixDigits,List.flatMap_append]
theorem prefix_length (pairs : List (Bool×Bool)) : (prefixDigits pairs).length=3*pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [prefixDigits,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons] at ih ⊢
    omega
theorem prefix_left (pairs : List (Bool×Bool)) :
    PSTRTMRawNat010.leftBlocks (prefixDigits pairs).reverse=leftCols (triples pairs).reverse := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [prefixDigits,List.flatMap_cons,triples,List.map_cons,List.reverse_append,List.reverse_cons,
      PSTRTMRawNat010.leftBlocks,List.flatMap_append,PSTRTMMulPassCode079.leftColumns] at ih ⊢
    simpa only [List.flatMap_cons,List.flatMap_nil,List.reverse_nil,List.cons_append,List.nil_append,List.append_assoc] using
      congrArg (fun bits => bits++[true,b,true,a,true,false]) ih

def finishTrace (previous : List (Bool×Bool)) : List (MachineState 111) :=
  [state 0 (PSTRTMRawNat010.leftBlocks (prefixDigits previous).reverse) [],
    state 1 (false::PSTRTMRawNat010.leftBlocks (prefixDigits previous).reverse) []] ++
    (PSTRTMMulRewind085.fullTrace [] (triples previous).reverse []).map liftRewind

theorem finish_head (previous : List (Bool×Bool)) :
    (finishTrace previous).head?=some (state 0 (PSTRTMRawNat010.leftBlocks (prefixDigits previous).reverse) []) := rfl
theorem finish_last (previous : List (Bool×Bool)) :
    (finishTrace previous).getLast?=some (state 111 [false] (cols (triples previous))) := by
  simp only [finishTrace,List.getLast?_append,List.getLast?_map,PSTRTMMulRewind085.full_last,
    List.reverse_reverse,List.append_nil,Option.map_some,Option.some_or]
  rfl
theorem finish_length (previous : List (Bool×Bool)) : (finishTrace previous).length=6*previous.length+5 := by
  simp only [finishTrace,List.length_append,List.length_cons,List.length_nil,List.length_map,
    PSTRTMMulRewind085.full_length,List.length_reverse,triples,List.length_map]
  omega

theorem finish_chain (previous : List (Bool×Bool)) :
    (finishTrace previous).IsChain (fun a b => Turing.TM0.step expandMachine a=some b) := by
  unfold finishTrace
  apply List.IsChain.append
  · simp [List.isChain_cons_cons,Turing.TM0.step,expandMachine,state,Turing.Tape.mk₂]
  · exact PSTRTMMulExpandLift096.rewind_chain _ (PSTRTMMulRewind085.full_chain [] (triples previous).reverse [])
  · intro before hb after ha
    simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
    simp only [List.head?_map,PSTRTMMulRewind085.full_head,Option.map_some,Option.mem_some_iff] at ha
    subst before
    subst after
    rw [prefix_left]
    simp [Turing.TM0.step,expandMachine,state,liftRewind,rewindLabel,PSTRTMMulRewind085.state,
      Turing.Tape.mk₂,PSTRTMRawNat010.blank_append_false,PSTRTMRawNat010.blank_single_false]

def loopTrace (previous : List (Bool×Bool)) : List (Bool×Bool) → List (MachineState 111)
  | [] => finishTrace previous
  | (a,b)::later => unitTrace (prefixDigits previous) a b (operandCols later) ++ loopTrace (previous++[(a,b)]) later

theorem loop_head (previous later : List (Bool×Bool)) :
    (loopTrace previous later).head?=some (state 0 (PSTRTMRawNat010.leftBlocks (prefixDigits previous).reverse) (operandCols later)) := by
  cases later with
  | nil => exact finish_head previous
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp only [loopTrace,List.head?_append,unit_head,Option.some_or,PSTRTMBinaryAdd024.operandColumns,List.flatMap_cons,
      List.cons_append,List.nil_append]
theorem loop_last (previous later : List (Bool×Bool)) :
    (loopTrace previous later).getLast?=some (state 111 [false] (cols (triples (previous++later)))) := by
  induction later generalizing previous with
  | nil => simpa only [loopTrace,List.append_nil] using finish_last previous
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [loopTrace,List.getLast?_append,ih,Option.some_or,List.append_assoc,List.singleton_append]

theorem loop_chain (previous later : List (Bool×Bool)) :
    (loopTrace previous later).IsChain (fun a b => Turing.TM0.step expandMachine a=some b) := by
  induction later generalizing previous with
  | nil => exact finish_chain previous
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [loopTrace]
    apply (unit_chain (prefixDigits previous) a b (operandCols later)).append (ih (previous++[(a,b)]))
    intro before hb after ha
    rw [unit_last] at hb
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp hb
    have hf := Option.mem_some_iff.mp ha
    subst before
    subst after
    have hp : prefixDigits (previous++[(a,b)])=prefixDigits previous++[false,a,b] := by
      rw [prefix_append]
      rfl
    rw [hp]
    exact restore_advance (prefixDigits previous) a b (operandCols later)

theorem loop_length_le (previous later : List (Bool×Bool)) :
    (loopTrace previous later).length ≤ 64*(previous.length+later.length+1)*(later.length+1) := by
  induction later generalizing previous with
  | nil =>
    simp only [loopTrace,finish_length,List.length_nil]
    omega
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have hn := ih (previous++[(a,b)])
    simp only [List.length_append,List.length_cons,List.length_nil] at hn
    simp only [loopTrace,List.length_append,unit_length,prefix_length,List.length_cons]
    nlinarith

def expandTrace (pairs : List (Bool×Bool)) : List (MachineState 111) := loopTrace [] pairs
def expandFinal (pairs : List (Bool×Bool)) : MachineState 111 := state 111 [false] (cols (triples pairs))

theorem expand_runs (pairs : List (Bool×Bool)) :
    Runs expandMachine (operandCols pairs) (expandTrace pairs) (expandFinal pairs) := by
  apply PSTRTMTrace002.runs_of_chain
  · have hd : (default : Fin 112)=0 := rfl
    simpa only [expandTrace,prefixDigits,List.flatMap_nil,List.reverse_nil,PSTRTMRawNat010.leftBlocks,
      state,Turing.TM0.init,Turing.Tape.mk₁,hd] using loop_head [] pairs
  · exact loop_chain [] pairs
  · simpa only [expandTrace,expandFinal,List.nil_append] using loop_last [] pairs
  · exact expand_halt _ _

theorem expand_final_tape (pairs : List (Bool×Bool)) :
    (expandFinal pairs).Tape=Turing.Tape.mk₁ (cols (triples pairs)) := by
  simp only [expandFinal,state,Turing.Tape.mk₁,Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem expand_length_le (pairs : List (Bool×Bool)) : (expandTrace pairs).length ≤ 64*(pairs.length+1)^2 := by
  have hl := loop_length_le [] pairs
  simpa only [expandTrace,List.length_nil,Nat.zero_add,pow_two,Nat.mul_assoc] using hl

theorem operandColumns_length (pairs : List (Bool×Bool)) : (operandCols pairs).length=4*pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change (operandCols later).length+4=4*(later.length+1)
    rw [ih]
    omega

/-- Real expansion of the ORIGINAL045 operand columns. All C zero cells
and flags are written by expandMachine, A/B retained, and the full tape
is exactly the six-cell format with head physically rewound to its start.
Blank original left/right tails are required; no arbitrary archive frame. -/
theorem expand_computes (pairs : List (Bool×Bool)) :
    computes expandMachine (operandCols pairs) (cols (triples pairs))
      (64*(pairs.length+1)^2) (256*(pairs.length+1)^2) := by
  refine ⟨expandTrace pairs,expandFinal pairs,expand_runs pairs,?_,expand_length_le pairs,?_⟩
  · rw [expand_final_tape]
    simp [Turing.Tape.mk₁,Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le expandMachine (operandCols pairs).length (expandTrace pairs)
    have ht := expand_length_le pairs
    rw [operandColumns_length] at hs ⊢
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandRun098
