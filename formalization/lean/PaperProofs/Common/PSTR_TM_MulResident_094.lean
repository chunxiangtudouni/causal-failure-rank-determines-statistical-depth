module
public import PaperProofs.Common.PSTR_TM_MulLoopRun_093

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulResident094
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulLoopCode088 PSTRTMMulLoopValue091 PSTRTMMulLoopIteration092 PSTRTMMulLoopRun093
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns

def scanTrace (left : List Bool) : List Triple → List (MachineState 263)
  | [] => [state 0 left [],state 1 (false::left) []]
  | (c,a,b)::later =>
    [state 0 left (c::true::a::true::b::true::cols later),
      state 1 (c::left) (true::a::true::b::true::cols later),
      state 0 (true::c::left) (a::true::b::true::cols later),
      state 1 (a::true::c::left) (true::b::true::cols later),
      state 0 (true::a::true::c::left) (b::true::cols later),
      state 1 (b::true::a::true::c::left) (true::cols later)] ++
      scanTrace (true::b::true::a::true::c::left) later

theorem scan_head (left : List Bool) (triples : List Triple) :
    (scanTrace left triples).head?=some (state 0 left (cols triples)) := by
  cases triples with
  | nil => rfl
  | cons triple later => obtain ⟨c,a,b⟩ := triple; rfl
theorem scan_last (left : List Bool) (triples : List Triple) :
    (scanTrace left triples).getLast?=some (state 1 (false::(leftCols triples.reverse++left)) []) := by
  induction triples generalizing left with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    have hne : scanTrace (true::b::true::a::true::c::left) later≠[] := by
      intro h
      have hh := scan_head (true::b::true::a::true::c::left) later
      simp [h] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMMulPassCode079.leftColumns,List.reverse_cons,List.flatMap_append,List.append_assoc]
theorem scan_length (left : List Bool) (triples : List Triple) : (scanTrace left triples).length=6*triples.length+2 := by
  induction triples generalizing left with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega
theorem scan_chain (left : List Bool) (triples : List Triple) :
    (scanTrace left triples).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) := by
  induction triples generalizing left with
  | nil => simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [scanTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,loopMachine,state,Turing.Tape.mk₂]

theorem scan_advance (archive : List Bool) (triples : List Triple) :
    Turing.TM0.step loopMachine (state 1 (false::(leftCols triples.reverse++false::archive)) [])=
      some (entry archive triples) := by
  simp [Turing.TM0.step,loopMachine,state,entry,liftHalf,halfLabel,PSTRTMMulHalfCode082.state,
    Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]

def residentTrace (triples : List Triple) : List (MachineState 263) :=
  scanTrace [false] triples++loopTrace [] triples.length triples
def residentFinal (triples : List Triple) : MachineState 263 := loopFinal [] triples.length triples
def result (triples : List Triple) : List Triple := endTriples triples.length triples

theorem resident_runs (triples : List Triple) :
    Runs loopMachine (cols triples) (residentTrace triples) (residentFinal triples) := by
  have hb := bValue_lt_width triples
  apply PSTRTMTrace002.runs_of_chain
  · simp only [residentTrace,List.head?_append,scan_head,Option.some_or]
    simp [Turing.TM0.init,state,Turing.Tape.mk₁,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]
  · apply (scan_chain [false] triples).append (loop_chain [] triples.length triples hb)
    intro before hbefore after hafter
    rw [scan_last] at hbefore
    rw [loop_head] at hafter
    have he := Option.mem_some_iff.mp hbefore
    have hf := Option.mem_some_iff.mp hafter
    subst before
    subst after
    exact scan_advance [] triples
  · simp only [residentTrace,List.getLast?_append,loop_last [] triples.length triples hb,Option.some_or,residentFinal]
  · exact loop_halt _ _

theorem resident_final_tape (triples : List Triple) :
    (residentFinal triples).Tape=Turing.Tape.mk₁ (cols (result triples)) := by
  simp only [residentFinal,loopFinal,state,result,Turing.Tape.mk₁,Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem resident_result_values (triples : List Triple) :
    PSTRTMMulPassCode079.cValue (result triples)=PSTRTMMulPassCode079.cValue triples+
      PSTRTMMulPassCode079.aValue triples*PSTRTMMulPassCode079.bValue triples ∧
    PSTRTMMulPassCode079.bValue (result triples)=0 :=
  end_values triples.length triples (bValue_lt_width triples)

theorem resident_length_le (triples : List Triple) :
    (residentTrace triples).length ≤ 256*(triples.length+1)^2 := by
  have hl := loop_length_le [] triples.length triples
  simp only [residentTrace,List.length_append,scan_length]
  nlinarith

theorem resident_visitedSpace_le (triples : List Triple) :
    visitedSpace loopMachine (cols triples).length (residentTrace triples) ≤ 1024*(triples.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le loopMachine (cols triples).length (residentTrace triples)
  have ht := resident_length_le triples
  rw [PSTRTMMulAppendTrace087.columns_length] at hs ⊢
  nlinarith

/-- ONE fixed264-label real multiplication accumulator on the resident
six-cell tuples. This is a full original Runs trace with actual bit-cost,
but DOES NOT yet claim original encodeNat a++encodeNat b input or a
canonical encodeNat(a*b) output. Those concrete transports remain owed. -/
theorem resident_computes (triples : List Triple) :
    computes loopMachine (cols triples) (cols (result triples))
      (256*(triples.length+1)^2) (1024*(triples.length+1)^2) := by
  refine ⟨residentTrace triples,residentFinal triples,resident_runs triples,?_,
    resident_length_le triples,resident_visitedSpace_le triples⟩
  rw [resident_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulResident094
