module
public import PaperProofs.Common.PSTR_TM_MulAppendCode_086

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulAppendTrace087
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulAppendCode086
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "cols" => PSTRTMMulPassCode079.columns
local notation "leftCols" => PSTRTMMulPassCode079.leftColumns

def seekTrace (left : List Bool) : List Triple → List (MachineState 17)
  | [] => [state 0 left [],state 1 (false::left) []]
  | (c,a,b)::later =>
    [state 0 left (c::true::a::true::b::true::cols later),
      state 1 (c::left) (true::a::true::b::true::cols later),
      state 0 (true::c::left) (a::true::b::true::cols later),
      state 1 (a::true::c::left) (true::b::true::cols later),
      state 0 (true::a::true::c::left) (b::true::cols later),
      state 1 (b::true::a::true::c::left) (true::cols later)] ++
      seekTrace (true::b::true::a::true::c::left) later

theorem seek_head (left : List Bool) (triples : List Triple) :
    (seekTrace left triples).head?=some (state 0 left (cols triples)) := by
  cases triples with
  | nil => rfl
  | cons triple later => obtain ⟨c,a,b⟩ := triple; rfl
theorem seek_last (left : List Bool) (triples : List Triple) :
    (seekTrace left triples).getLast?=some (state 1 (false::(leftCols triples.reverse++left)) []) := by
  induction triples generalizing left with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    have hne : seekTrace (true::b::true::a::true::c::left) later≠[] := by
      intro h
      have hh := seek_head (true::b::true::a::true::c::left) later
      simp [h] at hh
    simp only [seekTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMMulPassCode079.leftColumns,List.reverse_cons,List.flatMap_append,List.append_assoc]
theorem seek_length (left : List Bool) (triples : List Triple) : (seekTrace left triples).length=6*triples.length+2 := by
  induction triples generalizing left with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simp only [seekTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega
theorem seek_chain (left : List Bool) (triples : List Triple) :
    (seekTrace left triples).IsChain (fun a b => Turing.TM0.step appendMachine a=some b) := by
  induction triples generalizing left with
  | nil => simp [seekTrace,List.isChain_cons_cons,Turing.TM0.step,appendMachine,state,Turing.Tape.mk₂]
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [seekTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,appendMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [seek_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,appendMachine,state,Turing.Tape.mk₂]
theorem seek_advance (left : List Bool) :
    Turing.TM0.step appendMachine (state 1 (false::left) [])=some (state 2 left []) := by
  simp [Turing.TM0.step,appendMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]

def allocateTrace (left : List Bool) : List (MachineState 17) :=
  [state 2 left [],state 3 left [false],state 4 (false::left) [],state 5 (false::left) [true],
    state 6 (true::false::left) [],state 7 (true::false::left) [false],
    state 8 (false::true::false::left) [],state 9 (false::true::false::left) [true],
    state 10 (true::false::true::false::left) [],state 11 (true::false::true::false::left) [false],
    state 12 (false::true::false::true::false::left) [],state 13 (false::true::false::true::false::left) [true]]
theorem allocate_head (left : List Bool) : (allocateTrace left).head?=some (state 2 left []) := rfl
theorem allocate_last (left : List Bool) : (allocateTrace left).getLast?=some (state 13 (false::true::false::true::false::left) [true]) := rfl
theorem allocate_length (left : List Bool) : (allocateTrace left).length=12 := rfl
theorem allocate_chain (left : List Bool) :
    (allocateTrace left).IsChain (fun a b => Turing.TM0.step appendMachine a=some b) := by
  simp [allocateTrace,List.isChain_cons_cons,Turing.TM0.step,appendMachine,state,Turing.Tape.mk₂]

theorem allocate_advance (archive : List Bool) (triples : List Triple) :
    Turing.TM0.step appendMachine
      (state 13 (false::true::false::true::false::(leftCols triples.reverse++false::archive)) [true]) =
      some (liftRewind (PSTRTMMulRewind085.state 0 (leftCols (paddedTriples triples).reverse++false::archive) [])) := by
  have hl : leftCols (paddedTriples triples).reverse = [true,false,true,false,true,false]++leftCols triples.reverse := by
    simp [paddedTriples,List.reverse_append,PSTRTMMulPassCode079.leftColumns]
  rw [hl]
  simp [Turing.TM0.step,appendMachine,state,liftRewind,embedRewind,PSTRTMMulRewind085.state,
    Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 17)) (last first : MachineState 17)
    (hx : xs.IsChain (fun a b => Turing.TM0.step appendMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step appendMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step appendMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step appendMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def appendTrace (archive : List Bool) (triples : List Triple) : List (MachineState 17) :=
  seekTrace (false::archive) triples ++ allocateTrace (leftCols triples.reverse++false::archive) ++
    (PSTRTMMulRewind085.fullTrace archive (paddedTriples triples).reverse []).map liftRewind
def appendFinal (archive : List Bool) (triples : List Triple) : MachineState 17 :=
  state 17 (false::archive) (cols (paddedTriples triples))

theorem append_head (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).head?=some (state 0 (false::archive) (cols triples)) := by
  simp only [appendTrace,List.head?_append,seek_head,Option.some_or]
theorem append_last (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).getLast?=some (appendFinal archive triples) := by
  simp only [appendTrace,List.getLast?_append,List.getLast?_map,PSTRTMMulRewind085.full_last,
    List.reverse_reverse,List.append_nil,Option.map_some,Option.some_or]
  rfl
theorem append_length (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).length=12*triples.length+23 := by
  simp only [appendTrace,List.length_append,List.length_map,seek_length,allocate_length,
    PSTRTMMulRewind085.full_length,List.length_reverse,paddedTriples,List.length_append,List.length_cons,List.length_nil]
  omega

theorem append_chain (archive : List Bool) (triples : List Triple) :
    (appendTrace archive triples).IsChain (fun a b => Turing.TM0.step appendMachine a=some b) := by
  unfold appendTrace
  refine append_link _ _
    (state 13 (false::true::false::true::false::(leftCols triples.reverse++false::archive)) [true])
    (liftRewind (PSTRTMMulRewind085.state 0 (leftCols (paddedTriples triples).reverse++false::archive) []))
    ?_ (rewind_chain _ (PSTRTMMulRewind085.full_chain archive (paddedTriples triples).reverse [])) ?_ ?_
    (allocate_advance archive triples)
  · exact append_link _ _ _ _ (seek_chain (false::archive) triples) (allocate_chain _)
      (seek_last (false::archive) triples) (allocate_head _) (seek_advance _)
  · simp only [List.getLast?_append,allocate_last,Option.some_or]
  · simp only [List.head?_map,PSTRTMMulRewind085.full_head,Option.map_some]

/-- Actual framed high-zero allocation with blank right tail. Every
archive cell beyond the REAL false guard is retained at the SAME offset. -/
theorem append_runsFrom (archive : List Bool) (triples : List Triple) :
    PSTRTMSeq005.RunsFrom appendMachine (state 0 (false::archive) (cols triples))
      (appendTrace archive triples) (appendFinal archive triples) :=
  ⟨append_head archive triples,append_chain archive triples,append_last archive triples,append_halt _ _⟩

theorem append_runs (triples : List Triple) :
    Runs appendMachine (cols triples) (appendTrace [] triples) (appendFinal [] triples) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa [Turing.TM0.init,state,Turing.Tape.mk₁,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false] using append_head [] triples
  · exact append_chain [] triples
  · exact append_last [] triples
  · exact append_halt _ _

theorem append_final_tape (triples : List Triple) :
    (appendFinal [] triples).Tape=Turing.Tape.mk₁ (cols (paddedTriples triples)) := by
  simp only [appendFinal,state,Turing.Tape.mk₁,Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem columns_length (triples : List Triple) : (cols triples).length=6*triples.length := by
  induction triples with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    change (cols later).length+6=6*(later.length+1)
    rw [ih]
    omega

/-- Every high-zero data/true-flag cell is actually allocated and all
rewinds charged. No padding/width certificate is supplied as input. -/
theorem append_computes (triples : List Triple) :
    computes appendMachine (cols triples) (cols (paddedTriples triples)) (12*triples.length+23) (30*triples.length+47) := by
  refine ⟨appendTrace [] triples,appendFinal [] triples,append_runs triples,?_,(append_length [] triples).le,?_⟩
  · rw [append_final_tape]
    simp [Turing.Tape.mk₁,Turing.Tape.mk₂]
  · have hs := PSTRTMTrace002.visitedSpace_le appendMachine (cols triples).length (appendTrace [] triples)
    rw [columns_length,append_length] at hs
    rw [columns_length]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulAppendTrace087
