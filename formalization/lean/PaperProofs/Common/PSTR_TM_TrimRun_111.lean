module
public import PaperProofs.Common.PSTR_TM_TrimBackward_110

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimRun111
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103

def scanTrace (left : List Bool) : List Bool → List (MachineState 16)
  | [] => [state 0 left [],state 1 (false::left) []]
  | bit::later => [state 0 left (bit::true::PSTRTMIncrement009.blocks later),state 1 (bit::left) (true::PSTRTMIncrement009.blocks later)] ++
      scanTrace (true::bit::left) later
theorem scan_head (left digits : List Bool) :
    (scanTrace left digits).head?=some (state 0 left (PSTRTMIncrement009.blocks digits)) := by cases digits <;> rfl
theorem scan_last (left digits : List Bool) :
    (scanTrace left digits).getLast?=some (state 1 (false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) []) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : scanTrace (true::bit::left) later≠[] := by
      intro h
      have hh := scan_head (true::bit::left) later
      simp [h] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]
theorem scan_length (left digits : List Bool) : (scanTrace left digits).length=2*digits.length+2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih => simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]; omega
theorem scan_chain (left digits : List Bool) :
    (scanTrace left digits).IsChain (fun x y => Turing.TM0.step trimMachine x=some y) := by
  induction digits generalizing left with
  | nil => simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [scanTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]
theorem scan_advance (left : List Bool) :
    Turing.TM0.step trimMachine (state 1 (false::left) [])=some (state 2 left []) := by
  simp [Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]
theorem enter_advance (reversed : List Bool) :
    Turing.TM0.step trimMachine (state 2 (PSTRTMRawNat010.leftBlocks reversed++[false]) [])=
      some (PSTRTMTrimBackward110.initial reversed) := by
  cases reversed <;> simp [PSTRTMTrimBackward110.initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]

def trimTrace (digits : List Bool) : List (MachineState 16) :=
  scanTrace [false] digits ++ (state 2 (PSTRTMRawNat010.leftBlocks digits.reverse++[false]) [] ::PSTRTMTrimBackward110.backTrace digits.reverse)
def trimFinal (digits : List Bool) : MachineState 16 := state 14 [false] (PSTRTMIncrement009.blocks (trimmed digits))

theorem trim_runs (digits : List Bool) : Runs trimMachine (PSTRTMIncrement009.blocks digits) (trimTrace digits) (trimFinal digits) := by
  apply PSTRTMTrace002.runs_of_chain
  · simp only [trimTrace,List.head?_append,scan_head,Option.some_or]
    simp [Turing.TM0.init,state,Turing.Tape.mk₁,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]
  · apply (scan_chain [false] digits).append
    · apply List.isChain_cons.mpr
      constructor
      · intro after ha
        rw [PSTRTMTrimBackward110.back_head] at ha
        have he := Option.mem_some_iff.mp ha
        subst after
        exact enter_advance digits.reverse
      · exact PSTRTMTrimBackward110.back_chain digits.reverse
    · intro before hb after ha
      rw [scan_last] at hb
      simp only [List.head?_cons,Option.mem_some_iff] at ha
      have he := Option.mem_some_iff.mp hb
      subst before
      subst after
      exact scan_advance _
  · have hne : PSTRTMTrimBackward110.backTrace digits.reverse≠[] := by
      intro h
      have hh := PSTRTMTrimBackward110.back_head digits.reverse
      simp [h] at hh
    simp only [trimTrace,List.getLast?_append,List.getLast?_cons_of_ne_nil hne,
      PSTRTMTrimBackward110.back_last,Option.some_or,trimFinal]
    rfl
  · exact trim_halt _ _

theorem trim_final_tape (digits : List Bool) :
    (trimFinal digits).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))) := by
  have ht : (trimFinal digits).Tape=Turing.Tape.mk₁ (PSTRTMIncrement009.blocks (trimmed digits)) := by
    simp only [trimFinal,state,Turing.Tape.mk₁,Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false]
  rw [ht,PSTRTMTrimValue104.trimmed_canonical]

theorem trim_length_le (digits : List Bool) : (trimTrace digits).length ≤ 16*(digits.length+1) := by
  have hb := PSTRTMTrimBackward110.back_length_le digits.reverse
  rw [List.length_reverse] at hb
  simp only [trimTrace,List.length_append,List.length_cons,scan_length]
  omega

theorem trim_visitedSpace_le (digits : List Bool) :
    visitedSpace trimMachine (PSTRTMIncrement009.blocks digits).length (trimTrace digits) ≤ 64*(digits.length+1) := by
  have hs := PSTRTMTrace002.visitedSpace_le trimMachine (PSTRTMIncrement009.blocks digits).length (trimTrace digits)
  have ht := trim_length_le digits
  rw [PSTRTMIncrement009.blocks_length] at hs ⊢
  omega

/-- Actual flag erasure/zero allocation/rewind produces EXACT canonical
payload in linear real cost. Empty and all-zero inputs allocate ONE false
digit; no semantic truncation or free replacement of the original tape. -/
theorem trim_computes (digits : List Bool) :
    computes trimMachine (PSTRTMIncrement009.blocks digits)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits)))
      (16*(digits.length+1)) (64*(digits.length+1)) := by
  refine ⟨trimTrace digits,trimFinal digits,trim_runs digits,?_,trim_length_le digits,trim_visitedSpace_le digits⟩
  rw [trim_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrimRun111
