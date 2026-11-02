module
public import Structure.PA17_TM_RatArithmetic_Parse_002b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

open PSTRTMRawNat010

def streamState (q : Fin 18) (left right : List Bool) : MachineState 17 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def streamDone (base previous suffix : List Bool) : List (MachineState 17) :=
  [streamState 0 (processedLeft base previous) (false::suffix),
   streamState 17 (false::processedLeft base previous) suffix]

def streamTrace (base previous : List Bool) : List Bool → List Bool → List (MachineState 17)
  | [],suffix => streamDone base previous suffix
  | bit::later,suffix => (streamUnit base bit previous later suffix).map streamCfg ++
      streamTrace base (bit::previous) later suffix

theorem streamTrace_head (base previous digits suffix : List Bool) :
    (streamTrace base previous digits suffix).head? = some
      (streamState 0 (processedLeft base previous)
        (List.replicate digits.length true ++ false::(digits++suffix))) := by
  cases digits with
  | nil => rfl
  | cons bit later =>
    simp only [streamTrace,List.head?_append,List.head?_map,streamUnit_head,Option.map_some,Option.some_or]
    rfl

theorem streamTrace_last (base previous digits suffix : List Bool) :
    (streamTrace base previous digits suffix).getLast? = some
      (streamState 17 (false::(leftBlocks (digits.reverse++previous)++base)) suffix) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    simp only [streamTrace,List.getLast?_append,ih,Option.some_or,
      List.reverse_cons,List.append_assoc,List.singleton_append]

theorem streamTrace_length (base previous digits suffix : List Bool) :
    (streamTrace base previous digits suffix).length = digits.length^2+9*digits.length+2 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hmap : ((streamUnit base bit previous later suffix).map streamCfg).length =
        (streamUnit base bit previous later suffix).length := List.length_map _
    change (((streamUnit base bit previous later suffix).map streamCfg) ++
      streamTrace base (bit::previous) later suffix).length = _
    rw [List.length_append,hmap,streamUnit_length,ih,List.length_cons]
    ring

theorem streamDone_chain (base previous suffix : List Bool) :
    (streamDone base previous suffix).IsChain (fun before after => Turing.TM0.step streamMachine before = some after) := by
  simp [streamDone,List.isChain_cons_cons,Turing.TM0.step,streamMachine,streamState,Turing.Tape.mk₂]

theorem streamTrace_chain (base previous digits suffix : List Bool) :
    (streamTrace base previous digits suffix).IsChain (fun before after => Turing.TM0.step streamMachine before = some after) := by
  induction digits generalizing previous with
  | nil => exact streamDone_chain base previous suffix
  | cons bit later ih =>
    rw [streamTrace]
    apply (liftedUnit_chain base bit previous later suffix).append (ih (bit::previous))
    intro before hb after ha
    simp only [List.getLast?_map,streamUnit_last,Option.map_some,Option.mem_some_iff] at hb
    simp only [streamTrace_head,Option.mem_some_iff] at ha
    subst before
    subst after
    simp [Turing.TM0.step,streamMachine,streamCfg,streamLabel,streamState,processedLeft,leftBlocks,
      rawNatMachine,state,Turing.Tape.mk₂,List.replicate_succ]

theorem stream_halt (left right : List Bool) :
    Turing.TM0.step streamMachine (streamState 17 left right) = none := by
  simp [Turing.TM0.step,streamMachine,streamState]

def streamInitial (base digits suffix : List Bool) : MachineState 17 :=
  streamState 0 base (rawField digits++suffix)

def streamFinal (base digits suffix : List Bool) : MachineState 17 :=
  streamState 17 (false::(leftBlocks digits.reverse++base)) suffix

/-- Actual framed stream parser. Header cells become flagged payload
in-place, the one false field-end cell remains, and the real head advances
onto the next original suffix cell. No OWN00 is assumed or fabricated. -/
theorem stream_runsFrom (base digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom streamMachine (streamInitial base digits suffix)
      (streamTrace base [] digits suffix) (streamFinal base digits suffix) := by
  refine ⟨?_,streamTrace_chain base [] digits suffix,?_,stream_halt _ _⟩
  · simpa only [streamInitial,rawField,processedLeft,leftBlocks,List.flatMap_nil,List.nil_append,
      List.append_assoc,List.cons_append] using streamTrace_head base [] digits suffix
  · simpa only [streamFinal,List.append_nil] using streamTrace_last base [] digits suffix

theorem stream_final_tape (base digits suffix : List Bool) :
    (streamFinal base digits suffix).Tape =
      Turing.Tape.mk₂ (false::(leftBlocks digits.reverse++base)) suffix := rfl

theorem stream_length_le (base digits suffix : List Bool) :
    (streamTrace base [] digits suffix).length ≤ 16*(digits.length+1)^2 := by
  rw [streamTrace_length]
  nlinarith [Nat.zero_le (digits.length^2)]

theorem stream_visitedSpace_le (inputLength : Nat) (base digits suffix : List Bool) :
    visitedSpace streamMachine inputLength (streamTrace base [] digits suffix) ≤
      inputLength+32*(digits.length+1)^2 := by
  have h := PSTRTMTrace002.visitedSpace_le streamMachine inputLength (streamTrace base [] digits suffix)
  rw [streamTrace_length] at h
  nlinarith [Nat.zero_le (digits.length^2)]

theorem encodeNat_stream_runsFrom (base suffix : List Bool) (n : Nat) :
    PSTRTMSeq005.RunsFrom streamMachine
      (streamState 0 base (encodeNat n++suffix))
      (streamTrace base [] (PSTRTMNatValue017.rawPayload n) suffix)
      (streamFinal base (PSTRTMNatValue017.rawPayload n) suffix) := by
  rw [encodeNat_rawField]
  exact stream_runsFrom base (PSTRTMNatValue017.rawPayload n) suffix

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
