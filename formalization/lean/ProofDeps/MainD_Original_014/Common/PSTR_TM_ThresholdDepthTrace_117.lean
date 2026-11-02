module
public import Common.PSTR_TM_ThresholdDepthCode_116
public import Common.PSTR_TM_TwoRawOperands_029

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthTrace117
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthCode116

theorem unit_safe (context : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    ∀ old∈PSTRTMContextRaw028.unitTrace context bit previous later suffix,EntrySafe old := by
  let left := PSTRTMContextRaw028.contextLeft context previous
  have hr (old : MachineState 16)
      (h : old∈PSTRTMRawNat010.scanRight later.length (false::left) (bit::(later++suffix))) : EntrySafe old := by
    left
    have hc := PSTRTMFullRawPadding015.scanRight_control _ _ _ old h
    omega
  have hl (old : MachineState 16)
      (h : old∈PSTRTMRawNat010.scanLeft bit later.length left (true::false::(later++suffix))) : EntrySafe old := by
    left
    have hc := PSTRTMFullRawPadding015.scanLeft_control _ _ _ _ old h
    cases bit <;> simp [PSTRTMRawNat010.leftMode] at hc <;> omega
  simp only [PSTRTMContextRaw028.unitTrace,List.forall_mem_append,List.forall_mem_cons]
  simp only [EntrySafe] at hr hl
  cases bit <;> simp_all [EntrySafe,PSTRTMRawNat010.state,PSTRTMRawNat010.payloadMode,
    PSTRTMRawNat010.markerMode,PSTRTMRawNat010.leftStartMode,Turing.Tape.mk₂,List.replicate_succ,left]

def unitTrace (context : List Bool) (bit : Bool) (previous later tail : List Bool) : List (MachineState 19) :=
  (PSTRTMContextRaw028.unitTrace context bit previous later (true::tail)).map liftRaw
theorem unit_head (context : List Bool) (bit : Bool) (previous later tail : List Bool) :
    (unitTrace context bit previous later tail).head?=some (liftRaw
      (PSTRTMRawNat010.state 0 (PSTRTMContextRaw028.contextLeft context previous)
        (List.replicate (later.length+1) true++false::bit::(later++true::tail)))) := by
  simp only [unitTrace,List.head?_map,PSTRTMContextRaw028.unit_head,Option.map_some]
theorem unit_last (context : List Bool) (bit : Bool) (previous later tail : List Bool) :
    (unitTrace context bit previous later tail).getLast?=some (liftRaw
      (PSTRTMRawNat010.state 15 (bit::PSTRTMContextRaw028.contextLeft context previous)
        (List.replicate (later.length+1) true++false::(later++true::tail)))) := by
  simp only [unitTrace,List.getLast?_map,PSTRTMContextRaw028.unit_last,Option.map_some]
theorem unit_length (context : List Bool) (bit : Bool) (previous later tail : List Bool) :
    (unitTrace context bit previous later tail).length=2*later.length+10 := by
  simp only [unitTrace,List.length_map,PSTRTMContextRaw028.unit_length]
theorem unit_chain (context : List Bool) (bit : Bool) (previous later tail : List Bool) :
    (unitTrace context bit previous later tail).IsChain (fun x y => Turing.TM0.step depthMachine x=some y) :=
  retained_chain _ (PSTRTMContextRaw028.unit_chain context bit previous later (true::tail))
    (unit_safe context bit previous later (true::tail))

theorem rewind_safe (context previous right : List Bool) :
    ∀ old∈PSTRTMContextRaw028.contextRewind context previous right,EntrySafe old := by
  induction previous generalizing right with
  | nil => simp [PSTRTMContextRaw028.contextRewind,EntrySafe,PSTRTMRawNat010.state]
  | cons bit previous ih =>
    simp only [PSTRTMContextRaw028.contextRewind,List.forall_mem_cons]
    exact ⟨Or.inl (by simp [PSTRTMRawNat010.state]),Or.inl (by simp [PSTRTMRawNat010.state]),ih _⟩

def extraTrace (context previous tail : List Bool) : List (MachineState 19) :=
  let left := PSTRTMContextRaw028.contextLeft context previous
  [state 0 left (false::true::tail),state 17 (false::left) (true::tail),
    state 18 (false::left) (false::tail),state 19 left (false::false::tail)]
theorem extra_head (context previous tail : List Bool) : (extraTrace context previous tail).head?=some
    (state 0 (PSTRTMContextRaw028.contextLeft context previous) (false::true::tail)) := rfl
theorem extra_last (context previous tail : List Bool) : (extraTrace context previous tail).getLast?=some
    (state 19 (PSTRTMContextRaw028.contextLeft context previous) (false::false::tail)) := rfl
theorem extra_chain (context previous tail : List Bool) :
    (extraTrace context previous tail).IsChain (fun x y => Turing.TM0.step depthMachine x=some y) := by
  simp [extraTrace,List.isChain_cons_cons,Turing.TM0.step,depthMachine,state,Turing.Tape.mk₂]
theorem extra_advance (context previous tail : List Bool) :
    Turing.TM0.step depthMachine (state 19 (PSTRTMContextRaw028.contextLeft context previous) (false::false::tail))=
      some (liftRaw (PSTRTMContextRaw028.contextRewindInitial context previous (false::false::tail))) := by
  cases previous <;> simp [PSTRTMContextRaw028.contextRewindInitial,PSTRTMContextRaw028.contextLeft,
    PSTRTMRawNat010.leftBlocks,Turing.TM0.step,depthMachine,state,liftRaw,embedRaw,PSTRTMRawNat010.state,Turing.Tape.mk₂]

private theorem append_link (xs ys : List (MachineState 19)) (last first : MachineState 19)
    (hx : xs.IsChain (fun a b => Turing.TM0.step depthMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step depthMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step depthMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step depthMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def doneTrace (context previous tail : List Bool) : List (MachineState 19) := extraTrace context previous tail ++
  (PSTRTMContextRaw028.contextRewind context previous (false::false::tail)).map liftRaw
theorem done_head (context previous tail : List Bool) : (doneTrace context previous tail).head?=some
    (state 0 (PSTRTMContextRaw028.contextLeft context previous) (false::true::tail)) := by
  simp only [doneTrace,List.head?_append,extra_head,Option.some_or]
theorem done_last (context previous tail : List Bool) : (doneTrace context previous tail).getLast?=some
    (state 16 (false::context) (PSTRTMIncrement009.blocks previous.reverse++false::false::tail)) := by
  simp only [doneTrace,List.getLast?_append,List.getLast?_map,PSTRTMContextRaw028.contextRewind_last,Option.map_some,Option.some_or]
  rfl
theorem done_length (context previous tail : List Bool) : (doneTrace context previous tail).length=2*previous.length+6 := by
  simp only [doneTrace,List.length_append,List.length_map,extraTrace,List.length_cons,List.length_nil,
    PSTRTMContextRaw028.contextRewind_length]
  omega
theorem done_chain (context previous tail : List Bool) :
    (doneTrace context previous tail).IsChain (fun x y => Turing.TM0.step depthMachine x=some y) := by
  apply append_link _ _ _ _ (extra_chain context previous tail)
    (retained_chain _ (PSTRTMContextRaw028.contextRewind_chain context previous (false::false::tail)) (rewind_safe _ _ _))
    (extra_last context previous tail) ?_ (extra_advance context previous tail)
  simp only [List.head?_map,PSTRTMContextRaw028.contextRewind_head,Option.map_some]

def depthTrace (context previous : List Bool) : List Bool → List Bool → List (MachineState 19)
  | [],tail => doneTrace context previous tail
  | bit::later,tail => unitTrace context bit previous later tail++depthTrace context (bit::previous) later tail

theorem depth_head (context previous digits tail : List Bool) : (depthTrace context previous digits tail).head?=some
    (state 0 (PSTRTMContextRaw028.contextLeft context previous)
      (List.replicate digits.length true++false::(digits++true::tail))) := by
  cases digits with
  | nil => exact done_head context previous tail
  | cons bit later => simp only [depthTrace,List.head?_append,unit_head,Option.some_or]; rfl
theorem depth_last (context previous digits tail : List Bool) : (depthTrace context previous digits tail).getLast?=some
    (state 16 (false::context) (PSTRTMIncrement009.blocks (previous.reverse++digits)++false::false::tail)) := by
  induction digits generalizing previous with
  | nil => simpa only [depthTrace,List.append_nil] using done_last context previous tail
  | cons bit later ih =>
    simp only [depthTrace,List.getLast?_append,ih,Option.some_or,List.reverse_cons,List.append_assoc,List.singleton_append]
theorem depth_length (context previous digits tail : List Bool) : (depthTrace context previous digits tail).length=
    digits.length^2+11*digits.length+2*previous.length+6 := by
  induction digits generalizing previous with
  | nil =>
    have h := done_length context previous tail
    simp only [depthTrace,List.length_nil]
    nlinarith
  | cons bit later ih =>
    simp only [depthTrace,List.length_append,unit_length,ih,List.length_cons]
    ring
theorem depth_chain (context previous digits tail : List Bool) :
    (depthTrace context previous digits tail).IsChain (fun x y => Turing.TM0.step depthMachine x=some y) := by
  induction digits generalizing previous with
  | nil => exact done_chain context previous tail
  | cons bit later ih =>
    apply append_link _ _ _ _ (unit_chain context bit previous later tail) (ih (bit::previous))
      (unit_last context bit previous later tail) (depth_head context (bit::previous) later tail)
    have hs : EntrySafe (PSTRTMRawNat010.state 15 (bit::PSTRTMContextRaw028.contextLeft context previous)
      (List.replicate (later.length+1) true++false::(later++true::tail))) := Or.inl (by simp [PSTRTMRawNat010.state])
    rw [raw_step _ hs]
    simp [Turing.TM0.step,PSTRTMRawNat010.rawNatMachine,PSTRTMRawNat010.state,liftRaw,embedRaw,state,
      Turing.Tape.mk₂,PSTRTMContextRaw028.contextLeft,PSTRTMRawNat010.leftBlocks,List.replicate_succ]

/-- Original depth raw header/payload is consumed on the SAME retained
risk archive. The original list-end true is ACTUALLY erased, yielding00
followed by the unchanged tail, not the unsafe one-false-plus-true format. -/
theorem depth_runsFrom (context digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom depthMachine
      (state 0 (false::context) (PSTRTMTwoRawOperands029.rawInput digits++true::tail))
      (depthTrace context [] digits tail)
      (state 16 (false::context) (PSTRTMIncrement009.blocks digits++false::false::tail)) := by
  refine ⟨?_,depth_chain context [] digits tail,?_,depth_halt _ _⟩
  · simpa only [PSTRTMContextRaw028.contextLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.nil_append,
      PSTRTMTwoRawOperands029.rawInput,List.append_assoc,List.singleton_append,List.cons_append] using depth_head context [] digits tail
  · simpa only [List.reverse_nil,List.nil_append] using depth_last context [] digits tail

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthTrace117
