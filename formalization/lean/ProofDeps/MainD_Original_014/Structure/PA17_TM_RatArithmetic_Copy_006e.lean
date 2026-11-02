module
public import Structure.PA17_TM_RatArithmetic_Copy_006d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

def copyLoop (archive copied : List Bool) : List Bool → List (MachineState 42)
  | [] =>
    [state 11 (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive) (false::false::workspace copied),
     state 12 (false::(PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)) (false::workspace copied),
     state 42 (false::(PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)) (true::workspace copied)]
  | bit::later =>
    copyIteration bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive) later copied ++
    copyLoop archive (copied ++ [bit]) later

theorem copyLoop_head (archive copied later : List Bool) :
    (copyLoop archive copied later).head? = some
      (state 11 (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)
        (PSTRTMIncrement009.blocks later ++ false::false::workspace copied)) := by
  cases later with
  | nil => rfl
  | cons bit later => simp [copyLoop,List.head?_append,copyIteration_head]

theorem copyLoop_last (archive copied later : List Bool) :
    (copyLoop archive copied later).getLast? = some
      (state 42 (false::(PSTRTMRawNat010.leftBlocks (copied ++ later).reverse ++ false::archive))
        (true::workspace (copied ++ later))) := by
  induction later generalizing copied with
  | nil => simp [copyLoop]
  | cons bit later ih =>
    simp [copyLoop,List.getLast?_append,ih,List.append_assoc]

theorem copyLoop_length (archive copied later : List Bool) :
    (copyLoop archive copied later).length =
      4*later.length^2+4*copied.length*later.length+18*later.length+3 := by
  induction later generalizing copied with
  | nil => simp [copyLoop]
  | cons bit later ih =>
    simp only [copyLoop,List.length_append,copyIteration_length,ih,List.length_cons,List.length_nil]
    ring

theorem copyLoop_chain (archive copied later : List Bool) :
    (copyLoop archive copied later).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction later generalizing copied with
  | nil =>
    simp [copyLoop,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [copyLoop]
    apply chain_append _ _ _ _ (copyIteration_chain bit _ later copied) (ih (copied ++ [bit]))
      (copyIteration_last bit _ later copied) (copyLoop_head archive (copied ++ [bit]) later)
    simp [Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks,
      List.reverse_append]

def sourceLeft (archive digits : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive)

/-- Initialize two real OWN zeros and clamp the original footer, all with
charged writes and moves. No arbitrary suffix is assumed to be blank. -/
def startupTrace (archive digits : List Bool) : List (MachineState 42) :=
  [state 0 (sourceLeft archive digits) [true],
   state 1 (true::sourceLeft archive digits) [false,false],
   state 2 (true::sourceLeft archive digits) [false,false],
   state 3 (false::true::sourceLeft archive digits) [false],
   state 4 (false::true::sourceLeft archive digits) [false],
   state 5 (true::sourceLeft archive digits) [false,false],
   state 6 (sourceLeft archive digits) [true,false,false],
   state 7 (sourceLeft archive digits) [false,false,false],
   state 8 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) [false,false,false,false]]

theorem startup_head (archive digits : List Bool) :
    (startupTrace archive digits).head? = some (state 0 (sourceLeft archive digits) [true]) := rfl

theorem startup_last (archive digits : List Bool) :
    (startupTrace archive digits).getLast? = some
      (state 8 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) [false,false,false,false]) := rfl

theorem startup_length (archive digits : List Bool) : (startupTrace archive digits).length = 9 := rfl

private theorem startup_blank_two_false :
    Turing.ListBlank.mk ([false,false] : List Bool) = Turing.ListBlank.mk ([] : List Bool) :=
  (PSTRTMRawNat010.blank_append_false [false]).trans PSTRTMRawNat010.blank_single_false

private theorem startup_blank_bit_false (bit : Bool) :
    Turing.ListBlank.mk [bit,false] = Turing.ListBlank.mk [bit] :=
  PSTRTMRawNat010.blank_append_false [bit]

private theorem startup_blank_bit_two_false (bit : Bool) :
    Turing.ListBlank.mk [bit,false,false] = Turing.ListBlank.mk [bit] :=
  (PSTRTMRawNat010.blank_append_false [bit,false]).trans (startup_blank_bit_false bit)

private theorem startup_blank_pair_two_false (first second : Bool) :
    Turing.ListBlank.mk [first,second,false,false] = Turing.ListBlank.mk [first,second] :=
  (PSTRTMRawNat010.blank_append_false [first,second,false]).trans
    (PSTRTMRawNat010.blank_append_false [first,second])

private theorem startup_blank_bit_four_false (bit : Bool) :
    Turing.ListBlank.mk [bit,false,false,false,false] = Turing.ListBlank.mk [bit] :=
  (PSTRTMRawNat010.blank_append_false [bit,false,false,false]).trans
    ((PSTRTMRawNat010.blank_append_false [bit,false,false]).trans
      ((PSTRTMRawNat010.blank_append_false [bit,false]).trans
        (PSTRTMRawNat010.blank_append_false [bit])))

attribute [local simp] startup_blank_two_false startup_blank_bit_false startup_blank_bit_two_false
  startup_blank_pair_two_false startup_blank_bit_four_false PSTRTMRawNat010.blank_single_false

theorem startup_chain (archive digits : List Bool) :
    (startupTrace archive digits).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  simp [startupTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,sourceLeft,Turing.Tape.mk₂]

def copyTrace (archive digits : List Bool) : List (MachineState 42) :=
  startupTrace archive digits ++
  backScan 9 10 archive [false,false,false,false] digits.reverse ++ copyLoop archive [] digits

theorem copy_length (archive digits : List Bool) :
    (copyTrace archive digits).length = 4*digits.length^2+20*digits.length+13 := by
  simp only [copyTrace,List.length_append,startup_length,backScan_length,copyLoop_length,
    List.length_reverse,List.length_nil]
  ring

theorem copy_chain (archive digits : List Bool) :
    (copyTrace archive digits).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hb := backScan_chain 9 10 archive [false,false,false,false] digits.reverse
    (by rfl) (by intro symbol; rfl)
  have hl := chain_append _ _ _ _ hb (copyLoop_chain archive [] digits)
    (backScan_last 9 10 archive [false,false,false,false] digits.reverse)
    (copyLoop_head archive [] digits) (by
      simp [workspace,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks,
        PSTRTMIncrement009.blocks])
  have hlh : (backScan 9 10 archive [false,false,false,false] digits.reverse ++
      copyLoop archive [] digits).head? = some (backStart 9 digits.reverse archive [false,false,false,false]) := by
    simp [List.head?_append,backScan_head]
  have h := chain_append _ _ _ _ (startup_chain archive digits) hl (startup_last archive digits) hlh (by
    cases digits.reverse <;>
      simp [backStart,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks])
  simpa only [copyTrace,List.append_assoc] using h

theorem copy_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom copyMachine (state 0 (sourceLeft archive digits) [true])
      (copyTrace archive digits) (state 42 (sourceLeft archive digits) (true::workspace digits)) := by
  refine ⟨?_,copy_chain archive digits,?_,copy_halt _ _⟩
  · simp [copyTrace,List.head?_append,startup_head]
  · simp [copyTrace,List.getLast?_append,copyLoop_last,sourceLeft]

theorem copy_time_le (archive digits : List Bool) :
    (copyTrace archive digits).length ≤ 64*(digits.length+1)^2 := by
  rw [copy_length]
  nlinarith

theorem copy_visitedSpace_le (archive digits : List Bool) (inputLength : Nat) :
    visitedSpace copyMachine inputLength (copyTrace archive digits) ≤ inputLength+128*(digits.length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le copyMachine inputLength (copyTrace archive digits)
  rw [copy_length] at hs
  nlinarith

/-- Nearest-field physical copy with complete source archive/footer
restoration and two genuinely produced OWN false cells in blank workspace. -/
theorem copy_framed (archive digits : List Bool) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom copyMachine ⟨0,Turing.Tape.mk₂ (sourceLeft archive digits) [true]⟩ trace final ∧
      final.q = 42 ∧ final.Tape = Turing.Tape.mk₂ (sourceLeft archive digits) (true::workspace digits) ∧
      trace.length ≤ 64*(digits.length+1)^2 ∧
      ∀ inputLength, visitedSpace copyMachine inputLength trace ≤ inputLength+128*(digits.length+1)^2 :=
  ⟨copyTrace archive digits,state 42 (sourceLeft archive digits) (true::workspace digits),
    copy_runsFrom archive digits,rfl,rfl,copy_time_le archive digits,copy_visitedSpace_le archive digits⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006
