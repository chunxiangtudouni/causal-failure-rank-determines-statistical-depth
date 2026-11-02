module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

def anchorLeft (gap : Nat) (source : List Bool) : List Bool :=
  true::(List.replicate gap false ++ true::source)

/-- Both destination OWN cells are really written, even on a blank tail. -/
def startupMiddle (source : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 44 (anchorLeft gap source) (false::PA17TMRatArithmeticCopy006.workspace []),
   state 1 (destinationLeft gap source) (PA17TMRatArithmeticCopy006.workspace []),
   state 2 (destinationLeft gap source) (PA17TMRatArithmeticCopy006.workspace []),
   state 3 (false::destinationLeft gap source) [false],
   state 4 (false::destinationLeft gap source) [false],
   state 5 (destinationLeft gap source) (PA17TMRatArithmeticCopy006.workspace []),
   state 45 (anchorLeft gap source) (false::PA17TMRatArithmeticCopy006.workspace []),
   state 46 (List.replicate gap false ++ true::source) (true::false::PA17TMRatArithmeticCopy006.workspace [])]

theorem startupMiddle_head (source : List Bool) (gap : Nat) :
    (startupMiddle source gap).head? = some
      (state 44 (anchorLeft gap source) (false::PA17TMRatArithmeticCopy006.workspace [])) := rfl

theorem startupMiddle_last (source : List Bool) (gap : Nat) :
    (startupMiddle source gap).getLast? = some
      (state 46 (List.replicate gap false ++ true::source) (true::false::PA17TMRatArithmeticCopy006.workspace [])) := rfl

theorem startupMiddle_length (source : List Bool) (gap : Nat) : (startupMiddle source gap).length = 8 := rfl

theorem startupMiddle_chain (source : List Bool) (gap : Nat) :
    (startupMiddle source gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  simp [startupMiddle,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,anchorLeft,destinationLeft,
    PA17TMRatArithmeticCopy006.copyMachine,PA17TMRatArithmeticCopy006.workspace,PSTRTMIncrement009.blocks,
    oldLabel,PSTRTMSeq005.leftLabel,Turing.Tape.mk₂]

def startupTail (base : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 7 (false::base) (false::bankTail gap []),state 8 base (false::false::bankTail gap [])]

theorem startupTail_chain (base : List Bool) (gap : Nat) :
    (startupTail base gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  simp [startupTail,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,
    PA17TMRatArithmeticCopy006.copyMachine,oldLabel,PSTRTMSeq005.leftLabel,Turing.Tape.mk₂]

def startupTrace (archive digits : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (true::bankTail gap [])] ++
  zeroRight 43 (true::PA17TMRatArithmeticCopy006.sourceLeft archive digits)
    (false::PA17TMRatArithmeticCopy006.workspace []) gap ++
  startupMiddle (PA17TMRatArithmeticCopy006.sourceLeft archive digits) gap ++
  zeroLeft 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
    (true::false::PA17TMRatArithmeticCopy006.workspace []) gap ++
  startupTail (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) gap

theorem startup_head (archive digits : List Bool) (gap : Nat) :
    (startupTrace archive digits gap).head? = some
      (state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (true::bankTail gap [])) := rfl

theorem startup_last (archive digits : List Bool) (gap : Nat) :
    (startupTrace archive digits gap).getLast? = some
      (state 8 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) (false::false::bankTail gap [])) := by
  unfold startupTrace
  rw [List.getLast?_append]
  rfl

theorem startup_length (archive digits : List Bool) (gap : Nat) :
    (startupTrace archive digits gap).length = 2*gap+13 := by
  simp only [startupTrace,List.length_append,zeroRight_length,
    startupMiddle_length,zeroLeft_length,startupTail,List.length_cons,List.length_nil]
  omega

theorem startup_chain (archive digits : List Bool) (gap : Nat) :
    (startupTrace archive digits gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hz := zeroLeft_chain 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
    (true::false::PA17TMRatArithmeticCopy006.workspace []) gap (by rfl)
  have ht := chain_append _ _ _ _ hz
    (startupTail_chain (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) gap)
    (zeroLeft_last 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
      (true::false::PA17TMRatArithmeticCopy006.workspace []) gap) (by rfl) (by
      simp [Turing.TM0.step,copyMachine,state,bankTail,PA17TMRatArithmeticCopy006.sourceLeft,Turing.Tape.mk₂])
  have hth : (zeroLeft 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
      (true::false::PA17TMRatArithmeticCopy006.workspace []) gap ++
      startupTail (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) gap).head? =
      some (zeroBackStart 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
        (true::false::PA17TMRatArithmeticCopy006.workspace []) gap) := by
    simp [List.head?_append,zeroLeft_head]
  have hm := chain_append _ _ _ _
    (startupMiddle_chain (PA17TMRatArithmeticCopy006.sourceLeft archive digits) gap) ht
    (startupMiddle_last (PA17TMRatArithmeticCopy006.sourceLeft archive digits) gap) hth (by
      cases gap <;> simp [zeroBackStart,List.replicate_succ,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂])
  have hmh : (startupMiddle (PA17TMRatArithmeticCopy006.sourceLeft archive digits) gap ++
      (zeroLeft 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
        (true::false::PA17TMRatArithmeticCopy006.workspace []) gap ++
        startupTail (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) gap)).head? = some
      (state 44 (anchorLeft gap (PA17TMRatArithmeticCopy006.sourceLeft archive digits))
        (false::PA17TMRatArithmeticCopy006.workspace [])) := by
    simp [List.head?_append,startupMiddle_head]
  have hr := zeroRight_chain 43 (true::PA17TMRatArithmeticCopy006.sourceLeft archive digits)
    (false::PA17TMRatArithmeticCopy006.workspace []) gap (by rfl)
  have hrm := chain_append _ _ _ _ hr hm
    (zeroRight_last 43 (true::PA17TMRatArithmeticCopy006.sourceLeft archive digits)
      (false::PA17TMRatArithmeticCopy006.workspace []) gap) hmh (by
      simp [Turing.TM0.step,copyMachine,state,anchorLeft,Turing.Tape.mk₂])
  have hrmh : (zeroRight 43 (true::PA17TMRatArithmeticCopy006.sourceLeft archive digits)
      (false::PA17TMRatArithmeticCopy006.workspace []) gap ++
      (startupMiddle (PA17TMRatArithmeticCopy006.sourceLeft archive digits) gap ++
        (zeroLeft 47 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
          (true::false::PA17TMRatArithmeticCopy006.workspace []) gap ++
          startupTail (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) gap))).head? = some
      (state 43 (true::PA17TMRatArithmeticCopy006.sourceLeft archive digits)
        (List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.workspace [])) := by
    simp [List.head?_append,zeroRight_head]
  have h := chain_append
    [state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (true::bankTail gap [])] _ _ _
    (.singleton _) hrm (by rfl) hrmh (by
      simp [Turing.TM0.step,copyMachine,state,bankTail,Turing.Tape.mk₂])
  simpa only [startupTrace,List.append_assoc] using h

def finishTail (source digits : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 57 (anchorLeft gap source) (false::PA17TMRatArithmeticCopy006.workspace digits),
   state 58 (destinationLeft gap source) (PA17TMRatArithmeticCopy006.workspace digits)]

theorem finishTail_chain (source digits : List Bool) (gap : Nat) :
    (finishTail source digits gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  simp [finishTail,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,anchorLeft,destinationLeft,Turing.Tape.mk₂]

def finishTrace (source digits : List Bool) (gap : Nat) : List (MachineState 58) :=
  zeroRight 56 (true::source) (false::PA17TMRatArithmeticCopy006.workspace digits) gap ++
    finishTail source digits gap

theorem finish_head (source digits : List Bool) (gap : Nat) :
    (finishTrace source digits gap).head? = some
      (state 56 (true::source) (List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.workspace digits)) := by
  simp [finishTrace,List.head?_append,zeroRight_head]

theorem finish_last (source digits : List Bool) (gap : Nat) :
    (finishTrace source digits gap).getLast? = some
      (state 58 (destinationLeft gap source) (PA17TMRatArithmeticCopy006.workspace digits)) := by
  unfold finishTrace
  rw [List.getLast?_append]
  rfl

theorem finish_length (source digits : List Bool) (gap : Nat) :
    (finishTrace source digits gap).length = gap+3 := by
  simp [finishTrace,zeroRight_length,finishTail,Nat.add_assoc]

theorem finish_chain (source digits : List Bool) (gap : Nat) :
    (finishTrace source digits gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  exact chain_append _ _ _ _
    (zeroRight_chain 56 (true::source) (false::PA17TMRatArithmeticCopy006.workspace digits) gap (by rfl))
    (finishTail_chain source digits gap)
    (zeroRight_last 56 (true::source) (false::PA17TMRatArithmeticCopy006.workspace digits) gap)
    (by rfl) (by simp [Turing.TM0.step,copyMachine,state,anchorLeft,Turing.Tape.mk₂])

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
