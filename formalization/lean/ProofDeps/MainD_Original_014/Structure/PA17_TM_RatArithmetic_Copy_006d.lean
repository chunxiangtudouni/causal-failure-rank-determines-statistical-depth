module
public import Structure.PA17_TM_RatArithmetic_Copy_006c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

def sourceBase (bit : Bool) (left later : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks later.reverse ++ false::bit::left

/-- Return to the one temporarily cleared source flag and actually restore
it. The remainder of the source and the produced workspace remain intact. -/
def sourceReturn (bit : Bool) (left later tail : List Bool) : List (MachineState 42) :=
  [state 38 (sourceBase bit left later) (false::false::tail)] ++
  backScan 39 40 (bit::left) (false::false::tail) later.reverse ++
  [state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))]

theorem sourceReturn_head (bit : Bool) (left later tail : List Bool) :
    (sourceReturn bit left later tail).head? = some
      (state 38 (sourceBase bit left later) (false::false::tail)) := rfl

theorem sourceReturn_last (bit : Bool) (left later tail : List Bool) :
    (sourceReturn bit left later tail).getLast? = some
      (state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))) := by
  unfold sourceReturn
  rw [List.getLast?_append]
  rfl

theorem sourceReturn_length (bit : Bool) (left later tail : List Bool) :
    (sourceReturn bit left later tail).length = 2*later.length+3 := by
  simp only [sourceReturn,List.length_append,List.length_singleton,backScan_length,List.length_reverse]
  omega

theorem sourceReturn_chain (bit : Bool) (left later tail : List Bool) :
    (sourceReturn bit left later tail).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hb := backScan_chain 39 40 (bit::left) (false::false::tail) later.reverse
    (by rfl) (by intro symbol; rfl)
  have hr := chain_append
    (backScan 39 40 (bit::left) (false::false::tail) later.reverse)
    [state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))]
    _ _ hb (.singleton _)
    (backScan_last 39 40 (bit::left) (false::false::tail) later.reverse) (by rfl) (by
      simp [Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂])
  have hrh : (backScan 39 40 (bit::left) (false::false::tail) later.reverse ++
      [state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))]).head? =
      some (backStart 39 later.reverse (bit::left) (false::false::tail)) := by
    simp [List.head?_append,backScan_head]
  have h := chain_append
    [state 38 (sourceBase bit left later) (false::false::tail)]
    (backScan 39 40 (bit::left) (false::false::tail) later.reverse ++
      [state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))])
    _ _ (.singleton _) hr (by rfl) hrh (by
    unfold sourceBase
    cases later.reverse <;>
      simp [backStart,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks])
  simpa only [sourceReturn,List.append_assoc] using h

def copyPrefix (bit : Bool) (left later copied : List Bool) : List (MachineState 42) :=
  [state 11 left (bit::true::(PSTRTMIncrement009.blocks later ++ false::false::workspace copied)),
   state (saveFlag bit) (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::workspace copied)),
   state (leaveFlag bit) (bit::left) (false::(PSTRTMIncrement009.blocks later ++ false::false::workspace copied))]

theorem copyPrefix_head (bit : Bool) (left later copied : List Bool) :
    (copyPrefix bit left later copied).head? = some
      (state 11 left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::workspace copied)) := by
  simp [copyPrefix,PSTRTMIncrement009.blocks]

theorem copyPrefix_last (bit : Bool) (left later copied : List Bool) :
    (copyPrefix bit left later copied).getLast? = some
      (state (leaveFlag bit) (bit::left) (false::(PSTRTMIncrement009.blocks later ++ false::false::workspace copied))) := rfl

theorem copyPrefix_length (bit : Bool) (left later copied : List Bool) :
    (copyPrefix bit left later copied).length = 3 := rfl

theorem copyPrefix_chain (bit : Bool) (left later copied : List Bool) :
    (copyPrefix bit left later copied).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  cases bit <;>
    simp [copyPrefix,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,saveFlag,leaveFlag,Turing.Tape.mk₂]

def copyIteration (bit : Bool) (left later copied : List Bool) : List (MachineState 42) :=
  copyPrefix bit left later copied ++
  pairScan (outData bit) (outFlag bit) (false::bit::left) (workspace copied) later ++
  workspaceRound bit (false::sourceBase bit left later) copied ++
  sourceReturn bit left later (workspace (copied ++ [bit]))

theorem copyIteration_head (bit : Bool) (left later copied : List Bool) :
    (copyIteration bit left later copied).head? = some
      (state 11 left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::workspace copied)) := by
  simp [copyIteration,List.head?_append,copyPrefix_head]

theorem copyIteration_last (bit : Bool) (left later copied : List Bool) :
    (copyIteration bit left later copied).getLast? = some
      (state 41 (bit::left)
        (true::(PSTRTMIncrement009.blocks later ++ false::false::workspace (copied ++ [bit])))) := by
  simp [copyIteration,List.getLast?_append,sourceReturn_last]

theorem copyIteration_length (bit : Bool) (left later copied : List Bool) :
    (copyIteration bit left later copied).length = 4*(later.length+copied.length)+22 := by
  simp only [copyIteration,List.length_append,copyPrefix_length,pairScan_length,
    workspaceRound_length,sourceReturn_length]
  omega

theorem copyIteration_chain (bit : Bool) (left later copied : List Bool) :
    (copyIteration bit left later copied).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hr := sourceReturn_chain bit left later (workspace (copied ++ [bit]))
  have hw := chain_append _ _ _ _ (workspaceRound_chain bit (false::sourceBase bit left later) copied) hr
    (workspaceRound_last bit (false::sourceBase bit left later) copied)
    (sourceReturn_head bit left later (workspace (copied ++ [bit]))) (by
      simp [Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂])
  have hwh : (workspaceRound bit (false::sourceBase bit left later) copied ++
      sourceReturn bit left later (workspace (copied ++ [bit]))).head? = some
      (state (workData bit) (false::false::sourceBase bit left later) (workspace copied)) := by
    simp [List.head?_append,workspaceRound_head]
  have ho := pairScan_chain (outData bit) (outFlag bit) (false::bit::left) (workspace copied) later
    (by cases bit <;> intro symbol <;> rfl) (by cases bit <;> rfl)
  have how := chain_append _ _ _ _ ho hw (pairScan_last _ _ _ _ _) hwh (by
    cases bit <;> simp [sourceBase,Turing.TM0.step,copyMachine,state,outFlag,workData,Turing.Tape.mk₂])
  have howh : (pairScan (outData bit) (outFlag bit) (false::bit::left) (workspace copied) later ++
      (workspaceRound bit (false::sourceBase bit left later) copied ++
        sourceReturn bit left later (workspace (copied ++ [bit])))).head? = some
      (state (outData bit) (false::bit::left) (PSTRTMIncrement009.blocks later ++ false::false::workspace copied)) := by
    simp [List.head?_append,pairScan_head]
  have h := chain_append _ _ _ _ (copyPrefix_chain bit left later copied)
    (by simpa only [List.append_assoc] using how) (copyPrefix_last bit left later copied) howh (by
      cases bit <;> simp [Turing.TM0.step,copyMachine,state,leaveFlag,outData,Turing.Tape.mk₂])
  simpa only [copyIteration,List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006
