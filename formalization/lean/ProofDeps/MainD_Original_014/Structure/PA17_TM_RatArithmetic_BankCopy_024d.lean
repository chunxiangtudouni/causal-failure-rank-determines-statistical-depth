module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

theorem workspaceTrace_head (bit : Bool) (left copied : List Bool) :
    (workspaceTrace bit left copied).head? = some
      (state (oldLabel (PA17TMRatArithmeticCopy006.workData bit)) (false::left)
        (PA17TMRatArithmeticCopy006.workspace copied)) := by
  simp only [workspaceTrace,List.head?_map,PA17TMRatArithmeticCopy006.workspaceRound_head,Option.map_some,oldCfg_state]

theorem workspaceTrace_last (bit : Bool) (left copied : List Bool) :
    (workspaceTrace bit left copied).getLast? = some
      (state 36 left (false::PA17TMRatArithmeticCopy006.workspace (copied ++ [bit]))) := by
  simp only [workspaceTrace,List.getLast?_map,PA17TMRatArithmeticCopy006.workspaceRound_last,Option.map_some,
    oldCfg_state,oldLabel,PSTRTMSeq005.leftLabel]
  rfl

theorem sourceTrace_head (bit : Bool) (left later tail : List Bool) :
    (sourceTrace bit left later tail).head? = some
      (state 38 (PA17TMRatArithmeticCopy006.sourceBase bit left later) (false::false::tail)) := by
  simp only [sourceTrace,List.head?_map,PA17TMRatArithmeticCopy006.sourceReturn_head,Option.map_some,
    oldCfg_state,oldLabel,PSTRTMSeq005.leftLabel]
  rfl

theorem sourceTrace_last (bit : Bool) (left later tail : List Bool) :
    (sourceTrace bit left later tail).getLast? = some
      (state 41 (bit::left) (true::(PSTRTMIncrement009.blocks later ++ false::false::tail))) := by
  simp only [sourceTrace,List.getLast?_map,PA17TMRatArithmeticCopy006.sourceReturn_last,Option.map_some,
    oldCfg_state,oldLabel,PSTRTMSeq005.leftLabel]
  rfl

/-- The bit is actually read at11. Only its flag is cleared; data is kept. -/
def prefixTrace (bit : Bool) (left later copied : List Bool) (gap : Nat) : List (MachineState 58) :=
  [state 11 left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::bankTail gap copied),
   state (oldLabel (PA17TMRatArithmeticCopy006.saveFlag bit)) (bit::left)
     (true::(PSTRTMIncrement009.blocks later ++ false::false::bankTail gap copied)),
   state (oldLabel (PA17TMRatArithmeticCopy006.leaveFlag bit)) (bit::left)
     (false::(PSTRTMIncrement009.blocks later ++ false::false::bankTail gap copied))]

theorem prefix_head (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (prefixTrace bit left later copied gap).head? = some
      (state 11 left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::bankTail gap copied)) := rfl

theorem prefix_last (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (prefixTrace bit left later copied gap).getLast? = some
      (state (oldLabel (PA17TMRatArithmeticCopy006.leaveFlag bit)) (bit::left)
        (false::(PSTRTMIncrement009.blocks later ++ false::false::bankTail gap copied))) := rfl

theorem prefix_length (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (prefixTrace bit left later copied gap).length = 3 := rfl

theorem prefix_chain (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (prefixTrace bit left later copied gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  cases bit <;> simp [prefixTrace,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,
    PA17TMRatArithmeticCopy006.copyMachine,PA17TMRatArithmeticCopy006.saveFlag,
    PA17TMRatArithmeticCopy006.leaveFlag,PSTRTMIncrement009.blocks,oldLabel,
    PSTRTMSeq005.leftLabel,Turing.Tape.mk₂]

def iterationTrace (bit : Bool) (left later copied : List Bool) (gap : Nat) : List (MachineState 58) :=
  prefixTrace bit left later copied gap ++
  pairTrace (PA17TMRatArithmeticCopy006.outData bit) (PA17TMRatArithmeticCopy006.outFlag bit)
    (false::bit::left) (bankTail gap copied) later ++
  outwardTrace bit (PA17TMRatArithmeticCopy006.sourceBase bit left later) copied gap ++
  workspaceTrace bit
    (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied ++
  returnTrace (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap ++
  sourceTrace bit left later (bankTail gap (copied ++ [bit]))

theorem iteration_head (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (iterationTrace bit left later copied gap).head? = some
      (state 11 left (PSTRTMIncrement009.blocks (bit::later) ++ false::false::bankTail gap copied)) := by
  simp [iterationTrace,List.head?_append,prefix_head]

theorem iteration_last (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (iterationTrace bit left later copied gap).getLast? = some
      (state 41 (bit::left)
        (true::(PSTRTMIncrement009.blocks later ++ false::false::bankTail gap (copied ++ [bit])))) := by
  simp [iterationTrace,List.getLast?_append,sourceTrace_last]

theorem iteration_length (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (iterationTrace bit left later copied gap).length = 4*(later.length+copied.length)+2*gap+28 := by
  simp only [iterationTrace,List.length_append,prefix_length,pairTrace_length,
    outward_length,workspaceTrace_length,return_length,sourceTrace_length]
  omega

theorem iteration_chain (bit : Bool) (left later copied : List Bool) (gap : Nat) :
    (iterationTrace bit left later copied gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hr := chain_append _ _ _ _
    (return_chain (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap)
    (sourceTrace_chain bit left later (bankTail gap (copied ++ [bit])))
    (return_last (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap)
    (sourceTrace_head bit left later (bankTail gap (copied ++ [bit]))) (by
      simp [Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂])
  have hrh : (returnTrace (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap ++
      sourceTrace bit left later (bankTail gap (copied ++ [bit]))).head? = some
      (state 38 (List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)
        (true::false::PA17TMRatArithmeticCopy006.workspace (copied ++ [bit]))) := by
    simp [List.head?_append,return_head]
  have hw := chain_append _ _ _ _
    (workspaceTrace_chain bit
      (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied)
    hr (workspaceTrace_last bit
      (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied)
    hrh (by
      simp [Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.copyMachine,Turing.Tape.mk₂,oldLabel,PSTRTMSeq005.leftLabel])
  have hwh : (workspaceTrace bit
      (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied ++
      (returnTrace (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap ++
        sourceTrace bit left later (bankTail gap (copied ++ [bit])))).head? = some
      (state (oldLabel (PA17TMRatArithmeticCopy006.workData bit))
        (false::true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later))
        (PA17TMRatArithmeticCopy006.workspace copied)) := by
    simp [List.head?_append,workspaceTrace_head]
  have ho := chain_append _ _ _ _
    (outward_chain bit (PA17TMRatArithmeticCopy006.sourceBase bit left later) copied gap) hw
    (outward_last bit (PA17TMRatArithmeticCopy006.sourceBase bit left later) copied gap) hwh (by
      cases bit <;> simp [Turing.TM0.step,copyMachine,state,outwardGuardQ,
        PA17TMRatArithmeticCopy006.workData,oldLabel,PSTRTMSeq005.leftLabel,Turing.Tape.mk₂])
  have hoh : (outwardTrace bit (PA17TMRatArithmeticCopy006.sourceBase bit left later) copied gap ++
      (workspaceTrace bit
        (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied ++
        (returnTrace (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap ++
          sourceTrace bit left later (bankTail gap (copied ++ [bit]))))).head? = some
      (state (outwardQ bit) (false::PA17TMRatArithmeticCopy006.sourceBase bit left later) (true::bankTail gap copied)) := by
    simp [List.head?_append,outward_head]
  have hp := pairTrace_chain (PA17TMRatArithmeticCopy006.outData bit) (PA17TMRatArithmeticCopy006.outFlag bit)
    (false::bit::left) (bankTail gap copied) later
    (by cases bit <;> intro symbol <;> rfl) (by cases bit <;> rfl)
  have hpo := chain_append _ _ _ _ hp ho
    (pairTrace_last (PA17TMRatArithmeticCopy006.outData bit) (PA17TMRatArithmeticCopy006.outFlag bit)
      (false::bit::left) (bankTail gap copied) later) hoh (by
      cases bit <;> simp [Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.outFlag,
        PA17TMRatArithmeticCopy006.sourceBase,outwardQ,oldLabel,PSTRTMSeq005.leftLabel,Turing.Tape.mk₂])
  have hpoh : (pairTrace (PA17TMRatArithmeticCopy006.outData bit) (PA17TMRatArithmeticCopy006.outFlag bit)
      (false::bit::left) (bankTail gap copied) later ++
      (outwardTrace bit (PA17TMRatArithmeticCopy006.sourceBase bit left later) copied gap ++
        (workspaceTrace bit
          (true::(List.replicate gap false ++ true::false::PA17TMRatArithmeticCopy006.sourceBase bit left later)) copied ++
          (returnTrace (PA17TMRatArithmeticCopy006.sourceBase bit left later) (copied ++ [bit]) gap ++
            sourceTrace bit left later (bankTail gap (copied ++ [bit])))))).head? = some
      (state (oldLabel (PA17TMRatArithmeticCopy006.outData bit)) (false::bit::left)
        (PSTRTMIncrement009.blocks later ++ false::false::bankTail gap copied)) := by
    simp [List.head?_append,pairTrace_head]
  have h := chain_append _ _ _ _ (prefix_chain bit left later copied gap) hpo
    (prefix_last bit left later copied gap) hpoh (by
      cases bit <;> simp [Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.copyMachine,
        PA17TMRatArithmeticCopy006.leaveFlag,PA17TMRatArithmeticCopy006.outData,oldLabel,
        PSTRTMSeq005.leftLabel,Turing.Tape.mk₂])
  simpa only [iterationTrace,List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
