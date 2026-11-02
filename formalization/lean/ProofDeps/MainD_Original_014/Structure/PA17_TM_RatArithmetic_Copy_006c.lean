module
public import Structure.PA17_TM_RatArithmetic_Copy_006b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006

def workspace (digits : List Bool) : List Bool := PSTRTMIncrement009.blocks digits ++ [false,false]

theorem workspace_push (copied : List Bool) (bit : Bool) :
    workspace (copied ++ [bit]) = PSTRTMIncrement009.blocks copied ++ [bit,true,false,false] := by
  simp [workspace,PSTRTMIncrement009.blocks,List.flatMap_append,List.append_assoc]

/-- Append a physically read source bit in the blank workspace, write both
new OWN zeros, and return to the still-clamped footer. Source is opaque. -/
def workspaceRound (bit : Bool) (left copied : List Bool) : List (MachineState 42) :=
  pairScan (workData bit) (workFlag bit) (false::left) [] copied ++
  writeTrace bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left) ++
  backScan 36 37 left [bit,true,false,false] copied.reverse

theorem workspaceRound_head (bit : Bool) (left copied : List Bool) :
    (workspaceRound bit left copied).head? = some
      (state (workData bit) (false::left) (workspace copied)) := by
  simp [workspaceRound,List.head?_append,pairScan_head,workspace]

theorem workspaceRound_last (bit : Bool) (left copied : List Bool) :
    (workspaceRound bit left copied).getLast? = some
      (state 36 left (false::workspace (copied ++ [bit]))) := by
  simp [workspaceRound,List.getLast?_append,backScan_last,workspace_push]

theorem workspaceRound_length (bit : Bool) (left copied : List Bool) :
    (workspaceRound bit left copied).length = 4*copied.length+14 := by
  simp only [workspaceRound,List.length_append,pairScan_length,writeTrace_length,backScan_length,List.length_reverse]
  omega

theorem workspaceRound_chain (bit : Bool) (left copied : List Bool) :
    (workspaceRound bit left copied).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hb := backScan_chain 36 37 left [bit,true,false,false] copied.reverse
    (by rfl) (by intro symbol; rfl)
  have hw := chain_append _ _ _ _
    (writeTrace_chain bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left)) hb
    (writeTrace_last bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left))
    (backScan_head 36 37 left [bit,true,false,false] copied.reverse) (by
      cases copied.reverse <;>
        simp [backStart,Turing.TM0.step,copyMachine,state,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks])
  have hwh : (writeTrace bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left) ++
      backScan 36 37 left [bit,true,false,false] copied.reverse).head? = some
      (state (writeData bit) (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left) [false,false]) := by
    simp [List.head?_append,writeTrace_head]
  have hp := pairScan_chain (workData bit) (workFlag bit) (false::left) [] copied
    (by cases bit <;> intro symbol <;> rfl) (by cases bit <;> rfl)
  have h := chain_append _ _ _ _ hp hw
    (pairScan_last (workData bit) (workFlag bit) (false::left) [] copied) hwh (by
    cases bit <;> simp [Turing.TM0.step,copyMachine,state,workFlag,writeData,Turing.Tape.mk₂])
  simpa only [workspaceRound,List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopy006
