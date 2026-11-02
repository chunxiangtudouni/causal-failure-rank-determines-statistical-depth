module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

def copyLoop (archive copied : List Bool) (gap : Nat) : List Bool → List (MachineState 58)
  | [] =>
    [state 11 (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive) (false::false::bankTail gap copied),
     state 12 (false::(PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)) (false::bankTail gap copied),
     state 42 (false::(PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)) (true::bankTail gap copied)]
  | bit::later =>
    iterationTrace bit (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive) later copied gap ++
      copyLoop archive (copied ++ [bit]) gap later

theorem copyLoop_head (archive copied later : List Bool) (gap : Nat) :
    (copyLoop archive copied gap later).head? = some
      (state 11 (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::archive)
        (PSTRTMIncrement009.blocks later ++ false::false::bankTail gap copied)) := by
  cases later with
  | nil => rfl
  | cons bit later => simp [copyLoop,List.head?_append,iteration_head]

theorem copyLoop_last (archive copied later : List Bool) (gap : Nat) :
    (copyLoop archive copied gap later).getLast? = some
      (state 42 (false::(PSTRTMRawNat010.leftBlocks (copied ++ later).reverse ++ false::archive))
        (true::bankTail gap (copied ++ later))) := by
  induction later generalizing copied with
  | nil => simp [copyLoop]
  | cons bit later ih =>
    simp [copyLoop,List.getLast?_append,ih,List.append_assoc]

theorem copyLoop_length (archive copied later : List Bool) (gap : Nat) :
    (copyLoop archive copied gap later).length =
      4*later.length^2+4*copied.length*later.length+(24+2*gap)*later.length+3 := by
  induction later generalizing copied with
  | nil => simp [copyLoop]
  | cons bit later ih =>
    simp only [copyLoop,List.length_append,iteration_length,ih,List.length_cons,List.length_nil]
    ring

theorem copyLoop_chain (archive copied later : List Bool) (gap : Nat) :
    (copyLoop archive copied gap later).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  induction later generalizing copied with
  | nil =>
    simp [copyLoop,List.isChain_cons_cons,Turing.TM0.step,copyMachine,state,
      PA17TMRatArithmeticCopy006.copyMachine,Turing.Tape.mk₂,oldLabel,PSTRTMSeq005.leftLabel]
  | cons bit later ih =>
    rw [copyLoop]
    apply chain_append _ _ _ _ (iteration_chain bit _ later copied gap) (ih (copied ++ [bit]))
      (iteration_last bit _ later copied gap) (copyLoop_head archive (copied ++ [bit]) later gap)
    simp [Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.copyMachine,
      Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks,List.reverse_append,oldLabel,PSTRTMSeq005.leftLabel]

def initialBackTrace (archive digits : List Bool) (gap : Nat) : List (MachineState 58) :=
  (PA17TMRatArithmeticCopy006.backScan 9 10 archive (false::false::bankTail gap []) digits.reverse).map oldCfg

theorem initialBack_head (archive digits : List Bool) (gap : Nat) :
    (initialBackTrace archive digits gap).head? = some
      (oldCfg (PA17TMRatArithmeticCopy006.backStart 9 digits.reverse archive (false::false::bankTail gap []))) := by
  simp only [initialBackTrace,List.head?_map,PA17TMRatArithmeticCopy006.backScan_head,Option.map_some]

theorem initialBack_last (archive digits : List Bool) (gap : Nat) :
    (initialBackTrace archive digits gap).getLast? = some
      (state 9 archive (false::(PSTRTMIncrement009.blocks digits ++ false::false::bankTail gap []))) := by
  simp only [initialBackTrace,List.getLast?_map,PA17TMRatArithmeticCopy006.backScan_last,
    List.reverse_reverse,Option.map_some,oldCfg_state,oldLabel,PSTRTMSeq005.leftLabel]
  rfl

theorem initialBack_length (archive digits : List Bool) (gap : Nat) :
    (initialBackTrace archive digits gap).length = 2*digits.length+1 := by
  simp only [initialBackTrace,List.length_map,PA17TMRatArithmeticCopy006.backScan_length,List.length_reverse]

theorem initialBack_chain (archive digits : List Bool) (gap : Nat) :
    (initialBackTrace archive digits gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  apply old_chain _ (PA17TMRatArithmeticCopy006.backScan_chain 9 10 archive
    (false::false::bankTail gap []) digits.reverse (by rfl) (by intro symbol; rfl))
  intro s hs
  apply lookup_core
  have hc := backScan_labels 9 10 archive (false::false::bankTail gap []) digits.reverse s hs
  rcases hc with h | h <;> rw [h] <;> decide

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
