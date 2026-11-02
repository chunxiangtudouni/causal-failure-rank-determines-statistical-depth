module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024f

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024

def copyTrace (archive digits : List Bool) (gap : Nat) : List (MachineState 58) :=
  startupTrace archive digits gap ++ initialBackTrace archive digits gap ++
    copyLoop archive [] gap digits ++
    finishTrace (PA17TMRatArithmeticCopy006.sourceLeft archive digits) digits gap

theorem copy_length (archive digits : List Bool) (gap : Nat) :
    (copyTrace archive digits gap).length =
      4*digits.length^2+26*digits.length+2*gap*digits.length+3*gap+20 := by
  simp only [copyTrace,List.length_append,startup_length,initialBack_length,copyLoop_length,
    finish_length,List.length_nil]
  ring

theorem copy_chain (archive digits : List Bool) (gap : Nat) :
    (copyTrace archive digits gap).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  have hl := chain_append _ _ _ _ (copyLoop_chain archive [] digits gap)
    (finish_chain (PA17TMRatArithmeticCopy006.sourceLeft archive digits) digits gap)
    (copyLoop_last archive [] digits gap)
    (finish_head (PA17TMRatArithmeticCopy006.sourceLeft archive digits) digits gap) (by
      simp [Turing.TM0.step,copyMachine,state,bankTail,PA17TMRatArithmeticCopy006.sourceLeft,Turing.Tape.mk₂])
  have hlh : (copyLoop archive [] gap digits ++
      finishTrace (PA17TMRatArithmeticCopy006.sourceLeft archive digits) digits gap).head? = some
      (state 11 (false::archive) (PSTRTMIncrement009.blocks digits ++ false::false::bankTail gap [])) := by
    simp [List.head?_append,copyLoop_head,PSTRTMRawNat010.leftBlocks]
  have hb := chain_append _ _ _ _ (initialBack_chain archive digits gap) hl
    (initialBack_last archive digits gap) hlh (by
      simp [Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.copyMachine,
        oldLabel,PSTRTMSeq005.leftLabel,Turing.Tape.mk₂])
  have hbh : (initialBackTrace archive digits gap ++
      (copyLoop archive [] gap digits ++
        finishTrace (PA17TMRatArithmeticCopy006.sourceLeft archive digits) digits gap)).head? = some
      (oldCfg (PA17TMRatArithmeticCopy006.backStart 9 digits.reverse archive (false::false::bankTail gap []))) := by
    simp [List.head?_append,initialBack_head]
  have h := chain_append _ _ _ _ (startup_chain archive digits gap) hb
    (startup_last archive digits gap) hbh (by
      cases digits.reverse <;>
        simp [PA17TMRatArithmeticCopy006.backStart,PA17TMRatArithmeticCopy006.state,
          Turing.TM0.step,copyMachine,state,PA17TMRatArithmeticCopy006.copyMachine,
          oldCfg,oldLabel,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
          Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks])
  simpa only [copyTrace,List.append_assoc] using h

theorem copy_full_runsFrom (archive digits : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom copyMachine
      (state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (true::bankTail gap []))
      (copyTrace archive digits gap)
      (state 58 (destinationLeft gap (PA17TMRatArithmeticCopy006.sourceLeft archive digits))
        (PA17TMRatArithmeticCopy006.workspace digits)) := by
  refine ⟨?_,copy_chain archive digits gap,?_,halt _ _⟩
  · simp [copyTrace,List.head?_append,startup_head]
  · simp [copyTrace,List.getLast?_append,finish_last]

/-- Only the genuine far-right infinite blank tail is normalized. -/
theorem tape_append_false (left word : List Bool) :
    Turing.Tape.mk₂ left (word ++ [false]) = Turing.Tape.mk₂ left word := by
  simp only [Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_append_false]

theorem entry_tape (left : List Bool) (gap : Nat) :
    Turing.Tape.mk₂ left (true::bankTail gap []) =
      Turing.Tape.mk₂ left (true::(List.replicate gap false ++ [true,false])) := by
  let word := true::(List.replicate gap false ++ [true,false])
  have h := (tape_append_false left (word ++ [false])).trans (tape_append_false left word)
  simpa only [word,bankTail,PA17TMRatArithmeticCopy006.workspace,PSTRTMIncrement009.blocks,
    List.flatMap_nil,List.nil_append,List.append_assoc,List.cons_append] using h

/-- TRUE sourceFooter, actual zero gap, TRUE work anchor, FALSE guard, blank
tail. The machine really writes OWN00 and really ends on destination data. -/
theorem copy_runsFrom (archive digits : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom copyMachine
      (state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
        (true::(List.replicate gap false ++ [true,false])))
      (copyTrace archive digits gap)
      (state 58 (destinationLeft gap (PA17TMRatArithmeticCopy006.sourceLeft archive digits))
        (PSTRTMIncrement009.blocks digits ++ [false,false])) := by
  have h := copy_full_runsFrom archive digits gap
  change PSTRTMSeq005.RunsFrom copyMachine
    ⟨0,Turing.Tape.mk₂ (PA17TMRatArithmeticCopy006.sourceLeft archive digits) (true::bankTail gap [])⟩
    (copyTrace archive digits gap) _ at h
  rw [entry_tape] at h
  exact h

theorem copy_time_le (archive digits : List Bool) (gap : Nat) :
    (copyTrace archive digits gap).length ≤ 64*((digits.length+1)*(digits.length+gap+1)) := by
  rw [copy_length]
  nlinarith

theorem copy_visitedSpace_le (archive digits : List Bool) (gap inputLength : Nat) :
    visitedSpace copyMachine inputLength (copyTrace archive digits gap) ≤
      inputLength+128*((digits.length+1)*(digits.length+gap+1))+1 := by
  have hs := PSTRTMTrace002.visitedSpace_le copyMachine inputLength (copyTrace archive digits gap)
  have ht := copy_time_le archive digits gap
  omega

theorem originalNat_runsFrom (archive : List Bool) (n gap : Nat) :
    PSTRTMSeq005.RunsFrom copyMachine
      (state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive (PSTRTMNatValue017.rawPayload n))
        (true::(List.replicate gap false ++ [true,false])))
      (copyTrace archive (PSTRTMNatValue017.rawPayload n) gap)
      (state 58 (destinationLeft gap (PA17TMRatArithmeticCopy006.sourceLeft archive (PSTRTMNatValue017.rawPayload n)))
        (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++ [false,false])) :=
  copy_runsFrom archive (PSTRTMNatValue017.rawPayload n) gap

theorem copy_framed (archive digits : List Bool) (gap : Nat) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom copyMachine
        (state 0 (PA17TMRatArithmeticCopy006.sourceLeft archive digits)
          (true::(List.replicate gap false ++ [true,false]))) trace final ∧
      final.q = 58 ∧
      final.Tape = Turing.Tape.mk₂
        (false::true::(List.replicate gap false ++ true::PA17TMRatArithmeticCopy006.sourceLeft archive digits))
        (PSTRTMIncrement009.blocks digits ++ [false,false]) ∧
      trace.length ≤ 64*((digits.length+1)*(digits.length+gap+1)) ∧
      ∀ inputLength, visitedSpace copyMachine inputLength trace ≤
        inputLength+128*((digits.length+1)*(digits.length+gap+1))+1 :=
  ⟨copyTrace archive digits gap,
    state 58 (destinationLeft gap (PA17TMRatArithmeticCopy006.sourceLeft archive digits))
      (PSTRTMIncrement009.blocks digits ++ [false,false]),
    copy_runsFrom archive digits gap,rfl,rfl,copy_time_le archive digits gap,
    fun inputLength => copy_visitedSpace_le archive digits gap inputLength⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
