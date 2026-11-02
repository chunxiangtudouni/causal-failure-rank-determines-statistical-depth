module
public import Common.PSTR_TM_ThresholdBReblockCost_196
public import Common.PSTR_TM_Prepend_022
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBDatum224
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBReblock195

/-! Original FIRST threshold Datum. Actual B backup/reblock195 -> actual
inverse004c -> SAME022 one-bit natural tag. The final head really moves
one cell left; that existing false guard becomes the output tag. -/

private theorem blank_two (bits : List Bool) :
    Turing.ListBlank.mk (bits++[false,false]) = Turing.ListBlank.mk bits := by
  calc
    _ = Turing.ListBlank.mk ((bits++[false])++[false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits++[false]) := PSTRTMRawNat010.blank_append_false _
    _ = _ := PSTRTMRawNat010.blank_append_false _

def rawMachine : Machine 1311 := PSTRTMSeq005.seqMachine savedMachine PSTRTMUnblock018.unblockMachine

def rawTrace (risk : Rat) (depth : Nat) : List (MachineState 1311) :=
  (savedTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PA17TMRatArithmeticUnblock004.framedTrace (savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)) []).map
        (PSTRTMSeq005.rightCfg (a := 1291))

def rawFinal (risk : Rat) (depth : Nat) : MachineState 1311 :=
  PSTRTMSeq005.rightCfg (a := 1291) (PSTRTMUnblock018.state 19 (false::savedLeft risk depth)
    (encodeNat (PaperProofs.Statistics.controllerB risk depth)++[false]))

theorem raw_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs rawMachine (encode [.rational risk,.natural depth]) (rawTrace risk depth) (rawFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs savedMachine PSTRTMUnblock018.unblockMachine
    (encode [.rational risk,.natural depth]) (savedFinal risk depth)
    (PSTRTMUnblock018.state 19 (false::savedLeft risk depth)
      (encodeNat (PaperProofs.Statistics.controllerB risk depth)++[false]))
    (savedTrace risk depth)
    (PA17TMRatArithmeticUnblock004.framedTrace (savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)) [])
    (saved_runs risk depth hr hd)
  have ht : (savedFinal risk depth).Tape = Turing.Tape.mk₂ (false::savedLeft risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload
        (PaperProofs.Statistics.controllerB risk depth))++[false,false]) := by
    rw [saved_final_tape]
    simp only [Turing.Tape.mk₂,blank_two]
  rw [ht]
  exact PA17TMRatArithmeticUnblock004.originalNat_runsFrom _ _ []

theorem raw_final_tape (risk : Rat) (depth : Nat) :
    (rawFinal risk depth).Tape = Turing.Tape.mk₂ (false::savedLeft risk depth)
      (encodeNat (PaperProofs.Statistics.controllerB risk depth)) := by
  simp only [rawFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_append_false]

def tagTrace (archive input : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ (false::archive) input⟩,
   ⟨1,Turing.Tape.mk₂ archive (false::input)⟩,
   ⟨2,Turing.Tape.mk₂ archive (false::input)⟩]

theorem tag_runsFrom (archive input : List Bool) :
    PSTRTMSeq005.RunsFrom (PSTRTMPrepend022.bitMachine false)
      ⟨0,Turing.Tape.mk₂ (false::archive) input⟩ (tagTrace archive input)
      ⟨2,Turing.Tape.mk₂ archive (false::input)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [tagTrace,List.isChain_cons_cons,Turing.TM0.step,PSTRTMPrepend022.bitMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,PSTRTMPrepend022.bitMachine]

def datumMachine : Machine 1314 := PSTRTMSeq005.seqMachine rawMachine (PSTRTMPrepend022.bitMachine false)

def datumTrace (risk : Rat) (depth : Nat) : List (MachineState 1314) :=
  (rawTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 2)) ++
    (tagTrace (savedLeft risk depth) (encodeNat (PaperProofs.Statistics.controllerB risk depth))).map
      (PSTRTMSeq005.rightCfg (a := 1311))

def datumFinal (risk : Rat) (depth : Nat) : MachineState 1314 :=
  PSTRTMSeq005.rightCfg (a := 1311) (b := 2)
    ⟨2,Turing.Tape.mk₂ (savedLeft risk depth) (encodeDatum (.natural (PaperProofs.Statistics.controllerB risk depth)))⟩

theorem datum_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs datumMachine (encode [.rational risk,.natural depth]) (datumTrace risk depth) (datumFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs rawMachine (PSTRTMPrepend022.bitMachine false)
    (encode [.rational risk,.natural depth]) (rawFinal risk depth)
    ⟨2,Turing.Tape.mk₂ (savedLeft risk depth) (false::encodeNat (PaperProofs.Statistics.controllerB risk depth))⟩
    (rawTrace risk depth) (tagTrace (savedLeft risk depth) (encodeNat (PaperProofs.Statistics.controllerB risk depth)))
    (raw_runs risk depth hr hd)
  rw [raw_final_tape]
  exact tag_runsFrom _ _

theorem datum_final_tape (risk : Rat) (depth : Nat) :
    (datumFinal risk depth).Tape = Turing.Tape.mk₂ (savedLeft risk depth)
      (encodeDatum (.natural (PaperProofs.Statistics.controllerB risk depth))) := rfl

private theorem arithmetic_time (input depth width main inverse : Nat)
    (hm : main ≤ 16777216*(input+depth+1)^3)
    (hi : inverse ≤ 32*(width+1)^2) (hw : width ≤ input+4) :
    main+inverse+3 ≤ 33554432*(input+depth+1)^3 := by
  let scale := input+depth+1
  have hs : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width+1 ≤ 5*scale := by dsimp only [scale]; omega
  have hpow := Nat.pow_le_pow_left hwidth 2
  have hinv : inverse ≤ 800*scale^2 := by nlinarith
  have hc : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have hinv' := hinv.trans (Nat.mul_le_mul_left 800 hc)
  have hp : scale ≤ scale^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  change main+inverse+3 ≤ 33554432*scale^3
  have hm' : main ≤ 16777216*scale^3 := hm
  omega

theorem datum_time_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (datumTrace risk depth).length ≤ 33554432*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have hm := PSTRTMThresholdBReblockCost196.saved_length_le risk depth hr hd
  have hi := PA17TMRatArithmeticUnblock004.framed_time_le (savedLeft risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)) []
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn] at hi
  have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  simp only [datumTrace,rawTrace,List.length_append,List.length_map,tagTrace,List.length_cons,List.length_nil]
  exact arithmetic_time _ _ _ _ _ hm hi hw

private theorem scale_cube (input depth : Nat) : input+1 ≤ (input+depth+1)^3 := by
  have hs : 1 ≤ input+depth+1 := by omega
  have hp : input+depth+1 ≤ (input+depth+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  omega

theorem datum_prefix_space_le (risk : Rat) (depth clock : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace datumMachine (encode [.rational risk,.natural depth]).length ((datumTrace risk depth).take clock) ≤
      134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := datum_time_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le datumMachine (encode [.rational risk,.natural depth]).length
    ((datumTrace risk depth).take clock)
  have hl : ((datumTrace risk depth).take clock).length ≤ (datumTrace risk depth).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

theorem original_BDatum_computes (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    computes datumMachine (encode [.rational risk,.natural depth])
      (encodeDatum (.natural (PaperProofs.Statistics.controllerB risk depth)))
      (134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3)
      (134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3) := by
  refine ⟨datumTrace risk depth,datumFinal risk depth,datum_runs risk depth hr hd,?_,?_,?_⟩
  · rw [datum_final_tape]
    simp only [Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · have ht := datum_time_le risk depth hr hd
    omega
  · simpa only [List.take_length] using datum_prefix_space_le risk depth (datumTrace risk depth).length hr hd

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBDatum224
