module
public import Structure.PA17_TM_RatArithmetic_PairEncode_017a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017

def backEncodeMachine : Machine 25 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticParse002.fieldBackMachine
    PA17TMRatArithmeticUnblock004.markerMachine

def backEncodeTrace (archive : List Bool) (a : Nat) (tail : List Bool) : List (MachineState 25) :=
  (PA17TMRatArithmeticParse002.fieldBackTrace archive (payload a) (false::tail)).map
    (PSTRTMSeq005.leftCfg (b := 19)) ++
  (PA17TMRatArithmeticUnblock004.markerTrace archive (payload a) tail).map
    (PSTRTMSeq005.rightCfg (a := 5))

def backEncodeFinal (archive : List Bool) (a : Nat) (tail : List Bool) : MachineState 25 :=
  PSTRTMSeq005.rightCfg (a := 5)
    (PSTRTMUnblock018.state 19 (false::archive) (encodeNat a ++ true::tail))

theorem backEncode_runsFrom (archive : List Bool) (a : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom backEncodeMachine
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (false::tail)⟩
      (backEncodeTrace archive a tail) (backEncodeFinal archive a tail) := by
  have ha : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticUnblock004.markerMachine
      ⟨0,(PA17TMRatArithmeticParse002.fieldBackFinal archive (payload a) (false::tail)).Tape⟩
      (PA17TMRatArithmeticUnblock004.markerTrace archive (payload a) tail)
      (PSTRTMUnblock018.state 19 (false::archive) (encodeNat a ++ true::tail)) := by
    rw [PA17TMRatArithmeticParse002.fieldBack_final_tape]
    exact PA17TMRatArithmeticUnblock004.marker_originalNat_runsFrom a archive tail
  have h := PSTRTMSeq005.seq_runsFrom PA17TMRatArithmeticParse002.fieldBackMachine
    PA17TMRatArithmeticUnblock004.markerMachine
    ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (false::tail)⟩
    (PA17TMRatArithmeticParse002.fieldBackFinal archive (payload a) (false::tail))
    (PSTRTMUnblock018.state 19 (false::archive) (encodeNat a ++ true::tail))
    (PA17TMRatArithmeticParse002.fieldBackTrace archive (payload a) (false::tail))
    (PA17TMRatArithmeticUnblock004.markerTrace archive (payload a) tail)
    (PA17TMRatArithmeticParse002.fieldBack_runsFrom archive (payload a) (false::tail)) ha
  simpa [backEncodeMachine,backEncodeTrace,backEncodeFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel] using h

theorem backEncode_length (archive : List Bool) (a : Nat) (tail : List Bool) :
    (backEncodeTrace archive a tail).length = (payload a).length^2+13*(payload a).length+11 := by
  simp only [backEncodeTrace,List.length_append,List.length_map,
    PA17TMRatArithmeticParse002.fieldBackTrace_length,PA17TMRatArithmeticUnblock004.marker_length]
  ring

def clampBackMachine : Machine 27 := PSTRTMSeq005.seqMachine clampHeaderMachine backEncodeMachine

def clampBackTrace (archive : List Bool) (a : Nat) (tail : List Bool) : List (MachineState 27) :=
  (clampHeaderTrace (false::aArchive archive a) tail).map (PSTRTMSeq005.leftCfg (b := 25)) ++
    (backEncodeTrace archive a tail).map (PSTRTMSeq005.rightCfg (a := 1))

def clampBackFinal (archive : List Bool) (a : Nat) (tail : List Bool) : MachineState 27 :=
  PSTRTMSeq005.rightCfg (a := 1) (backEncodeFinal archive a tail)

theorem clampBack_runsFrom (archive : List Bool) (a : Nat) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom clampBackMachine
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (true::tail)⟩
      (clampBackTrace archive a tail) (clampBackFinal archive a tail) := by
  have h := PSTRTMSeq005.seq_runsFrom clampHeaderMachine backEncodeMachine
    ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (true::tail)⟩
    ⟨1,Turing.Tape.mk₂ (false::aArchive archive a) (false::tail)⟩
    (backEncodeFinal archive a tail) (clampHeaderTrace (false::aArchive archive a) tail)
    (backEncodeTrace archive a tail) (clampHeader_runsFrom (false::aArchive archive a) tail)
    (backEncode_runsFrom archive a tail)
  simpa [clampBackMachine,clampBackTrace,clampBackFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel] using h

theorem clampBack_length (archive : List Bool) (a : Nat) (tail : List Bool) :
    (clampBackTrace archive a tail).length = (payload a).length^2+13*(payload a).length+13 := by
  simp only [clampBackTrace,List.length_append,List.length_map,clampHeader_length,backEncode_length]
  omega

def bTail (footer : Bool) (b : Nat) (suffix : List Bool) : List Bool := natTail b ++ footer::suffix

/-- Two fixed formats. The footer choice is made in code before a/b inputs. -/
def pairMachine (footer : Bool) : Machine 47 :=
  PSTRTMSeq005.seqMachine (inverseMachine footer) clampBackMachine

def pairTrace (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 47) :=
  (inverseTrace footer (aArchive archive a) (payload b) suffix).map (PSTRTMSeq005.leftCfg (b := 27)) ++
    (clampBackTrace archive a (bTail footer b suffix)).map (PSTRTMSeq005.rightCfg (a := 19))

def pairFinal (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 47 :=
  PSTRTMSeq005.rightCfg (a := 19) (clampBackFinal archive a (bTail footer b suffix))

theorem pair_runsFrom (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (pairMachine footer)
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ false::false::suffix)⟩
      (pairTrace footer archive a b suffix) (pairFinal footer archive a b suffix) := by
  have hc : PSTRTMSeq005.RunsFrom clampBackMachine
      ⟨0,(PSTRTMUnblock018.state 19 (false::aArchive archive a) (encodeNat b ++ footer::suffix)).Tape⟩
      (clampBackTrace archive a (bTail footer b suffix)) (clampBackFinal archive a (bTail footer b suffix)) := by
    change PSTRTMSeq005.RunsFrom clampBackMachine
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (encodeNat b ++ footer::suffix)⟩ _ _
    rw [encodeNat_head b]
    exact clampBack_runsFrom archive a (bTail footer b suffix)
  have h := PSTRTMSeq005.seq_runsFrom (inverseMachine footer) clampBackMachine
    ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ false::false::suffix)⟩
    (PSTRTMUnblock018.state 19 (false::aArchive archive a) (encodeNat b ++ footer::suffix))
    (clampBackFinal archive a (bTail footer b suffix))
    (inverseTrace footer (aArchive archive a) (payload b) suffix)
    (clampBackTrace archive a (bTail footer b suffix))
    (inverseNat_runsFrom footer (aArchive archive a) suffix b) hc
  simpa [pairMachine,pairTrace,pairFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel] using h

theorem pairFinal_label (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (pairFinal footer archive a b suffix).q = 47 := by
  apply Fin.ext
  simp [pairFinal,clampBackFinal,backEncodeFinal,PSTRTMSeq005.rightCfg,PSTRTMSeq005.rightLabel,PSTRTMUnblock018.state]

theorem pairFinal_tape (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (pairFinal footer archive a b suffix).Tape =
      Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ footer::suffix) := by
  change Turing.Tape.mk₂ (false::archive) (encodeNat a ++ true::bTail footer b suffix) = _
  rw [encodeNat_head b]
  simp only [bTail,List.append_assoc,List.cons_append]

theorem pair_length (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (pairTrace footer archive a b suffix).length =
      (payload a).length^2+(payload b).length^2+13*(payload a).length+11*(payload b).length+18+
        (if footer then 1 else 0) := by
  simp only [pairTrace,List.length_append,List.length_map,inverse_length,clampBack_length]
  ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017
