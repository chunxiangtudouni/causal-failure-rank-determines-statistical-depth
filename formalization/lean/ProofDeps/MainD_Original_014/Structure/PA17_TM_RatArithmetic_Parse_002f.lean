module
public import Structure.PA17_TM_RatArithmetic_Parse_002e

/-! Framed original two-Rat list input, including its list header and final
marker. These are actual runs of the same fixed parser, with arbitrary
external data on both sides; no boundary is changed to an assumed OWN00. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def framedOriginalTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 97) :=
  (prefixTrace base (encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix)).map
      (PSTRTMSeq005.leftCfg (b:=91)) ++
    (pairTrace (listPrefixLeft base) x y (true::suffix)).map (PSTRTMSeq005.rightCfg (a:=5))

def framedOriginalFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 97 :=
  PSTRTMSeq005.rightCfg (a:=5) (pairFinal (listPrefixLeft base) x y (true::suffix))

theorem framedOriginal_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom originalParserMachine
      ⟨0,Turing.Tape.mk₂ base (encode [.rational x,.rational y]++suffix)⟩
      (framedOriginalTrace base x y suffix) (framedOriginalFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom prefixMachine pairMachine
    (prefixState 0 base (encodeNat 2++(encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix)))
    (prefixState 5 (listPrefixLeft base) (encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix))
    (pairFinal (listPrefixLeft base) x y (true::suffix))
    (prefixTrace base (encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix))
    (pairTrace (listPrefixLeft base) x y (true::suffix))
    (prefix_runsFrom base (encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix))
    (pair_runsFrom (listPrefixLeft base) x y (true::suffix))
  simpa only [originalParserMachine,framedOriginalTrace,framedOriginalFinal,prefixState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero,encode,List.length_cons,List.length_nil,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using h

/-- Equality of the ENTIRE tape, including arbitrary external archive and
suffix. The actual final head is at the original final TRUE marker. -/
theorem framedOriginal_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (framedOriginalFinal base x y suffix).Tape =
      Turing.Tape.mk₂ (ratLeft (ratLeft (listPrefixLeft base) x) y) (true::suffix) := rfl

theorem framedOriginalTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (framedOriginalTrace base x y suffix).length = (originalParserTrace x y).length := by
  change (((prefixTrace base (encodeDatum (.rational x)++encodeDatum (.rational y)++true::suffix)).map
        (PSTRTMSeq005.leftCfg (a:=5) (b:=91))) ++
    (pairTrace (listPrefixLeft base) x y (true::suffix)).map (PSTRTMSeq005.rightCfg (a:=5) (b:=91))).length = _
  rw [List.length_append,List.length_map,List.length_map,pairTrace_length,originalParserTrace_length]
  change 6+_ = _
  simp only [fieldWidth]
  omega

theorem framedOriginal_time (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (framedOriginalTrace base x y suffix).length ≤ 32*(fieldWidth x y+1)^2 := by
  rw [framedOriginalTrace_length]
  exact originalParser_time x y

theorem framedOriginal_space (inputLength : Nat) (base : List Bool) (x y : Rat) (suffix : List Bool) :
    visitedSpace originalParserMachine inputLength (framedOriginalTrace base x y suffix) ≤
      inputLength+64*(fieldWidth x y+1)^2+1 := by
  have h := PSTRTMTrace002.visitedSpace_le originalParserMachine inputLength (framedOriginalTrace base x y suffix)
  have ht := framedOriginal_time base x y suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
