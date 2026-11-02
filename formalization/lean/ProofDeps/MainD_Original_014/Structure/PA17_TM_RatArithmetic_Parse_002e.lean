module
public import Structure.PA17_TM_RatArithmetic_Parse_002d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def ratLeft (base : List Bool) (x : Rat) : List Bool :=
  bothLeft (false::sign x::base) (numeratorDigits x) (denominatorDigits x)

def pairMachine : Machine 91 := PSTRTMSeq005.seqMachine ratMachine ratMachine

def pairTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 91) :=
  (ratTrace base (sign x) (numeratorDigits x) (denominatorDigits x) (encodeDatum (.rational y)++suffix)).map
      (PSTRTMSeq005.leftCfg (b:=45)) ++
    (ratTrace (ratLeft base x) (sign y) (numeratorDigits y) (denominatorDigits y) suffix).map
      (PSTRTMSeq005.rightCfg (a:=45))

def pairFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 91 :=
  PSTRTMSeq005.rightCfg (a:=45)
    (ratFinal (ratLeft base x) (sign y) (numeratorDigits y) (denominatorDigits y) suffix)

theorem pair_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom pairMachine
      ⟨0,Turing.Tape.mk₂ base (encodeDatum (.rational x)++encodeDatum (.rational y)++suffix)⟩
      (pairTrace base x y suffix) (pairFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom ratMachine ratMachine
    (⟨0,Turing.Tape.mk₂ base (encodeDatum (.rational x)++(encodeDatum (.rational y)++suffix))⟩)
    (ratFinal base (sign x) (numeratorDigits x) (denominatorDigits x) (encodeDatum (.rational y)++suffix))
    (ratFinal (ratLeft base x) (sign y) (numeratorDigits y) (denominatorDigits y) suffix)
    (ratTrace base (sign x) (numeratorDigits x) (denominatorDigits x) (encodeDatum (.rational y)++suffix))
    (ratTrace (ratLeft base x) (sign y) (numeratorDigits y) (denominatorDigits y) suffix)
    (encodeDatum_rat_runsFrom base (encodeDatum (.rational y)++suffix) x)
    (encodeDatum_rat_runsFrom (ratLeft base x) suffix y)
  simpa only [pairMachine,pairTrace,pairFinal,List.append_assoc,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem pair_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (pairFinal base x y suffix).Tape = Turing.Tape.mk₂ (ratLeft (ratLeft base x) y) suffix := rfl

theorem pairTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (pairTrace base x y suffix).length =
      (numeratorDigits x).length^2+(denominatorDigits x).length^2+
      (numeratorDigits y).length^2+(denominatorDigits y).length^2+
      9*((numeratorDigits x).length+(denominatorDigits x).length+
        (numeratorDigits y).length+(denominatorDigits y).length)+22 := by
  change (((ratTrace base (sign x) (numeratorDigits x) (denominatorDigits x)
        (encodeDatum (.rational y)++suffix)).map (PSTRTMSeq005.leftCfg (a:=45) (b:=45))) ++
    (ratTrace (ratLeft base x) (sign y) (numeratorDigits y) (denominatorDigits y) suffix).map
      (PSTRTMSeq005.rightCfg (a:=45) (b:=45))).length = _
  rw [List.length_append,List.length_map,List.length_map,ratTrace_length,ratTrace_length]
  ring

def prefixMachine : Machine 5 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | 2 => some (3,.move .right)
  | 3 => some (4,.move .right)
  | 4 => some (5,.move .right)
  | _ => none

def prefixState (q : Fin 6) (left right : List Bool) : MachineState 5 := ⟨q,Turing.Tape.mk₂ left right⟩

def prefixTrace (base suffix : List Bool) : List (MachineState 5) :=
  [prefixState 0 base (true::true::false::false::true::suffix),
   prefixState 1 (true::base) (true::false::false::true::suffix),
   prefixState 2 (true::true::base) (false::false::true::suffix),
   prefixState 3 (false::true::true::base) (false::true::suffix),
   prefixState 4 (false::false::true::true::base) (true::suffix),
   prefixState 5 (true::false::false::true::true::base) suffix]

def listPrefixLeft (base : List Bool) : List Bool := true::false::false::true::true::base

theorem prefix_runsFrom (base suffix : List Bool) :
    PSTRTMSeq005.RunsFrom prefixMachine
      (prefixState 0 base (encodeNat 2++suffix)) (prefixTrace base suffix)
      (prefixState 5 (listPrefixLeft base) suffix) := by
  rw [encodeNat_two]
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [prefixTrace,List.isChain_cons_cons,Turing.TM0.step,prefixMachine,prefixState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,prefixMachine,prefixState]

def originalParserMachine : Machine 97 := PSTRTMSeq005.seqMachine prefixMachine pairMachine

def originalParserTrace (x y : Rat) : List (MachineState 97) :=
  (prefixTrace [] (encodeDatum (.rational x)++encodeDatum (.rational y)++[true])).map
      (PSTRTMSeq005.leftCfg (b:=91)) ++
    (pairTrace (listPrefixLeft []) x y [true]).map (PSTRTMSeq005.rightCfg (a:=5))

def originalParserFinal (x y : Rat) : MachineState 97 :=
  PSTRTMSeq005.rightCfg (a:=5) (pairFinal (listPrefixLeft []) x y [true])

theorem originalParser_runs (x y : Rat) :
    Runs originalParserMachine (encode [.rational x,.rational y])
      (originalParserTrace x y) (originalParserFinal x y) := by
  have hp := prefix_runsFrom [] (encodeDatum (.rational x)++encodeDatum (.rational y)++[true])
  have hprefix : Runs prefixMachine (encode [.rational x,.rational y])
      (prefixTrace [] (encodeDatum (.rational x)++encodeDatum (.rational y)++[true]))
      (prefixState 5 (listPrefixLeft []) (encodeDatum (.rational x)++encodeDatum (.rational y)++[true])) := by
    apply PSTRTMTrace002.runs_of_chain
    · simpa only [Turing.TM0.init,Turing.Tape.mk₁,prefixState,encode,List.length_cons,List.length_nil,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,Fin.default_eq_zero] using hp.1
    · exact hp.2.1
    · exact hp.2.2.1
    · exact hp.2.2.2
  exact PSTRTMSeq005.seq_runs prefixMachine pairMachine (encode [.rational x,.rational y])
    (prefixState 5 (listPrefixLeft []) (encodeDatum (.rational x)++encodeDatum (.rational y)++[true]))
    (pairFinal (listPrefixLeft []) x y [true])
    (prefixTrace [] (encodeDatum (.rational x)++encodeDatum (.rational y)++[true]))
    (pairTrace (listPrefixLeft []) x y [true]) hprefix (pair_runsFrom (listPrefixLeft []) x y [true])

theorem originalParser_final_tape (x y : Rat) :
    (originalParserFinal x y).Tape =
      Turing.Tape.mk₂ (ratLeft (ratLeft (listPrefixLeft []) x) y) [true] := rfl

def fieldWidth (x y : Rat) : Nat :=
  (numeratorDigits x).length+(denominatorDigits x).length+
    (numeratorDigits y).length+(denominatorDigits y).length

theorem originalParserTrace_length (x y : Rat) :
    (originalParserTrace x y).length =
      (numeratorDigits x).length^2+(denominatorDigits x).length^2+
      (numeratorDigits y).length^2+(denominatorDigits y).length^2+9*fieldWidth x y+28 := by
  change (((prefixTrace [] (encodeDatum (.rational x)++encodeDatum (.rational y)++[true])).map
        (PSTRTMSeq005.leftCfg (a:=5) (b:=91))) ++
    (pairTrace (listPrefixLeft []) x y [true]).map (PSTRTMSeq005.rightCfg (a:=5) (b:=91))).length = _
  rw [List.length_append,List.length_map,List.length_map,pairTrace_length]
  change 6+_ = _
  simp only [fieldWidth]
  omega

theorem originalParser_time (x y : Rat) :
    (originalParserTrace x y).length ≤ 32*(fieldWidth x y+1)^2 := by
  rw [originalParserTrace_length]
  dsimp [fieldWidth]
  nlinarith [Nat.zero_le ((numeratorDigits x).length*(denominatorDigits x).length),
    Nat.zero_le ((numeratorDigits x).length*(numeratorDigits y).length),
    Nat.zero_le ((numeratorDigits x).length*(denominatorDigits y).length),
    Nat.zero_le ((denominatorDigits x).length*(numeratorDigits y).length),
    Nat.zero_le ((denominatorDigits x).length*(denominatorDigits y).length),
    Nat.zero_le ((numeratorDigits y).length*(denominatorDigits y).length)]

theorem originalParser_space (x y : Rat) :
    visitedSpace originalParserMachine (encode [.rational x,.rational y]).length (originalParserTrace x y) ≤
      80*(fieldWidth x y+1)^2 := by
  have h := PSTRTMTrace002.visitedSpace_le originalParserMachine
    (encode [.rational x,.rational y]).length (originalParserTrace x y)
  have ht := originalParser_time x y
  have hw : (encode [.rational x,.rational y]).length = 2*fieldWidth x y+14 := pair_length x y
  rw [hw] at h ⊢
  nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

theorem originalParser_field_values (x y : Rat) :
    PSTRTMIncrement009.valueDigits (numeratorDigits x) = x.num.natAbs ∧
    PSTRTMIncrement009.valueDigits (denominatorDigits x) = x.den ∧
    PSTRTMIncrement009.valueDigits (numeratorDigits y) = y.num.natAbs ∧
    PSTRTMIncrement009.valueDigits (denominatorDigits y) = y.den ∧
    0<x.den ∧ 0<y.den :=
  ⟨numeratorDigits_value x,denominatorDigits_value x,numeratorDigits_value y,denominatorDigits_value y,
    denominator_positive x,denominator_positive y⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
