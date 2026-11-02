module
public import Structure.RootB23_Threshold_Uncapped_MarkedShift_006
public import Structure.RootB23_Threshold_Uncapped_Walk_005
public import Structure.RootB23_Threshold_Uncapped_Steps_007
public import Structure.PA17_TM_RatArithmetic_PairEncode_017c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Serialize
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMRawNat010
open PA17TMRatArithmeticPairEncode017

def marker (suffix : List Bool) : List Bool := false::false::true::false::suffix
def remainder (suffix : List Bool) : List Bool := false::false::false::false::suffix
def pairSuffix (suffix : List Bool) : List Bool := false::false::false::suffix
def shiftSuffix (suffix : List Bool) : List Bool := false::false::false::false::false::suffix

def inputRight (a b : Nat) (suffix : List Bool) : List Bool :=
  blocks (payload a)++marker (blocks (payload b)++false::false::suffix)
def numeratorLeft (archive : List Bool) (a : Nat) : List Bool :=
  leftBlocks (payload a).reverse++false::false::archive
def denominatorLeft (archive : List Bool) (a : Nat) : List Bool :=
  false::true::false::false::numeratorLeft archive a

def locateCode : Machine 7 := PSTRTMSeq005.seqMachine Walk.code Steps.fourRightCode
def locateTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 7) :=
  (Walk.actualTrace (false::false::archive) (payload a)
    (true::false::(blocks (payload b)++false::false::suffix))).map (PSTRTMSeq005.leftCfg (b:=4)) ++
  (Steps.fourRightTrace (numeratorLeft archive a) false false true false
    (blocks (payload b)++false::false::suffix)).map (PSTRTMSeq005.rightCfg (a:=2))
def locateFinal (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 7 :=
  PSTRTMSeq005.rightCfg (a:=2)
    (⟨4,Turing.Tape.mk₂ (denominatorLeft archive a) (blocks (payload b)++false::false::suffix)⟩ : MachineState 4)

theorem locate_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom locateCode
      ⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight a b suffix)⟩
      (locateTrace archive a b suffix) (locateFinal archive a b suffix) := by
  apply PSTRTMSeq005.seq_runsFrom Walk.code Steps.fourRightCode
    (Walk.state 0 (false::false::archive) (inputRight a b suffix))
    (Walk.state 2 (numeratorLeft archive a) (marker (blocks (payload b)++false::false::suffix)))
    (⟨4,Turing.Tape.mk₂ (denominatorLeft archive a) (blocks (payload b)++false::false::suffix)⟩ : MachineState 4)
    (Walk.actualTrace (false::false::archive) (payload a)
      (true::false::(blocks (payload b)++false::false::suffix)))
    (Steps.fourRightTrace (numeratorLeft archive a) false false true false
      (blocks (payload b)++false::false::suffix))
  · exact Walk.field_runsFrom _ _ _
  · exact Steps.fourRight_runsFrom _ _ _ _ _ _

def moveCode : Machine 34 := PSTRTMSeq005.seqMachine Shift.code PSTRTMMulRewind085.rewindMachine
def moveTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 34) :=
  (MarkedShift.actualTrace (false::aArchive (false::archive) a) [] false true false
    suffix (payload b)).map (PSTRTMSeq005.leftCfg (b:=3)) ++
  (PSTRTMPairRewind105.fullTrace (aArchive (false::archive) a) (payload b).reverse
    (shiftSuffix suffix)).map (PSTRTMSeq005.rightCfg (a:=30))
def moveFinal (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 34 :=
  PSTRTMSeq005.rightCfg (a:=30)
    (PSTRTMMulRewind085.state 3 (false::aArchive (false::archive) a)
      (blocks (payload b)++shiftSuffix suffix))

theorem move_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom moveCode
      ⟨0,Turing.Tape.mk₂ (denominatorLeft archive a) (blocks (payload b)++false::false::suffix)⟩
      (moveTrace archive a b suffix) (moveFinal archive a b suffix) := by
  apply PSTRTMSeq005.seq_runsFrom Shift.code PSTRTMMulRewind085.rewindMachine
    (Shift.state 0 (denominatorLeft archive a) (blocks (payload b)++false::false::suffix))
    (Shift.state 30 (leftBlocks (payload b).reverse++false::aArchive (false::archive) a)
      (shiftSuffix suffix))
    (PSTRTMMulRewind085.state 3 (false::aArchive (false::archive) a)
      (blocks (payload b)++shiftSuffix suffix))
    (MarkedShift.actualTrace (false::aArchive (false::archive) a) [] false true false
      suffix (payload b))
    (PSTRTMPairRewind105.fullTrace (aArchive (false::archive) a) (payload b).reverse (shiftSuffix suffix))
  · exact MarkedShift.marked_shift_runsFrom _ _ _ _ _ _
  · exact PSTRTMPairRewind105.rewind_runsFrom _ _ _

def encodeCode : Machine 82 := PSTRTMSeq005.seqMachine moveCode (pairMachine false)
def encodeTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 82) :=
  (moveTrace archive a b suffix).map (PSTRTMSeq005.leftCfg (b:=47)) ++
  (pairTrace false (false::archive) a b (pairSuffix suffix)).map (PSTRTMSeq005.rightCfg (a:=34))
def encodeFinal (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 82 :=
  PSTRTMSeq005.rightCfg (a:=34) (pairFinal false (false::archive) a b (pairSuffix suffix))

theorem encode_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom encodeCode
      ⟨0,Turing.Tape.mk₂ (denominatorLeft archive a) (blocks (payload b)++false::false::suffix)⟩
      (encodeTrace archive a b suffix) (encodeFinal archive a b suffix) := by
  apply PSTRTMSeq005.seq_runsFrom moveCode (pairMachine false)
    (⟨0,Turing.Tape.mk₂ (denominatorLeft archive a) (blocks (payload b)++false::false::suffix)⟩ : MachineState 34)
    (moveFinal archive a b suffix)
    (pairFinal false (false::archive) a b (pairSuffix suffix))
    (moveTrace archive a b suffix) (pairTrace false (false::archive) a b (pairSuffix suffix))
    (move_runsFrom archive a b suffix)
  exact pair_runsFrom false (false::archive) a b (pairSuffix suffix)

theorem encode_final_tape (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (encodeFinal archive a b suffix).Tape = Turing.Tape.mk₂ (false::false::archive)
      (encodeNat a++encodeNat b++remainder suffix) := by
  change (pairFinal false (false::archive) a b (pairSuffix suffix)).Tape = _
  rw [pairFinal_tape]
  rfl

def rawCode : Machine 90 := PSTRTMSeq005.seqMachine locateCode encodeCode
def rawTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 90) :=
  (locateTrace archive a b suffix).map (PSTRTMSeq005.leftCfg (b:=82)) ++
  (encodeTrace archive a b suffix).map (PSTRTMSeq005.rightCfg (a:=7))
def rawFinal (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 90 :=
  PSTRTMSeq005.rightCfg (a:=7) (encodeFinal archive a b suffix)

theorem raw_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom rawCode
      ⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight a b suffix)⟩
      (rawTrace archive a b suffix) (rawFinal archive a b suffix) := by
  apply PSTRTMSeq005.seq_runsFrom locateCode encodeCode
    (⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight a b suffix)⟩ : MachineState 7)
    (locateFinal archive a b suffix) (encodeFinal archive a b suffix)
    (locateTrace archive a b suffix) (encodeTrace archive a b suffix)
    (locate_runsFrom archive a b suffix)
  exact encode_runsFrom archive a b suffix

def code : Machine 95 := PSTRTMSeq005.seqMachine rawCode Steps.prefixCode
def actualTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 95) :=
  (rawTrace archive a b suffix).map (PSTRTMSeq005.leftCfg (b:=4)) ++
  (Steps.prefixTrace archive false false (encodeNat a++encodeNat b++remainder suffix)).map
    (PSTRTMSeq005.rightCfg (a:=90))
def final (archive : List Bool) (a b : Nat) (suffix : List Bool) : MachineState 95 :=
  PSTRTMSeq005.rightCfg (a:=90)
    (⟨4,Turing.Tape.mk₂ archive (true::false::(encodeNat a++encodeNat b++remainder suffix))⟩ : MachineState 4)

theorem actual_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom code
      ⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight a b suffix)⟩
      (actualTrace archive a b suffix) (final archive a b suffix) := by
  apply PSTRTMSeq005.seq_runsFrom rawCode Steps.prefixCode
    (⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight a b suffix)⟩ : MachineState 90)
    (rawFinal archive a b suffix)
    (⟨4,Turing.Tape.mk₂ archive (true::false::(encodeNat a++encodeNat b++remainder suffix))⟩ : MachineState 4)
    (rawTrace archive a b suffix)
    (Steps.prefixTrace archive false false (encodeNat a++encodeNat b++remainder suffix))
    (raw_runsFrom archive a b suffix)
  change PSTRTMSeq005.RunsFrom Steps.prefixCode ⟨0,(encodeFinal archive a b suffix).Tape⟩ _ _
  rw [encode_final_tape]
  exact Steps.prefix_runsFrom _ _ _ _

theorem final_tape (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (final archive a b suffix).Tape =
      Turing.Tape.mk₂ archive (true::false::(encodeNat a++encodeNat b++remainder suffix)) := rfl

theorem actual_length (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (actualTrace archive a b suffix).length =
      (payload a).length^2+(payload b).length^2+15*(payload a).length+25*(payload b).length+47 := by
  simp only [actualTrace,rawTrace,encodeTrace,moveTrace,locateTrace,List.length_append,List.length_map,
    Walk.actual_length,Steps.fourRightTrace,MarkedShift.actual_length,PSTRTMPairRewind105.full_length,
    List.length_reverse,pair_length,Steps.prefixTrace,
    List.length_cons,List.length_nil]
  rw [show (if (false : Bool) = true then 1 else 0 : Nat) = 0 by decide]
  omega

theorem actual_time_le (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (actualTrace archive a b suffix).length ≤ 128*((payload a).length+(payload b).length+1)^2 := by
  rw [actual_length]
  let w := (payload a).length+(payload b).length+1
  have ha : (payload a).length ≤ w := by dsimp [w]; omega
  have hb : (payload b).length ≤ w := by dsimp [w]; omega
  have hw : 1 ≤ w := by dsimp [w]; omega
  have ha2 := Nat.pow_le_pow_left ha 2
  have hb2 := Nat.pow_le_pow_left hb 2
  have hws : w ≤ w^2 := by nlinarith
  have h1 : 1 ≤ w^2 := hw.trans hws
  change _ ≤ 128*w^2
  have square_same : ((payload a).length+(payload b).length+1)^2 = w^2 := rfl
  omega

/-- Actual 96-label positive rational serializer. The NUM0010 marker,
DEN00 and arbitrary suffix are paid and preserved. Four FALSE residue
cells remain before that suffix rather than silently disappearing. -/
theorem rational_contract (archive suffix : List Bool) (q : Rat) (hq : 0 < q) :
    ∃ states last,
      PSTRTMSeq005.RunsFrom code
        ⟨0,Turing.Tape.mk₂ (false::false::archive) (inputRight q.num.natAbs q.den suffix)⟩ states last ∧
      last.Tape = Turing.Tape.mk₂ archive (encodeDatum (.rational q)++remainder suffix) ∧
      states.length ≤ 128*(natBits q.num.natAbs+natBits q.den+1)^2 := by
  refine ⟨actualTrace archive q.num.natAbs q.den suffix,final archive q.num.natAbs q.den suffix,
    actual_runsFrom _ _ _ _,?_,?_⟩
  · rw [final_tape]
    have nonnegative : ¬q < 0 := not_lt.mpr (le_of_lt hq)
    simp only [encodeDatum,nonnegative,decide_false,List.cons_append,List.nil_append,List.append_assoc]
  · simpa only [payload_length] using actual_time_le archive q.num.natAbs q.den suffix

/-- The original retained q/risk source has DEN0010, so its TRUE,FALSE
remain explicitly after the four genuine FALSE residue cells. -/
theorem marked_rational_contract (archive suffix : List Bool) (q : Rat) (hq : 0 < q) :
    ∃ states last,
      PSTRTMSeq005.RunsFrom code
        ⟨0,Turing.Tape.mk₂ (false::false::archive)
          (blocks (payload q.num.natAbs)++marker (blocks (payload q.den)++marker suffix))⟩ states last ∧
      last.Tape = Turing.Tape.mk₂ archive
        (encodeDatum (.rational q)++remainder (true::false::suffix)) ∧
      states.length ≤ 128*(natBits q.num.natAbs+natBits q.den+1)^2 :=
  rational_contract archive (true::false::suffix) q hq

end RootB23.Threshold.Uncapped.Serialize
