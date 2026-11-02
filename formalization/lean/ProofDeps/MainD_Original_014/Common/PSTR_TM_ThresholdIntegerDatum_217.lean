module
public import Common.PSTR_TM_ThresholdUnitDenominator_216
public import Common.PSTR_TM_Prepend_022

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdIntegerDatum217
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdUnitDenominator216

/-! The SAME frozen022 literal program [TRUE,FALSE], on exactly TWO owned
FALSE cells. Only a narrow retained-tape proof is derived here, following
the mature SYM015 sequencing argument. Its foreign022 product metadata
differs from our immutable022 product, so no mixed foreign cone is loaded.
This consumes both guard cells; the final left side is EXACT archive,
without an invented fresh output guard. It is not a generic allocator. -/

def signTrace (archive input : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩,
   ⟨1,Turing.Tape.mk₂ (false::archive) (false::input)⟩,
   ⟨2,Turing.Tape.mk₂ (false::archive) (false::input)⟩]

theorem sign_runsFrom (archive input : List Bool) :
    PSTRTMSeq005.RunsFrom (PSTRTMPrepend022.bitMachine false)
      ⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩ (signTrace archive input)
      ⟨2,Turing.Tape.mk₂ (false::archive) (false::input)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [signTrace,List.isChain_cons_cons,Turing.TM0.step,PSTRTMPrepend022.bitMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,PSTRTMPrepend022.bitMachine]

def nilState (archive input : List Bool) : MachineState 0 :=
  ⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩

def signPrefixTrace (archive input : List Bool) : List (MachineState 3) :=
  [nilState archive input].map (PSTRTMSeq005.leftCfg (b := 2)) ++
    (signTrace archive input).map (PSTRTMSeq005.rightCfg (a := 0))

def signPrefixFinal (archive input : List Bool) : MachineState 3 :=
  PSTRTMSeq005.rightCfg (a := 0) (b := 2) ⟨2,Turing.Tape.mk₂ (false::archive) (false::input)⟩

theorem signPrefix_runsFrom (archive input : List Bool) :
    PSTRTMSeq005.RunsFrom (PSTRTMPrepend022.prefixMachine [false])
      ⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩ (signPrefixTrace archive input)
      (signPrefixFinal archive input) := by
  apply PSTRTMSeq005.seq_runsFrom (PSTRTMPrepend022.prefixMachine []) (PSTRTMPrepend022.bitMachine false)
    (nilState archive input) (nilState archive input)
    ⟨2,Turing.Tape.mk₂ (false::archive) (false::input)⟩ [nilState archive input] (signTrace archive input)
  · exact ⟨rfl,.singleton _,rfl,rfl⟩
  · exact sign_runsFrom archive input

def trueTrace (archive input : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ (false::archive) (false::input)⟩,
   ⟨1,Turing.Tape.mk₂ archive (false::false::input)⟩,
   ⟨2,Turing.Tape.mk₂ archive (true::false::input)⟩]

/-- Exact alias of existing fixed literal code, no new prefix program. -/
def tagMachine : Machine 6 := PSTRTMPrepend022.prefixMachine [true,false]

def tagTrace (archive input : List Bool) : List (MachineState 6) :=
  (signPrefixTrace archive input).map (PSTRTMSeq005.leftCfg (b := 2)) ++
    (trueTrace archive input).map (PSTRTMSeq005.rightCfg (a := 3))

def tagFinal (archive input : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a := 3) (b := 2) ⟨2,Turing.Tape.mk₂ archive (true::false::input)⟩

theorem tag_runsFrom (archive input : List Bool) :
    PSTRTMSeq005.RunsFrom tagMachine ⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩
      (tagTrace archive input) (tagFinal archive input) := by
  apply PSTRTMSeq005.seq_runsFrom (PSTRTMPrepend022.prefixMachine [false]) (PSTRTMPrepend022.bitMachine true)
    ⟨0,Turing.Tape.mk₂ (false::false::archive) input⟩ (signPrefixFinal archive input)
    ⟨2,Turing.Tape.mk₂ archive (true::false::input)⟩ (signPrefixTrace archive input) (trueTrace archive input)
    (signPrefix_runsFrom archive input)
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [trueTrace,List.isChain_cons_cons,Turing.TM0.step,PSTRTMPrepend022.bitMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,PSTRTMPrepend022.bitMachine]

theorem tag_length (archive input : List Bool) : (tagTrace archive input).length = 7 := by
  simp [tagTrace,signPrefixTrace,signTrace,trueTrace]

/-- Fixed33-label real unit-denominator producer, using the frozen marker
inverse004d. No blank suffix is silently reinterpreted as encoded data. -/
def unitMachine : Machine 32 :=
  PSTRTMSeq005.seqMachine prepareMachine PA17TMRatArithmeticUnblock004.markerMachine

def unitTrace (archive digits : List Bool) : List (MachineState 32) :=
  (prepareTrace archive digits).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PA17TMRatArithmeticUnblock004.markerTrace archive digits [false,true]).map
      (PSTRTMSeq005.rightCfg (a := 12))

def unitFinal (archive digits : List Bool) : MachineState 32 :=
  PSTRTMSeq005.rightCfg (a := 12) (PSTRTMUnblock018.state 19 (false::archive)
    (PSTRTMUnblockTrace019.rawWord digits ++ [true,false,true]))

theorem unit_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom unitMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)⟩
      (unitTrace archive digits) (unitFinal archive digits) := by
  apply PSTRTMSeq005.seq_runsFrom prepareMachine PA17TMRatArithmeticUnblock004.markerMachine
    ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)⟩ (prepareFinal archive digits)
    (PSTRTMUnblock018.state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ [true,false,true]))
    (prepareTrace archive digits) (PA17TMRatArithmeticUnblock004.markerTrace archive digits [false,true])
    (prepare_runsFrom archive digits)
  exact PA17TMRatArithmeticUnblock004.marker_runsFrom archive digits [false,true]

theorem unit_length (archive digits : List Bool) :
    (unitTrace archive digits).length = digits.length^2 + 15*digits.length + 18 := by
  simp only [unitTrace,List.length_append,List.length_map,prepare_length,
    PA17TMRatArithmeticUnblock004.marker_length]
  omega

/-- Fixed40 labels for this special natural-valued Rat Datum. BOTH actual
false guards are consumed; all remaining archive cells survive unchanged. -/
def integerDatumMachine : Machine 39 := PSTRTMSeq005.seqMachine unitMachine tagMachine

def integerDatumTrace (archive : List Bool) (n : Nat) : List (MachineState 39) :=
  (unitTrace (false::archive) (PSTRTMNatValue017.rawPayload n)).map (PSTRTMSeq005.leftCfg (b := 6)) ++
    (tagTrace archive (PSTRTMUnblockTrace019.rawWord (PSTRTMNatValue017.rawPayload n) ++ [true,false,true])).map
      (PSTRTMSeq005.rightCfg (a := 32))

def integerDatumFinal (archive : List Bool) (n : Nat) : MachineState 39 :=
  PSTRTMSeq005.rightCfg (a := 32) (tagFinal archive
    (PSTRTMUnblockTrace019.rawWord (PSTRTMNatValue017.rawPayload n) ++ [true,false,true]))

theorem integerDatum_runsFrom (archive : List Bool) (n : Nat) :
    PSTRTMSeq005.RunsFrom integerDatumMachine
      ⟨0,Turing.Tape.mk₂ (false::false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))⟩
      (integerDatumTrace archive n) (integerDatumFinal archive n) := by
  apply PSTRTMSeq005.seq_runsFrom unitMachine tagMachine
    ⟨0,Turing.Tape.mk₂ (false::false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))⟩
    (unitFinal (false::archive) (PSTRTMNatValue017.rawPayload n))
    (tagFinal archive (PSTRTMUnblockTrace019.rawWord (PSTRTMNatValue017.rawPayload n) ++ [true,false,true]))
    (unitTrace (false::archive) (PSTRTMNatValue017.rawPayload n))
    (tagTrace archive (PSTRTMUnblockTrace019.rawWord (PSTRTMNatValue017.rawPayload n) ++ [true,false,true]))
    (unit_runsFrom _ _)
  exact tag_runsFrom archive _

theorem integerDatum_final_tape (archive : List Bool) (n : Nat) :
    (integerDatumFinal archive n).Tape = Turing.Tape.mk₂ archive (encodeDatum (.rational (n : Rat))) := by
  have hn : ¬(n : Rat) < 0 := not_lt.mpr (Nat.cast_nonneg _)
  simp [integerDatumFinal,tagFinal,PSTRTMSeq005.rightCfg,
    PA17TMRatArithmeticUnblock004.rawWord_payload,encodeDatum,hn,encodeNat,natBits]

theorem integerDatum_length (archive : List Bool) (n : Nat) :
    (integerDatumTrace archive n).length = (natBits n)^2 + 15*natBits n + 25 := by
  simp only [integerDatumTrace,List.length_append,List.length_map,unit_length,tag_length,
    PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem integerDatum_time_le (archive : List Bool) (n : Nat) :
    (integerDatumTrace archive n).length ≤ 64*(natBits n + 1)^2 := by
  rw [integerDatum_length]
  nlinarith [Nat.zero_le ((natBits n)^2)]

theorem integerDatum_prefix_space_le (archive : List Bool) (n inputLength clock : Nat) :
    visitedSpace integerDatumMachine inputLength ((integerDatumTrace archive n).take clock) ≤
      inputLength + 128*(natBits n + 1)^2 + 1 := by
  have ht := integerDatum_time_le archive n
  have hs := PSTRTMTrace002.visitedSpace_le integerDatumMachine inputLength
    ((integerDatumTrace archive n).take clock)
  have hl : ((integerDatumTrace archive n).take clock).length ≤ (integerDatumTrace archive n).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdIntegerDatum217
