module
public import Structure.PA17_TM_RatArithmetic_Width_018j

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

def originalBank (x y : Rat) (suffix : List Bool) : List Bool :=
  bank (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
    (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y)) suffix

theorem originalBank_bookmark (x y : Rat) : originalBank x y [true]=nxRight x y := rfl

theorem originalWidth_eq (x y : Rat) :
    bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))=fieldWidth x y := by
  unfold bankWidth fieldWidth
  rw [clampFirst_length _ (numerator_ne_nil x),clampFirst_length _ (denominator_ne_nil x),
    clampFirst_length _ (numerator_ne_nil y),clampFirst_length _ (denominator_ne_nil y)]

theorem counter_zero_tape (sx : Bool) (right : List Bool) :
    Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones 0)) right =
      Turing.Tape.mk₂ (false::sx::listPrefixLeft []) right := by
  change Turing.Tape.mk₂ ((false::sx::listPrefixLeft [])++[false]) right = _
  simp only [Turing.Tape.mk₂,PSTRTMRawNat010.blank_append_false]

theorem raw_width_runs (x y : Rat) :
    ∃ trace, Runs widthMachine (encode [.rational x,.rational y]) trace
      (widthFinal (mNx x y) (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones (fieldWidth x y))
        (prefixRight (sign x) (originalBank x y [true])))) ∧
      trace.length≤256*(fieldWidth x y+1)^2 := by
  obtain ⟨tm,hm,hlm⟩ := middle_memory_runs (mNx x y) (sign x) 0
    (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail [true]
  change PSTRTMSeq005.RunsFrom widthMachine
    (widthEntry (mNx x y) (Turing.Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones 0))
      (originalBank x y [true]))) tm
    (widthFinal (mNx x y) (Turing.Tape.mk₂
      (false::ROOTTMGCDCounter011.ones (0+bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
        (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))))
      (prefixRight (sign x) (originalBank x y [true])))) at hm
  rw [originalWidth_eq,Nat.zero_add] at hm
  change tm.length≤bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
    (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))*
    (2*0+6*bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))+68)+48 at hlm
  rw [Nat.mul_zero,Nat.zero_add,originalWidth_eq] at hlm
  have htape : (rawBookmarkFinal x y).Tape=
      Turing.Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones 0)) (originalBank x y [true]) := by
    rw [rawBookmark_final_tape,originalBank_bookmark]
    exact (counter_zero_tape (sign x) (nxRight x y)).symm
  have hr := rawBookmark_runs x y
  have hrf : PSTRTMSeq005.RunsFrom (widthFamily (0 : Fin 33))
      (Turing.TM0.init (encode [.rational x,.rational y])) (rawBookmarkTrace x y) (rawBookmarkFinal x y) :=
    ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩
  have hs := block_segment widthFamily widthPorts (0 : Fin 33) _ _ _ hrf
  let tr0 : List (MachineState 79265) :=
    (rawBookmarkTrace x y).map (blockCfg (s:=2401) (0 : Fin 33))
  change Segment widthMachine
    (blockCfg (s:=2401) (0 : Fin 33) (Turing.TM0.init (encode [.rational x,.rational y])))
    tr0 (blockCfg (s:=2401) (0 : Fin 33) (rawBookmarkFinal x y)) at hs
  have ht := raw_memory_transfer x y
  rw [htape] at ht
  have hf := segment_append widthMachine
    (blockCfg (s:=2401) (0 : Fin 33) (Turing.TM0.init (encode [.rational x,.rational y])))
    (blockCfg (s:=2401) (0 : Fin 33) (rawBookmarkFinal x y))
    (widthEntry (mNx x y) (Turing.Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones 0))
      (originalBank x y [true])))
    (widthFinal (mNx x y) (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones (fieldWidth x y))
      (prefixRight (sign x) (originalBank x y [true]))))
    tr0 tm hs ⟨hm.1,hm.2.1,hm.2.2.1⟩ ht
  refine ⟨tr0++tm,?_,?_⟩
  · apply PSTRTMTrace002.runs_of_chain
    · simpa [Turing.TM0.init,blockCfg,label] using hf.1
    · exact hf.2.1
    · exact hf.2.2
    · exact hm.2.2.2
  · have htr0 : tr0.length=(rawBookmarkTrace x y).length := by
      change ((rawBookmarkTrace x y).map (blockCfg (s:=2401) (0 : Fin 33))).length=(rawBookmarkTrace x y).length
      exact List.length_map _
    rw [List.length_append,htr0]
    have hraw := rawBookmark_time x y
    nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

/-- The original width is bounded by the original raw input, including
all four natural headers, both signs and the actual outer footer. -/
theorem original_width_le_input (x y : Rat) : fieldWidth x y≤(encode [.rational x,.rational y]).length := by
  have hw : (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 := pair_length x y
  rw [hw]
  omega

theorem original_width_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones (fieldWidth x y))
          (prefixRight (sign x) (originalBank x y [true])) ∧
        final.q.val=((mNx x y).val+1)*2402+645 ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        visitedSpace program (encode [.rational x,.rational y]).length trace≤
          c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨79265,1024,2,widthMachine,by decide,by decide,?_⟩
  intro x y
  obtain ⟨trace,hr,hl⟩ := raw_width_runs x y
  let tape := Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones (fieldWidth x y))
    (prefixRight (sign x) (originalBank x y [true]))
  have hw : (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 := pair_length x y
  refine ⟨trace,widthFinal (mNx x y) tape,hr,rfl,widthFinal_label (mNx x y) tape,?_,?_⟩
  · rw [hw]
    nlinarith [Nat.zero_le ((fieldWidth x y)^2)]
  · have hs := PSTRTMTrace002.visitedSpace_le widthMachine (encode [.rational x,.rational y]).length trace
    rw [hw] at hs ⊢
    nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
