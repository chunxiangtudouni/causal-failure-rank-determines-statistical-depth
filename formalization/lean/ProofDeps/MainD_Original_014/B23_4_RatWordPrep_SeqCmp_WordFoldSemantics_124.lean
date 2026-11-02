module

public import B23_4_RatWordPrep_SeqCmp_WordFoldLoop_123
public import RootB23_WordOddsBits_Public_003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

def symbols (E : BinaryExperiment) (word : E.StoppedWord) : List (Fin E.alphabetSize) :=
  (List.finRange word.1).map word.2

theorem symbols_values (E : BinaryExperiment) (word : E.StoppedWord) :
    (symbols E word).map Fin.val=WordFields.symbolValues E word := by
  simp only [symbols,List.map_map,WordFields.symbolValues]
  rfl

theorem value_eq_mul_fold (E : BinaryExperiment) (xs : List (Fin E.alphabetSize)) (odds : Rat) :
    value E xs odds=(xs.map (fun j => E.channel true j/E.channel false j)).foldl (fun a q => a*q) odds := by
  induction xs generalizing odds with
  | nil => rfl
  | cons j xs ih =>
    change value E xs ((E.channel true j/E.channel false j)*odds)=
      (xs.map (fun k => E.channel true k/E.channel false k)).foldl (fun a q => a*q)
        (odds*(E.channel true j/E.channel false j))
    rw [ih]
    exact congrArg (fun initial => (xs.map (fun k => E.channel true k/E.channel false k)).foldl
      (fun a q => a*q) initial) (mul_comm _ _)

theorem factors_symbols (E : BinaryExperiment) (word : E.StoppedWord) :
    (symbols E word).map (fun j => E.channel true j/E.channel false j)=RootB23.WordOddsBits.factors E word := by
  simp only [symbols,List.finRange,List.map_ofFn,RootB23.WordOddsBits.factors]
  rfl

/-- Identifies the actual machine's normalized fold with the ORIGINAL
word-odds definition; no revised word or supplied computed odds is used. -/
theorem value_original (E : BinaryExperiment) (word : E.StoppedWord) :
    value E (symbols E word) (E.priorOne/(1-E.priorOne))=E.rationalWordOdds word := by
  change value E (symbols E word) (E.prior true/E.prior false)=_
  rw [value_eq_mul_fold,factors_symbols,←RootB23.WordOddsBits.rationalWordOdds_eq_foldl]

end B23_4_RatWordPrep.WordFold
