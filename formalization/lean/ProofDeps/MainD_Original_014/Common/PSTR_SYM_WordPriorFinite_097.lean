module

public import Common.PSTR_SYM_RatExportResources_095
public import Common.PSTR_SYM_WordPriorStack_096

/-! The original215 wholeTape supplies an actual finite prior field
prefix through sign. The nonblank witness comes from the original parsed
alphabet field, not caller bits/host index/empty scratch. This is directly
consumed by the SAME093 run, with exact finite source/scratch restoration. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport

open Turing PaperProofs.Common.Native PaperProofs.Statistics PSTRWordVM
open PSTRSymbolicNaturalExport PSTRTMRawNat010 PA17TMRatArithmeticParse002 PSTRTMWordPriorFront215

theorem prior_base_marker (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ tail, priorBase E target word = false :: true :: tail := by
  cases shape : (PSTRTMNatValue017.rawPayload E.alphabetSize).reverse with
  | nil =>
    have reversed := congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at reversed
    exact False.elim (PSTRSymbolicLaneArchive.rawPayload_nonempty E.alphabetSize reversed)
  | cons bit later =>
    refine ⟨bit :: (leftBlocks later ++ false :: PSTRTMWordPreparationFront214.headerLeft []
      (PSTRTMWordFrontCode213.wordData E target word).length),?_⟩
    rw [priorBase,PSTRTMWordPreparationFront214.fieldLeft,shape]
    rfl

def PriorEntry (E : BinaryExperiment) (bank : Slot → List Bool) : Prop :=
  ∃ tail, bank 1 = archive (sign E.priorOne) (numeratorDigits E.priorOne).reverse
    (denominatorDigits E.priorOne).reverse tail

theorem prior_finite_entry (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (bank : Slot → List Bool)
    (wholeLeft : ListBlank.mk (bank 1) = ListBlank.mk
      (bothLeft (false :: sign E.priorOne :: priorBase E target word)
        (numeratorDigits E.priorOne) (denominatorDigits E.priorOne))) : PriorEntry E bank := by
  obtain ⟨baseTail,baseShape⟩ := prior_base_marker E target word
  have physical : bothLeft (false :: sign E.priorOne :: priorBase E target word)
      (numeratorDigits E.priorOne) (denominatorDigits E.priorOne) =
      archive (sign E.priorOne) (numeratorDigits E.priorOne).reverse (denominatorDigits E.priorOne).reverse
        (false :: true :: baseTail) := by
    rw [baseShape]
    rfl
  rw [physical] at wholeLeft
  let frontBits := false :: (leftBlocks (denominatorDigits E.priorOne).reverse ++
    false :: (leftBlocks (numeratorDigits E.priorOne).reverse ++ false :: sign E.priorOne :: [false]))
  obtain ⟨tail,shape⟩ := finite_marked_prefix frontBits baseTail (bank 1)
    (by simpa only [frontBits,archive,List.cons_append,List.append_assoc,List.nil_append] using wholeLeft)
  refine ⟨false :: true :: tail,?_⟩
  simpa only [frontBits,archive,List.cons_append,List.append_assoc,List.nil_append] using shape

def PriorRun {C : Type*} (E : BinaryExperiment) (memory : Memory C) (bank : Slot → List Bool)
    (path : List (State C)) (final : State C) : Prop :=
  path.head? = some ⟨some 0,memory,bank⟩ ∧
  path.IsChain (fun before after => TM2.step ratProgram before = some after) ∧
  path.getLast? = some final ∧ final.l = some 4 ∧ final.var.1 = memory.1 ∧
  final.stk = Function.update bank 15
    (packet (sign E.priorOne) (numeratorDigits E.priorOne) (denominatorDigits E.priorOne) (bank 15)) ∧
  path.length ≤ 3*(bank 1).length+9 ∧
  ∀ current ∈ path, Bounded memory.1 bank (3*VirtualReturn.occupiedSlots bank+15-outside bank) current

theorem actual_current_prior {C : Type*} (E : BinaryExperiment) (memory : Memory C) (bank : Slot → List Bool)
    (entry : PriorEntry E bank) : ∃ (path : List (State C)) (final : State C), PriorRun E memory bank path final := by
  rcases memory with ⟨context,bit,flag,mode⟩
  obtain ⟨tail,shape⟩ := entry
  let numerator := (numeratorDigits E.priorOne).reverse
  let denominator := (denominatorDigits E.priorOne).reverse
  let path := ratTrace context bit flag mode (sign E.priorOne) numerator denominator tail (bank 7) (bank 15) bank
  obtain ⟨resultBit,first,chain,last,time⟩ := actual_rat_export context bit flag mode (sign E.priorOne)
    numerator denominator tail (bank 7) (bank 15) bank
  let final := state (some 4) (context,(resultBit,true,mode)) (bank 1) (bank 7)
    (packet (sign E.priorOne) (numeratorDigits E.priorOne) (denominatorDigits E.priorOne) (bank 15)) bank
  have start : state (some 0) (context,(bit,flag,mode)) (archive (sign E.priorOne) numerator denominator tail)
      (bank 7) (bank 15) bank = (⟨some 0,(context,(bit,flag,mode)),bank⟩ : State C) := by
    rw [← shape]
    exact state_rebuild _ _ bank
  have mass := bank_mass bank
  have length := congrArg List.length shape
  change (bank 1).length = (archive (sign E.priorOne) numerator denominator tail).length at length
  simp only [archive,List.length_cons,List.length_append,flagged_length] at length
  refine ⟨path,final,first.trans (congrArg some start),chain,?_,rfl,rfl,?_,?_,?_⟩
  · simpa only [path,final,numerator,denominator,List.reverse_reverse,shape] using last
  · exact bank_target bank _
  · rw [show path.length = 3*(numerator.length+denominator.length)+9 from time]
    omega
  · intro current present
    apply bounded_mono context bank _ _ current
      (rat_resources context bit flag mode (sign E.priorOne) numerator denominator tail (bank 7) (bank 15) bank current present)
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport
