module

public import B23_4_RatWordPrep_SeqCmp_WordPaths_011

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def time (background : RatInput.Stack → List Bool) (r low high : Rat) (tail scratch : List Bool) : Nat :=
  SeqCmp.twoTime background r low high r (RatPair.input 1 r (RatInput.Encoder.packet r tail)) scratch + 3 +
    SeqCmp.roundTime background 1 r (RatInput.Encoder.packet r tail) scratch +
    WordOutput.scale WordOutput.coefficient WordOutput.degree (RatPair.Link.clean background) r tail scratch

/-- Three actual comparisons. The two threshold answers are physically
popped and ORed, MAP is obtained by the third comparator, and the same
source then executes the complete original WordOutput serializer. -/
theorem actual_fields (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (r low high : Rat) (tail scratch : List Bool) :
    ∃ trace : List (State C), ∃ final : State C,
      trace.head?=some (entry background memory r low high tail scratch) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      registers final.var=((registers memory).1,decide (r≤low) || decide (high≤r),decide ((1:Rat)≤r)) ∧
      final.stk=RatInput.Encoder.bank (RatPair.Link.clean background) (RatInput.Encoder.packet r tail) scratch
        [] [] [] [] (encode [.rational r,boolDatum (decide (r≤low) || decide (high≤r)),boolDatum (decide ((1:Rat)≤r))]) [] [] ∧
      trace.length≤time background r low high tail scratch := by
  let mapSource := RatPair.input 1 r (RatInput.Encoder.packet r tail)
  let base := RatPair.Link.initial background mapSource scratch
  let lower := decide (r≤low)
  let upper := decide (high≤r)
  obtain ⟨fTrace,fFinal,fFirst,fChain,fLast,fActive,fRegs,fContents,fTime⟩ :=
    SeqCmp.actual_two .halt background memory r low high r mapSource scratch
  have fPath := front_path caller fTrace _ fFinal fFirst fChain fLast fActive
  let front : Segment caller (entry background memory r low high tail scratch) (frontCfg fFinal)
      (SeqCmp.twoTime background r low high r mapSource scratch) :=
    ⟨fTrace.map frontCfg,fPath.1,fPath.2.1,fPath.2.2,by simpa only [List.length_map] using fTime⟩
  have fTarget : frontCfg fFinal=⟨some .orFirst,fFinal.var,Function.update base 3 [lower,upper]⟩ := by
    cases fFinal with
    | mk position mem cells =>
      change position=some SeqCmp.Label.done at fActive
      subst position
      change (⟨some .orFirst,mem,cells⟩ : State C)=_
      change cells=Function.update base 3 [lower,upper] at fContents
      exact congrArg (fun stk => (⟨some .orFirst,mem,stk⟩ : State C)) fContents
  let orAfter : State C := ⟨some (.mapRound (.pair true (.collect 0))),
    recordOr (record false fFinal.var (some lower)) (some upper),Function.update base 3 []⟩
  let popped := or_path caller fFinal.var base lower upper
  let combined : Segment caller (frontCfg fFinal) orAfter 3 :=
    ⟨popped.trace,popped.head.trans (congrArg some fTarget.symm),popped.chain,popped.last,popped.count⟩
  obtain ⟨mFinal,mRound,mActive,mRegs,mContents⟩ :=
    SeqCmp.actual_round .halt true background orAfter.var 1 r (RatInput.Encoder.packet r tail) scratch
  have empty : Function.update base 3 []=base := by
    have h : base 3=[] := rfl
    rw [←h,Function.update_eq_self]
  have mapShared : mapCfg (SeqCmp.entry true background orAfter.var 1 r (RatInput.Encoder.packet r tail) scratch)=orAfter := by
    change (⟨some (.mapRound (.pair true (.collect 0))),orAfter.var,base⟩ : State C)=orAfter
    dsimp only [orAfter]
    rw [empty]
  have mPath := map_path caller mRound.trace _ mFinal mRound.head mRound.chain mRound.last mActive
  let mapped : Segment caller orAfter (mapCfg mFinal)
      (SeqCmp.roundTime background 1 r (RatInput.Encoder.packet r tail) scratch) :=
    ⟨mRound.trace.map mapCfg,mPath.1.trans (congrArg some mapShared),mPath.2.1,mPath.2.2,
      by simpa only [List.length_map] using mRound.count⟩
  have mapRegisters : registers mFinal.var=((registers memory).1,lower || upper,decide ((1:Rat)≤r)) := by
    rw [mRegs]
    change writeResult true (decide ((1:Rat)≤r))
      (registers (recordOr (record false fFinal.var (some lower)) (some upper)))=_
    rw [or_registers,fRegs]
    rfl
  let outputMemory := (outputIso C).symm mFinal.var
  obtain ⟨oTrace,oFinal,oFacts⟩ := WordOutput.actual_word_output .halt (RatPair.Link.clean background)
    outputMemory.1.1.1 outputMemory.1.1.2.1 outputMemory.1.1.2.2 outputMemory.1.2 outputMemory.2 r tail scratch
  have oPath := output_path caller oTrace _ oFinal oFacts.first oFacts.chain oFacts.last oFacts.active
  have oShared := output_shared background mFinal r tail scratch mActive mContents
  let serialized : Segment caller (mapCfg mFinal) (outputCfg oFinal)
      (WordOutput.scale WordOutput.coefficient WordOutput.degree (RatPair.Link.clean background) r tail scratch) :=
    ⟨oTrace.map outputCfg,oPath.1.trans (congrArg some oShared),oPath.2.1,oPath.2.2,
      by simpa only [List.length_map] using oFacts.time⟩
  let whole := ((front.append combined).append mapped).append serialized
  have finalRegisters : registers (outputIso C oFinal.var)=
      ((registers memory).1,lower || upper,decide ((1:Rat)≤r)) :=
    (output_registers mFinal.var oFinal.var oFacts.context_flags).trans mapRegisters
  have hit : outputMemory.1.1.2.1=(lower || upper) :=
    congrArg (fun rr : Registers C => rr.2.1) mapRegisters
  have map : outputMemory.1.1.2.2=decide ((1:Rat)≤r) :=
    congrArg (fun rr : Registers C => rr.2.2) mapRegisters
  refine ⟨whole.trace,outputCfg oFinal,whole.head,whole.chain,whole.last,?_,finalRegisters,?_,whole.count⟩
  · dsimp only [outputCfg,StoreIso.configuration,LabelMap.configuration]
    rw [oFacts.active]
    rfl
  · change oFinal.stk=_
    rw [oFacts.contents,hit,map]

def hit (r p : Rat) : Bool := decide (r≤p/(1-p) ∨ (1-p)/p≤r)
def map (r : Rat) : Bool := decide ((1:Rat)≤r)

/-- Exact original two-threshold predicate, including all rational p.
No positive-prior/H0 qualification and no host-supplied hit/MAP bit. -/
theorem actual_word (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (r p : Rat) (tail scratch : List Bool) :
    ∃ trace : List (State C), ∃ final : State C,
      trace.head?=some (entry background memory r (p/(1-p)) ((1-p)/p) tail scratch) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      registers final.var=((registers memory).1,hit r p,map r) ∧
      final.stk=RatInput.Encoder.bank (RatPair.Link.clean background) (RatInput.Encoder.packet r tail) scratch
        [] [] [] [] (encode [.rational r,boolDatum (hit r p),boolDatum (map r)]) [] [] ∧
      trace.length≤time background r (p/(1-p)) ((1-p)/p) tail scratch := by
  have predicate : (decide (r≤p/(1-p)) || decide ((1-p)/p≤r))=hit r p := by
    by_cases first : r≤p/(1-p) <;> by_cases second : (1-p)/p≤r <;> simp [hit,first,second]
  simpa only [predicate,map] using actual_fields caller background memory r (p/(1-p)) ((1-p)/p) tail scratch

end B23_4_RatWordPrep.SeqCmp.Word
