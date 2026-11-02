module

public import B23_4_RatWordPrep_SeqCmp_RawPublic_028
public import Common.PSTR_WordBool_RatInputComplementUniform_098

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

abbrev Store (C : Type*) := RatInput.Complement.Store (RawGetter.Store C)

inductive Label where
  | front : RatInput.Complement.Label → Label
  | read : RawGetter.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.front default⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def rawIso (C : Type*) : RawGetter.Store (RatInput.Complement.Store C) ≃ Store C where
  toFun := fun ⟨⟨⟨⟨⟨⟨⟨c,prior⟩,rat⟩,fmt⟩,native⟩,reader⟩,rawNative⟩,rawExport⟩ =>
    (((((((c,rawNative),rawExport),prior),rat),fmt),native),reader)
  invFun := fun ⟨⟨⟨⟨⟨⟨⟨c,rawNative⟩,rawExport⟩,prior⟩,rat⟩,fmt⟩,native⟩,reader⟩ =>
    (((((((c,prior),rat),fmt),native),reader),rawNative),rawExport)
  left_inv := by rintro ⟨⟨⟨⟨⟨⟨⟨c,prior⟩,rat⟩,fmt⟩,native⟩,reader⟩,rawNative⟩,rawExport⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨⟨⟨⟨c,rawNative⟩,rawExport⟩,prior⟩,rat⟩,fmt⟩,native⟩,reader⟩; rfl

def context (memory : Store C) : C := memory.1.1.1.1.1.1.1

def frontLabel (point : RatInput.Complement.Label) : Label :=
  if point=.done then .read .boot else .front point
def readLabel (point : RawGetter.Label) : Label := if point=.done then .done else .read point

noncomputable def program (caller : Statement C) : Label → Statement C
  | .front point => LabelMap.statement frontLabel (RatInput.Complement.program .halt point)
  | .read point => LabelMap.statement readLabel
    (StoreIso.statement (rawIso C) (RawGetter.program .halt point))
  | .done => caller

def frontCfg (before : RatInput.Complement.State (RawGetter.Store C)) : State C :=
  LabelMap.configuration frontLabel before
def readCfg (before : RawGetter.State (RatInput.Complement.Store C)) : State C :=
  LabelMap.configuration readLabel (StoreIso.configuration (rawIso C) before)

def entry (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags) (reader : RatInput.Complement.Reader)
    (bits : List Bool) : State C := frontCfg (RatInput.Complement.initial memory native reader bits)

def afterFee (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Bool :=
  ((PSTRTMWordFrontCode213.wordData E target word).drop 3).flatMap encodeDatum

theorem after_prior_fee (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    PSTRTMWordPriorFront215.afterPrior E target word=encodeDatum (.rational E.observationFee)++afterFee E target word++[true] := by
  have split : (PSTRTMWordFrontCode213.wordData E target word).drop 2=
      Datum.rational E.observationFee::(PSTRTMWordFrontCode213.wordData E target word).drop 3 := rfl
  unfold PSTRTMWordPriorFront215.afterPrior
  rw [split,List.flatMap_cons]
  rfl

theorem shared (before : RatInput.Complement.State (RawGetter.Store C)) (active : before.l=some .done) :
    readCfg (⟨some .boot,(rawIso C).symm before.var,before.stk⟩ : RawGetter.State (RatInput.Complement.Store C))=frontCfg before := by
  cases before with
  | mk position memory contents =>
    change position=some RatInput.Complement.Label.done at active
    subst position
    change (⟨some (.read .boot),rawIso C ((rawIso C).symm memory),contents⟩ : State C)=⟨some (.read .boot),memory,contents⟩
    rw [Equiv.apply_symm_apply]

theorem front_path (caller : Statement C) (trace : List (RatInput.Complement.State (RawGetter.Store C)))
    (before final : RatInput.Complement.State (RawGetter.Store C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (RatInput.Complement.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map frontCfg).head?=some (frontCfg before) ∧
    (trace.map frontCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map frontCfg).getLast?=some (frontCfg final) := by
  have proper := NativeMulLink.no_early_halt_port (RatInput.Complement.program .halt) .done rfl trace final chain last active
  have mapped := LabelMap.actual_path_on frontLabel (RatInput.Complement.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [frontLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem read_path (caller : Statement C) (trace : List (RawGetter.State (RatInput.Complement.Store C)))
    (before final : RawGetter.State (RatInput.Complement.Store C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (RawGetter.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map readCfg).head?=some (readCfg before) ∧
    (trace.map readCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map readCfg).getLast?=some (readCfg final) := by
  let old := RawGetter.program (C := RatInput.Complement.Store C) .halt
  let isoProgram := StoreIso.machine (rawIso C) old
  have iso := StoreIso.actual_path_on (rawIso C) old isoProgram trace before final first chain last
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on readLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notDone : point≠.done := by intro same; subst point; exact proper current member selected
      simp only [readLabel,notDone,ite_false,program]
      rfl)
  have maps : (trace.map (StoreIso.configuration (rawIso C))).map (LabelMap.configuration readLabel)=trace.map readCfg := by
    rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end B23_4_RatWordPrep.OriginalFee
