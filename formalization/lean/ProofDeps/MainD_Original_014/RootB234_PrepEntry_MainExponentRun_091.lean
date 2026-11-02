module

public import RootB234_PrepEntry_MainExponentCode_090

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*} {I : Instance}

def state (point : Label) (memory : Store C) (bank : RatInput.Stack→List Bool) : State C := ⟨some point,memory,bank⟩

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same];rfl
  exact ⟨front.trace++back.trace.tail,by rw [List.head?_append,front.first];rfl,
    NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain),
    (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)⟩

theorem Segment.append_length {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length≤front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length≤_
  simp only [List.length_append,List.length_tail];omega

theorem label_path {Λ : Type*} (mapping : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ (Store C)) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (trace : List (TM2.Cfg RatInput.Alphabet Λ (Store C)))
    (before final : TM2.Cfg RatInput.Alphabet Λ (Store C))
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (mapping point)=LabelMap.statement mapping (old point)) :
    (trace.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping before) ∧
    (trace.map (LabelMap.configuration mapping)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) := by
  have proper:=NativeMulLink.no_early_halt_port old port atPort trace final chain last active
  have linked:=LabelMap.actual_path_on mapping old (program caller) trace before final first chain last
    (by intro current member point selected;exact same point (by intro equal;subst point;exact proper current member selected))
  exact ⟨linked.1,linked.2.1,linked.2.2.1⟩

theorem store_label_path {σ Λ : Type*} (iso : σ ≃ Store C) (mapping : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program caller (mapping point)=LabelMap.statement mapping (StoreIso.statement iso (old point))) :
    let cfg := fun current => LabelMap.configuration mapping (StoreIso.configuration iso current)
    (trace.map cfg).head?=some (cfg before) ∧
    (trace.map cfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map cfg).getLast?=some (cfg final) := by
  let changed := StoreIso.machine iso old
  have stored := StoreIso.actual_path_on iso old changed trace before final first chain last
    (by intro current member point selected;rfl)
  have atPort' : changed port=.halt := by change StoreIso.statement iso (old port)=_;rw [atPort];rfl
  have path := label_path mapping changed caller port atPort' _ _ _ stored.1 stored.2.1 stored.2.2.1 active same
  simp only [List.map_map,Function.comp_def] at path
  exact path

def budgetCfg (before : Budget.State (Global.Store (StageChannels.Store C))) : State C :=
  LabelMap.configuration budgetLabel before

def exponentCfg (before : Global.State (ExponentContext C)) : State C :=
  LabelMap.configuration exponentLabel (StoreIso.configuration (exponentIso C) before)

def metadataBank (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  Budget.outputBank bits stages tools budget

def exponentBank (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  Global.bank (metadataBank bits stages tools budget)
    (RatInput.Encoder.packet (Global.qValue stages) (RatInput.Encoder.packet budget []))
    (NatField.packet (BinaryExperiment.quotaExponent budget stages) []) (RatInput.Encoder.packet budget []) [] [] []

theorem metadata_ready (bits : List Bool) (stages tools : Nat) (budget : Rat) :
    QLoop.bank (metadataBank bits stages tools budget) [] [] (RatInput.Encoder.packet budget []) []=
      metadataBank bits stages tools budget := by
  funext slot
  fin_cases slot <;> rfl

theorem budget_shared (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (final : Budget.State (Global.Store (StageChannels.Store C))) (active : final.l=some .done)
    (contents : final.stk=metadataBank bits stages tools budget) :
    budgetCfg final=exponentCfg (Global.state default ((exponentIso C).symm final.var)
      (QLoop.bank (metadataBank bits stages tools budget) [] [] (RatInput.Encoder.packet budget []) [])) := by
  cases final with
  | mk point memory bank =>
    change point=some .done at active
    subst point
    change (⟨some (.exponent default),memory,bank⟩ : State C)=
      ⟨some (.exponent default),exponentIso C ((exponentIso C).symm memory),_⟩
    rw [Equiv.apply_symm_apply,metadata_ready]
    exact congrArg (state (.exponent default) memory) contents

theorem exponent_stage (memory : Store C) :
    (QLoop.rootContext ((exponentIso C).symm memory)).2=
      QLoop.rootContext (Budget.callerContext memory) := rfl

/-- Budget029 really produces all E work banks empty; its complete
finite metadata and stage blocks remain allocated before the literal
original input. Root E starts with that actual memory and returns its
original exponent, without a staged archive to park or reload. -/
theorem through_exponent (caller : Statement C) (context : C)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (positive : 0<budget) :
    ∃ (afterMemory : Global.Store (ExponentContext C)) (part : Segment caller
      (entry context (preparationInput input contract budget))
      (state (.natural default) (exponentIso C afterMemory)
        (exponentBank (preparationInput input contract budget) I.stageCount I.toolCount budget))),
      (QLoop.rootContext afterMemory).2=WholeChannels.stageMemory context ∧
      callerContext (exponentIso C afterMemory)=context ∧
      part.trace.length≤Budget.coefficient*((preparationInput input contract budget).length+1)^3+
        Global.totalCost (metadataBank (preparationInput input contract budget) I.stageCount I.toolCount budget) [] budget I.stageCount := by
  let bits:=preparationInput input contract budget
  let background:=metadataBank bits I.stageCount I.toolCount budget
  obtain ⟨bRun,bFinal,bFacts⟩:=Budget.actual_polynomial (globalMemory context) input contract budget
  have budgetPath:=label_path budgetLabel (Budget.program .halt) caller .done rfl bRun _ bFinal
    bFacts.first bFacts.chain bFacts.last bFacts.active
    (by intro point different;simp only [budgetLabel,different,ite_false,program])
  let front : Segment caller (entry context bits) (budgetCfg bFinal):=
    ⟨bRun.map budgetCfg,budgetPath.1,budgetPath.2.1,budgetPath.2.2⟩
  let beforeMemory:=(exponentIso C).symm bFinal.var
  obtain ⟨afterMemory,exponent,exponentContext,_flags,count⟩:=
    Global.actual_original .halt background beforeMemory [] budget I.stageCount positive rfl
  have exponentPath:=store_label_path (exponentIso C) exponentLabel (Global.program .halt) caller .done rfl
    exponent.trace _ _ exponent.first exponent.chain exponent.last rfl
    (by intro point different;simp only [exponentLabel,different,ite_false,program])
  have shared:=budget_shared bits I.stageCount I.toolCount budget bFinal bFacts.active bFacts.contents
  let back : Segment caller (budgetCfg bFinal)
      (state (.natural default) (exponentIso C afterMemory) (exponentBank bits I.stageCount I.toolCount budget)):=
    ⟨exponent.trace.map exponentCfg,exponentPath.1.trans (congrArg some shared.symm),exponentPath.2.1,exponentPath.2.2⟩
  have originalStage : (QLoop.rootContext beforeMemory).2=WholeChannels.stageMemory context := by
    rw [exponent_stage,bFacts.context_eq]
    rfl
  have finalStage : (QLoop.rootContext afterMemory).2=WholeChannels.stageMemory context :=
    (congrArg Prod.snd exponentContext).trans originalStage
  let whole:=front.append back
  refine ⟨afterMemory,whole,finalStage,?_,?_⟩
  · rw [exponent_context,finalStage]
    rfl
  · have frontCount : front.trace.length≤Budget.coefficient*(bits.length+1)^3 := by
      simpa only [front,List.length_map] using bFacts.time
    have backCount : back.trace.length≤Global.totalCost background [] budget I.stageCount := by
      simpa only [back,List.length_map] using count
    exact (front.append_length back).trans (Nat.add_le_add frontCount backCount)

end RootB234.PrepEntry.MainExponent

