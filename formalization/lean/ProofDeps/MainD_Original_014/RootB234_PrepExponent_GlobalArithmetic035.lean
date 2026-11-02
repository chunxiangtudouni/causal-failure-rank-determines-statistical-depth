module

public import RootB234_PrepExponent_GlobalPackets034

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

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

def mulEntry (background : Stack → List Bool) (memory : Store C) (cache exponent : List Bool)
    (x y : Rat) (tail : List Bool) : QLoop.RawState C :=
  let m := QLoop.rawMemory memory
  RatBinary.entry (QLoop.rawBackground background cache exponent) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache

def mulCfg (site : MulSite) (before : QLoop.RawState C) : State C :=
  LabelMap.configuration (mulLabel site) (StoreIso.configuration (QLoop.arithmeticIso C)
    (Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C)) before))

theorem mul_entry (site : MulSite) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    mulCfg site (mulEntry background memory cache exponent x y tail)=
      state (.mul site default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []) := by
  have vars : QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
      (mulEntry background memory cache exponent x y tail).var)=memory := by
    change QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C) (QLoop.rawMemory memory))=memory
    simp only [QLoop.rawMemory,Equiv.apply_symm_apply]
  unfold mulCfg LabelMap.configuration StoreIso.configuration Arithmetic.binaryConfiguration StackIso.configuration
  change (⟨some (.mul site default),QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
    (mulEntry background memory cache exponent x y tail).var),_⟩ : State C)=_
  rw [vars]
  congr 1
  funext slot
  fin_cases slot <;> try rfl
  change (mulEntry background memory cache exponent x y tail).stk 15=RatPair.input x y tail
  let m := QLoop.rawMemory memory
  exact RatPair.entry_source (QLoop.rawBackground background cache exponent) ((m.1.1.1.1.1,m.1.2),m.2)
    m.1.1.1.1.2.1 m.1.1.1.1.2.2 m.1.1.1.2 m.1.1.2 x y tail cache

theorem binary_final_bank (background : Stack → List Bool) (cache exponent : List Bool) (value : Rat) (tail : List Bool) :
    StackIso.slots Arithmetic.binaryRoles
      (RatPair.Link.finalContents (QLoop.rawBackground background cache exponent) (RatPair.packet value tail) cache [])=
      bank background cache exponent (RatInput.Encoder.packet value tail) [] [] [] := by
  funext slot
  fin_cases slot <;> rfl

theorem mul_actual (caller : Statement C) (site : MulSite) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.mul site default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []))
      (state (mulNext site) afterMemory (bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length ≤ RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache exponent) x y tail cache := by
  let m := QLoop.rawMemory memory
  let oldBackground := QLoop.rawBackground background cache exponent
  obtain ⟨run,final,facts,first,chain,last,active,contexts,contents⟩ := Arithmetic.actual_mul
    oldBackground m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache
  let arithmeticCfg := Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C))
  let arithmeticFinal := arithmeticCfg final
  have path := store_label_path (QLoop.arithmeticIso C) (mulLabel site) Arithmetic.mulProgram caller .done rfl
    (run.map arithmeticCfg) _ arithmeticFinal first chain last active
    (by intro point different;simp only [mulLabel,different,ite_false,program])
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map (mulCfg site)).head?=some (mulCfg site (mulEntry background memory cache exponent x y tail)) := path.1
  rw [mul_entry] at first'
  let afterMemory := QLoop.arithmeticIso C arithmeticFinal.var
  have finalSlots : arithmeticFinal.stk=bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] [] :=
    contents.trans (binary_final_bank background cache exponent (x*y) tail)
  have lastState : mulCfg site final=state (mulNext site) afterMemory
      (bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] []) := by
    change (⟨arithmeticFinal.l.map (mulLabel site),afterMemory,arithmeticFinal.stk⟩ : State C)=_
    rw [active,finalSlots]
    rfl
  have oldContext : m.1.1.1.1.1.2.1=((QLoop.arithmeticIso C).symm memory).2.1 := by
    rw [←Arithmetic.mul_context (PacketUnary.Store C) m]
    dsimp only [m,QLoop.rawMemory]
    rw [Equiv.apply_symm_apply]
  refine ⟨afterMemory,⟨run.map (mulCfg site),first',path.2.1,path.2.2.trans (congrArg some lastState)⟩,?_,?_⟩
  · change arithmeticFinal.var.2.1.1.1=QLoop.rootContext memory
    exact congrArg (fun value : PacketUnary.Store C => value.1.1) (contexts.trans oldContext)
  · simpa only [List.length_map] using facts.count

abbrev RawSubStore (C : Type*) := RatBinary.Store (Arithmetic.SubContext (PacketUnary.Store C)) RatAddSub.addSubStates
abbrev RawSubState (C : Type*) := RatBinary.State (Arithmetic.SubContext (PacketUnary.Store C)) RatAddSub.addSubStates

def subMemory (memory : Store C) : RawSubStore C :=
  (Arithmetic.subIso (PacketUnary.Store C)).symm ((QLoop.arithmeticIso C).symm memory)

def subEntry (background : Stack → List Bool) (memory : Store C) (cache exponent : List Bool)
    (x y : Rat) (tail : List Bool) : RawSubState C :=
  let m := subMemory memory
  RatBinary.entry (QLoop.rawBackground background cache exponent) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache

def subCfg (before : RawSubState C) : State C :=
  LabelMap.configuration subLabel (StoreIso.configuration (QLoop.arithmeticIso C)
    (Arithmetic.binaryConfiguration (Arithmetic.subIso (PacketUnary.Store C)) before))

theorem sub_entry (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    subCfg (subEntry background memory cache exponent x y tail)=
      state (.subtract default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []) := by
  have vars : QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C)
      (subEntry background memory cache exponent x y tail).var)=memory := by
    change QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C) (subMemory memory))=memory
    simp only [subMemory,Equiv.apply_symm_apply]
  unfold subCfg LabelMap.configuration StoreIso.configuration Arithmetic.binaryConfiguration StackIso.configuration
  change (⟨some (.subtract default),QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C)
    (subEntry background memory cache exponent x y tail).var),_⟩ : State C)=_
  rw [vars]
  congr 1
  funext slot
  fin_cases slot <;> try rfl
  change (subEntry background memory cache exponent x y tail).stk 15=RatPair.input x y tail
  let m := subMemory memory
  exact RatPair.entry_source (QLoop.rawBackground background cache exponent) ((m.1.1.1.1.1,m.1.2),m.2)
    m.1.1.1.1.2.1 m.1.1.1.1.2.2 m.1.1.1.2 m.1.1.2 x y tail cache

theorem sub_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.subtract default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []))
      (state (.reader 0) afterMemory (bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length ≤ RatBinary.time RatAddSub.addSubCoefficient (QLoop.rawBackground background cache exponent) x y tail cache := by
  let m := subMemory memory
  let oldBackground := QLoop.rawBackground background cache exponent
  obtain ⟨run,final,facts,first,chain,last,active,contexts,contents⟩ := Arithmetic.actual_sub
    oldBackground m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache
  let arithmeticCfg := Arithmetic.binaryConfiguration (Arithmetic.subIso (PacketUnary.Store C))
  let arithmeticFinal := arithmeticCfg final
  have path := store_label_path (QLoop.arithmeticIso C) subLabel Arithmetic.subProgram caller .done rfl
    (run.map arithmeticCfg) _ arithmeticFinal first chain last active
    (by intro point different;simp only [subLabel,different,ite_false,program])
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map subCfg).head?=some (subCfg (subEntry background memory cache exponent x y tail)) := path.1
  rw [sub_entry] at first'
  let afterMemory := QLoop.arithmeticIso C arithmeticFinal.var
  have finalSlots : arithmeticFinal.stk=bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] [] :=
    contents.trans (binary_final_bank background cache exponent (x-y) tail)
  have lastState : subCfg final=state (.reader 0) afterMemory
      (bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] []) := by
    change (⟨arithmeticFinal.l.map subLabel,afterMemory,arithmeticFinal.stk⟩ : State C)=_
    rw [active,finalSlots]
    rfl
  have oldContext : m.1.1.1.1.1.2.1=((QLoop.arithmeticIso C).symm memory).2.1 := by
    rw [←Arithmetic.sub_context (PacketUnary.Store C) m]
    dsimp only [m,subMemory]
    rw [Equiv.apply_symm_apply]
  refine ⟨afterMemory,⟨run.map subCfg,first',path.2.1,path.2.2.trans (congrArg some lastState)⟩,?_,?_⟩
  · change arithmeticFinal.var.2.1.1.1=QLoop.rootContext memory
    exact congrArg (fun value : PacketUnary.Store C => value.1.1) (contexts.trans oldContext)
  · simpa only [List.length_map] using facts.count

end RootB234.PrepExponent.Global
