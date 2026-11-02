module

public import RootB234_PrepEntry_StageArithmeticCode_083

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*}

abbrev bank := Global.bank

theorem store_label_path {σ Λ : Type*} (iso : σ ≃ Store C) (mapping : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ σ) (multiply : Bool) (caller : Statement C)
    (port : Λ) (atPort : old port=.halt) (trace : List (TM2.Cfg RatInput.Alphabet Λ σ))
    (before final : TM2.Cfg RatInput.Alphabet Λ σ)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (last : trace.getLast?=some final) (active : final.l=some port)
    (same : ∀ point,point≠port→program multiply caller (mapping point)=LabelMap.statement mapping (StoreIso.statement iso (old point))) :
    let cfg := fun current => LabelMap.configuration mapping (StoreIso.configuration iso current)
    (trace.map cfg).head?=some (cfg before) ∧
    (trace.map cfg).IsChain (fun a b => TM2.step (program multiply caller) a=some b) ∧
    (trace.map cfg).getLast?=some (cfg final) := by
  let changed := StoreIso.machine iso old
  have stored := StoreIso.actual_path_on iso old changed trace before final first chain last
    (by intro current member point selected;rfl)
  have atPort' : changed port=.halt := by change StoreIso.statement iso (old port)=_;rw [atPort];rfl
  have path := label_path mapping changed multiply caller port atPort' _ _ _ stored.1 stored.2.1 stored.2.2.1 active same
  simp only [List.map_map,Function.comp_def] at path
  exact path

def mulEntry (background : Stack → List Bool) (memory : Store C) (cache exponent : List Bool)
    (x y : Rat) (tail : List Bool) : QLoop.RawState C :=
  let m := QLoop.rawMemory memory
  RatBinary.entry (QLoop.rawBackground background cache exponent) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache

def mulCfg (before : QLoop.RawState C) : State C :=
  LabelMap.configuration binaryLabel (StoreIso.configuration (QLoop.arithmeticIso C)
    (Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C)) before))

theorem mul_entry (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    mulCfg (mulEntry background memory cache exponent x y tail)=
      state (.binary default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []) := by
  have vars : QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
      (mulEntry background memory cache exponent x y tail).var)=memory := by
    change QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C) (QLoop.rawMemory memory))=memory
    simp only [QLoop.rawMemory,Equiv.apply_symm_apply]
  unfold mulCfg LabelMap.configuration StoreIso.configuration Arithmetic.binaryConfiguration StackIso.configuration
  change (⟨some (.binary default),QLoop.arithmeticIso C (Arithmetic.mulIso (PacketUnary.Store C)
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

theorem mul_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    ∃ (afterMemory : Store C) (part : Segment true caller
      (state (.binary default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []))
      (state (.restore (.clear 7)) afterMemory (bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length ≤ RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache exponent) x y tail cache := by
  let m := QLoop.rawMemory memory
  let oldBackground := QLoop.rawBackground background cache exponent
  obtain ⟨run,final,facts,first,chain,last,active,contexts,contents⟩ := Arithmetic.actual_mul
    oldBackground m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache
  let arithmeticCfg := Arithmetic.binaryConfiguration (Arithmetic.mulIso (PacketUnary.Store C))
  let arithmeticFinal := arithmeticCfg final
  have path := store_label_path (QLoop.arithmeticIso C) binaryLabel Arithmetic.mulProgram true caller .done rfl
    (run.map arithmeticCfg) _ arithmeticFinal first chain last active
    (by intro point different;simp only [binaryLabel,different,ite_false,program,binary,ite_true])
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map (mulCfg)).head?=some (mulCfg (mulEntry background memory cache exponent x y tail)) := path.1
  rw [mul_entry] at first'
  let afterMemory := QLoop.arithmeticIso C arithmeticFinal.var
  have finalSlots : arithmeticFinal.stk=bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] [] :=
    contents.trans (binary_final_bank background cache exponent (x*y) tail)
  have lastState : mulCfg final=state (.restore (.clear 7)) afterMemory
      (bank background cache exponent (RatInput.Encoder.packet (x*y) tail) [] [] []) := by
    change (⟨arithmeticFinal.l.map binaryLabel,afterMemory,arithmeticFinal.stk⟩ : State C)=_
    rw [active,finalSlots]
    rfl
  have oldContext : m.1.1.1.1.1.2.1=((QLoop.arithmeticIso C).symm memory).2.1 := by
    rw [←Arithmetic.mul_context (PacketUnary.Store C) m]
    dsimp only [m,QLoop.rawMemory]
    rw [Equiv.apply_symm_apply]
  refine ⟨afterMemory,⟨run.map (mulCfg),first',path.2.1,path.2.2.trans (congrArg some lastState)⟩,?_,?_⟩
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
  LabelMap.configuration binaryLabel (StoreIso.configuration (QLoop.arithmeticIso C)
    (Arithmetic.binaryConfiguration (Arithmetic.subIso (PacketUnary.Store C)) before))

theorem sub_entry (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    subCfg (subEntry background memory cache exponent x y tail)=
      state (.binary default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []) := by
  have vars : QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C)
      (subEntry background memory cache exponent x y tail).var)=memory := by
    change QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C) (subMemory memory))=memory
    simp only [subMemory,Equiv.apply_symm_apply]
  unfold subCfg LabelMap.configuration StoreIso.configuration Arithmetic.binaryConfiguration StackIso.configuration
  change (⟨some (.binary default),QLoop.arithmeticIso C (Arithmetic.subIso (PacketUnary.Store C)
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
    ∃ (afterMemory : Store C) (part : Segment false caller
      (state (.binary default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []))
      (state (.restore (.clear 7)) afterMemory (bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length ≤ RatBinary.time RatAddSub.addSubCoefficient (QLoop.rawBackground background cache exponent) x y tail cache := by
  let m := subMemory memory
  let oldBackground := QLoop.rawBackground background cache exponent
  obtain ⟨run,final,facts,first,chain,last,active,contexts,contents⟩ := Arithmetic.actual_sub
    oldBackground m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
    m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail cache
  let arithmeticCfg := Arithmetic.binaryConfiguration (Arithmetic.subIso (PacketUnary.Store C))
  let arithmeticFinal := arithmeticCfg final
  have path := store_label_path (QLoop.arithmeticIso C) binaryLabel Arithmetic.subProgram false caller .done rfl
    (run.map arithmeticCfg) _ arithmeticFinal first chain last active
    (by intro point different;simp only [binaryLabel,different,ite_false,program,binary,Bool.false_eq_true,ite_false])
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map subCfg).head?=some (subCfg (subEntry background memory cache exponent x y tail)) := path.1
  rw [sub_entry] at first'
  let afterMemory := QLoop.arithmeticIso C arithmeticFinal.var
  have finalSlots : arithmeticFinal.stk=bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] [] :=
    contents.trans (binary_final_bank background cache exponent (x-y) tail)
  have lastState : subCfg final=state (.restore (.clear 7)) afterMemory
      (bank background cache exponent (RatInput.Encoder.packet (x-y) tail) [] [] []) := by
    change (⟨arithmeticFinal.l.map binaryLabel,afterMemory,arithmeticFinal.stk⟩ : State C)=_
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



def binaryTime (multiply : Bool) (background : Bank) (cache exponent : List Bool)
    (x y : Rat) (tail : List Bool) : Nat :=
  if multiply then RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache exponent) x y tail cache
  else RatBinary.time RatAddSub.addSubCoefficient (QLoop.rawBackground background cache exponent) x y tail cache

theorem binary_actual (multiply : Bool) (caller : Statement C) (background : Bank) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) (tail : List Bool) :
    ∃ (afterMemory : Store C) (part : Segment multiply caller
      (state (.binary default) memory (bank background cache exponent (RatPair.input x y tail) [] [] []))
      (state (.restore (.clear 7)) afterMemory (bank background cache exponent
        (RatInput.Encoder.packet (result multiply x y) tail) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length≤binaryTime multiply background cache exponent x y tail := by
  cases multiply with
  | false => exact sub_actual caller background memory cache exponent x y tail
  | true => exact mul_actual caller background memory cache exponent x y tail

theorem stash_actual (multiply : Bool) (caller : Statement C) (memory : Store C) (before : Bank) :
    ∃ part : Segment multiply caller (state default memory before)
      (state (.binary default) (memory.1,false,false) (StageStash.stashBank before 8)),
      part.trace.length≤32*StageStash.scale before := by
  obtain ⟨run,facts,_clock,_charge⟩:=StageStash.Public.stash_actual memory before
  have path:=label_path stashLabel StageStash.source multiply caller .saved rfl run _ _
    facts.first facts.chain facts.last rfl
    (by intro point different;simp only [stashLabel,different,ite_false,program])
  exact ⟨⟨run.map (LabelMap.configuration stashLabel),path.1,path.2.1,path.2.2⟩,
    by simpa only [List.length_map] using facts.time⟩

theorem restore_actual (multiply : Bool) (caller : Statement C) (memory : Store C)
    (parent before : Bank) (spooled : before 0=StageStash.spool parent 8) :
    ∃ (afterMemory : Store C) (part : Segment multiply caller
      (state (.restore (.clear 7)) memory before)
      (state .done afterMemory (StageStash.restoreBank parent before 0))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length≤32*StageStash.scale before := by
  obtain ⟨run,current,facts,_clock,_charge⟩:=StageStash.Public.restore_actual memory parent before spooled
  have path:=label_path restoreLabel StageStash.source multiply caller .restored rfl run _ _
    facts.first facts.chain facts.last rfl
    (by intro point different;simp only [restoreLabel,different,ite_false,program])
  have held:=(facts.boundaries (StageStash.state .restored current (StageStash.restoreBank parent before 0))
    (List.mem_of_getLast? facts.last)).1
  change current.1=memory.1 at held
  refine ⟨current,⟨run.map (LabelMap.configuration restoreLabel),path.1,path.2.1,path.2.2⟩,?_,?_⟩
  · exact congrArg (fun value : Core C => value.1.1.2) held
  · simpa only [List.length_map] using facts.time

def actualCost (multiply : Bool) (before : Bank) (x y : Rat) (tail : List Bool) : Nat :=
  32*StageStash.scale before+
    binaryTime multiply (StageStash.stashBank before 8) (before 7) (before 11) x y tail+
    32*StageStash.scale (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail))

/-- The actual source keeps every old bank at exit except its new result15.
The eight stage fields are not assumed empty: they are paid stashed and restored.
Only physical4 is an internal parent-derived temporary. -/
theorem actual (multiply : Bool) (caller : Statement C) (memory : Store C) (before : Bank)
    (x y : Rat) (tail : List Bool) (source : before 15=RatPair.input x y tail) (temporary : before 4=[]) :
    ∃ (afterMemory : Store C) (part : Segment multiply caller (state default memory before)
      (state .done afterMemory (output before (RatInput.Encoder.packet (result multiply x y) tail)))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧
      part.trace.length≤actualCost multiply before x y tail := by
  obtain ⟨saved,saveCount⟩:=stash_actual multiply caller memory before
  obtain ⟨arithMemory,calculation,arithContext,arithCount⟩:=binary_actual multiply caller
    (StageStash.stashBank before 8) (memory.1,false,false) (before 7) (before 11) x y tail
  let binaryPart : Segment multiply caller
      (state (.binary default) (memory.1,false,false) (StageStash.stashBank before 8))
      (state (.restore (.clear 7)) arithMemory
        (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail))) :=
    ⟨calculation.trace,
      calculation.first.trans (congrArg some (congrArg (state (.binary default) (memory.1,false,false)) (stash_bank before x y tail source temporary))),
      calculation.chain,
      calculation.last.trans (congrArg some (congrArg (state (.restore (.clear 7)) arithMemory) (result_bank before (result multiply x y) tail temporary)))⟩
  have spooled : output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail) 0=
      StageStash.spool before 8 := rfl
  obtain ⟨afterMemory,restored,restoreContext,restoreCount⟩:=restore_actual multiply caller arithMemory before _ spooled
  let finalPart : Segment multiply caller
      (state (.restore (.clear 7)) arithMemory
        (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail)))
      (state .done afterMemory (output before (RatInput.Encoder.packet (result multiply x y) tail))) :=
    ⟨restored.trace,restored.first,restored.chain,
      restored.last.trans (congrArg some (congrArg (state .done afterMemory) (restored_bank before _)))⟩
  let front:=saved.append binaryPart
  let whole:=front.append finalPart
  refine ⟨afterMemory,whole,restoreContext.trans arithContext,?_⟩
  have bCount : binaryPart.trace.length≤binaryTime multiply (StageStash.stashBank before 8)
      (before 7) (before 11) x y tail := arithCount
  have rCount : finalPart.trace.length≤32*StageStash.scale
      (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail)) := restoreCount
  have c1 : front.trace.length≤saved.trace.length+binaryPart.trace.length := saved.append_length binaryPart
  have c2 : whole.trace.length≤front.trace.length+finalPart.trace.length := front.append_length finalPart
  unfold actualCost
  omega

end RootB234.PrepEntry.StageArithmetic
