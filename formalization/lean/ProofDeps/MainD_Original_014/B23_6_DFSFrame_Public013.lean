module
public import B23_6_DFSFrame_Push006
public import B23_6_DFSFrame_RankReturn009
public import B23_6_DFSFrame_Link012

/-! Ordinary embeddable raw frame API. Push kind is a fixed finite entry;
pop has one fixed entry and obtains kind from the saved physical frame.
All sixteen stacks, all Bool payloads, and arbitrary old spool tails are
covered. No theorem below asserts a complete original DFS implementation. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame.Public
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

theorem label_count : Fintype.card Label=84 := by decide

theorem push_actual (memory : Store C) (parent : Bank) (kind : Bool) :
    ∃ path,Facts (.pushBoot kind) .pushDone memory parent (pushBank kind parent) path ∧
      clockSum path≤65536*(scale parent)^2 ∧ chargedCost path≤65600*(scale parent)^2 := by
  obtain ⟨n,run,cap⟩:=push_run memory parent kind
  obtain ⟨path,facts,_⟩:=bounded_run (.pushBoot kind) .pushDone memory parent (pushBank kind parent) n run
    (by dsimp only [scale];omega)
  exact ⟨path,facts,clockSum_le facts,chargedCost_le facts⟩

theorem pop_actual (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∃ path,Facts .popBoot (.popDone kind) memory child (restoreBank parent (child 15)) path ∧
      clockSum path≤65536*(scale child)^2 ∧ chargedCost path≤65600*(scale child)^2 := by
  obtain ⟨n,run,cap⟩:=pop_run memory parent child kind flag spool
  obtain ⟨path,facts,_⟩:=bounded_run .popBoot (.popDone kind) memory child (restoreBank parent (child 15)) n run
    (by dsimp only [scale];omega)
  exact ⟨path,facts,clockSum_le facts,chargedCost_le facts⟩

theorem rank_return_actual (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∃ path,Facts .parkClear15 (.popDone kind) memory child (restoreBank parent (child 10)) path ∧
      clockSum path≤65536*(scale child)^2 ∧ chargedCost path≤65600*(scale child)^2 := by
  obtain ⟨n,run,cap⟩:=rank_return_run memory parent child kind flag spool
  obtain ⟨path,facts,_⟩:=bounded_run .parkClear15 (.popDone kind) memory child (restoreBank parent (child 10)) n run
    (by dsimp only [scale];omega)
  exact ⟨path,facts,clockSum_le facts,chargedCost_le facts⟩

theorem saved_fields (parent : Bank) (kind : Bool) (i : Field) :
    pushBank kind parent (field i)=if seed i then parent (field i) else [] := by
  simp only [pushBank,Function.update_of_ne (field_ne13 i),prefixBank,field_ne13,field_ne15,ite_false,
    field_index,i.isLt,true_and,seed_field]
  cases seed i <;> rfl
theorem push_seed (parent : Bank) (kind : Bool) :
    pushBank kind parent 0=parent 0 ∧ pushBank kind parent 1=parent 1 ∧ pushBank kind parent 2=parent 2 ∧
      pushBank kind parent 4=parent 4 ∧ pushBank kind parent 11=parent 11 := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem push_work_empty (parent : Bank) (kind : Bool) :
    pushBank kind parent 3=[] ∧ pushBank kind parent 5=[] ∧ pushBank kind parent 6=[] ∧
      pushBank kind parent 7=[] ∧ pushBank kind parent 8=[] ∧ pushBank kind parent 9=[] ∧
      pushBank kind parent 10=[] ∧ pushBank kind parent 12=[] ∧ pushBank kind parent 14=[] ∧
      pushBank kind parent 15=[] := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def payload (parent : Bank) : Nat → List Bool
  | 0 => []
  | n+1 => code (parent (field (rom n)))++payload parent n
theorem frame_split (parent : Bank) (kind : Bool) (n : Nat) :
    framePrefix parent kind n=payload parent n++kind::parent 13 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [framePrefix,payload,ih,List.append_assoc]
theorem spool_exact (parent : Bank) (kind : Bool) :
    pushBank kind parent 13=false::(payload parent 14++kind::parent 13) ∧
      (pushBank kind parent 13).length=(parent 13).length+2*massPrefix parent 14+30 := by
  constructor
  · change false::framePrefix parent kind 14=_
    rw [frame_split]
  · exact exact_spool parent kind

theorem restore_fields (parent : Bank) (rank : List Bool) (i : Field) :
    restoreBank parent rank (field i)=parent (field i) := Function.update_of_ne (field_ne15 i) _ _
theorem restore_rank (parent : Bank) (rank : List Bool) : restoreBank parent rank 15=rank := rfl
theorem restore_tail (parent : Bank) (rank : List Bool) : restoreBank parent rank 13=parent 13 := rfl
theorem restore_hasBest_tail (parent : Bank) (rank : List Bool) (hasBest : Bool) (oldTail : List Bool)
    (saved : parent 13=hasBest::oldTail) : restoreBank parent rank 13=hasBest::oldTail := saved

/-- This equality is about the finite returned label, selected by reading the
physical kind. Kind is absent from the runtime entry arguments of popBoot. -/
theorem kind_and_whole_memory (memory : Store C) (parent child : Bank) (kind flag : Bool)
    (spool : child 13=flag::framePrefix parent kind 14) :
    ∃ path,Facts .popBoot (.popDone kind) memory child (restoreBank parent (child 15)) path ∧
      path.getLast?=some (state (.popDone kind) (clean memory) (restoreBank parent (child 15))) := by
  obtain ⟨path,facts,_,_⟩:=pop_actual memory parent child kind flag spool
  exact ⟨path,facts,facts.last⟩

/-- Direct caller consumption of the same source path. Caller code at the
three return ports is unrestricted, and remains unexecuted. -/
theorem caller_actual {Ω : Type*} {entry exit : Label} {memory : Store C} {before output : Bank}
    {path : List (State C)} (facts : Facts entry exit memory before output path) (mapping : Label ↪ Ω)
    (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (agrees : ∀ point,Interior point→code (mapping point)=LabelMap.statement mapping (source point)) :
    ∃ linked : List (TM2.Cfg RatInput.Alphabet Ω (Store C)),
      linked=path.map (LabelMap.configuration mapping) ∧
      linked.head?=some (LabelMap.configuration mapping (state entry memory before)) ∧
      linked.getLast?=some (LabelMap.configuration mapping (state exit (clean memory) output)) ∧
      linked.IsChain (fun a b => TM2.step code a=some b) ∧ linked.length=path.length ∧
      callerClockSum code linked=clockSum path ∧
      linked.length+callerClockSum code linked≤65600*(scale before)^2 ∧
      (∀ current∈linked,current.var.1=memory.1 ∧
        (∀ slot,(current.stk slot).length≤155*scale before) ∧ RatInput.occupied current.stk≤2480*scale before) ∧
      (∀ current∈linked.dropLast,current.l≠some (mapping .pushDone) ∧
        current.l≠some (mapping (.popDone true)) ∧ current.l≠some (mapping (.popDone false))) := by
  refine ⟨path.map (LabelMap.configuration mapping),rfl,?_,?_,caller_chain facts mapping code agrees,
    List.length_map _,caller_clock_sum facts mapping code agrees,?_,?_,caller_noearly facts mapping⟩
  · simp only [List.head?_map,facts.first,Option.map_some]
  · simp only [List.getLast?_map,facts.last,Option.map_some]
  · rw [List.length_map,caller_clock_sum facts mapping code agrees]
    exact chargedCost_le facts
  · intro current member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    exact facts.boundaries old present

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (fixed : Label → Statement C) (allowed : Finset Label),fixed=source ∧ TM2.Supports fixed allowed ∧
      Fintype.card (Store C)=4*Fintype.card C ∧
      (∀ (memory : Store C) (parent : Bank) (kind : Bool),
        ∃ path,Facts (.pushBoot kind) .pushDone memory parent (pushBank kind parent) path ∧
          clockSum path≤65536*(scale parent)^2 ∧ chargedCost path≤65600*(scale parent)^2) ∧
      (∀ (memory : Store C) (parent child : Bank) (kind flag : Bool),child 13=flag::framePrefix parent kind 14→
        ∃ path,Facts .popBoot (.popDone kind) memory child (restoreBank parent (child 15)) path ∧
          clockSum path≤65536*(scale child)^2 ∧ chargedCost path≤65600*(scale child)^2) ∧
      (∀ (memory : Store C) (parent child : Bank) (kind flag : Bool),child 13=flag::framePrefix parent kind 14→
        ∃ path,Facts .parkClear15 (.popDone kind) memory child (restoreBank parent (child 10)) path ∧
          clockSum path≤65536*(scale child)^2 ∧ chargedCost path≤65600*(scale child)^2) := by
  exact ⟨source,Finset.univ,rfl,supports .halt .halt .halt,store_card,push_actual,pop_actual,rank_return_actual⟩

/-- A current machine state joins by whole store and whole physical memory. -/
theorem push_from_state (before : State C) (kind : Bool) (active : before.l=some (.pushBoot kind)) :
    ∃ path,Facts (.pushBoot kind) .pushDone before.var before.stk (pushBank kind before.stk) path ∧
      path.head?=some before := by
  obtain ⟨path,facts,_,_⟩:=push_actual before.var before.stk kind
  refine ⟨path,facts,?_⟩
  rw [facts.first]
  congr 1
  cases before with
  | mk position memory contents =>
    change (⟨some (.pushBoot kind),memory,contents⟩ : State C)=⟨position,memory,contents⟩
    change position=some (.pushBoot kind) at active
    rw [active]

end B23_6.DFSFrame.Public
