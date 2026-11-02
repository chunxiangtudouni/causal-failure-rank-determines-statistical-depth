module
public import Paid.PDCompute_CorePrelude_Endpoint_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

theorem chain_tail_property {α : Type} (relation : α→α→Prop) (good : α→Prop) :
    ∀ trace : List α,trace.IsChain relation →
      (∀ before∈trace.dropLast,∀ after,relation before after→good after) →
      ∀ state∈trace.tail,good state := by
  intro trace
  induction trace with
  | nil => simp
  | cons first rest ih =>
    intro chain preserved
    cases rest with
    | nil => simp
    | cons next tail =>
      have edges:=List.isChain_cons_cons.mp chain
      have later:=ih edges.2 (by
        intro before member after step
        exact preserved before (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem first member) after step)
      intro state member
      rcases List.mem_cons.mp member with same|inside
      · subst state
        exact preserved first (by simp) next edges.1
      · exact later state inside

theorem entry_count_one (entry : ℕ) (trace : List State) (before : State)
    (head : trace.head?=some before) (position : before.pc=entry)
    (later : ∀ state∈trace.tail,state.pc≠entry) :
    PaperProofs.Paid.Computation.entryCount entry trace=1 := by
  cases trace with
  | nil => cases head
  | cons first rest =>
    have same:=Option.some.inj head
    subst first
    have empty : rest.filter (fun state=>state.pc==entry)=[]:=by
      apply List.filter_eq_nil_iff.mpr
      intro state member
      simpa only [beq_iff_eq] using later state member
    simp only [PaperProofs.Paid.Computation.entryCount,List.filter_cons,position,beq_self_eq_true,ite_true,empty,
      List.length_singleton]

/-- Every executed straight instruction advances PC. The actual chain
therefore visits the entrance exactly at its real head, including the
shared-boundary convention used by joinTrace. -/
theorem straight_trace_entry_count (program : Program) (input : List Cell)
    (origin : ℕ) (code : List Instruction) (trace : List State) (before : State)
    (head : trace.head?=some before) (position : before.pc=origin)
    (chain : trace.IsChain (fun first later=>step program input first=some later))
    (straight : StraightCode code) (fetch : FetchesCode program origin code)
    (scope : ∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+code.length) :
    PaperProofs.Paid.Computation.entryCount origin trace=1 := by
  apply entry_count_one origin trace before head position
  have tailBound:=chain_tail_property (fun first later=>step program input first=some later)
    (fun state=>origin<state.pc) trace chain (by
      intro first member later actual
      have range:=scope first member
      obtain ⟨instruction,fetched,executed⟩:=Option.bind_eq_some_iff.mp actual
      have offset : first.pc-origin<code.length:=by omega
      have addressed : origin+(first.pc-origin)=first.pc:=Nat.add_sub_of_le range.1
      have value : code[first.pc-origin]?=some instruction:=by
        rw [←fetch _ offset,addressed]
        exact fetched
      have memberCode:=List.mem_of_getElem? value
      have nextPC:=execute_pc_succ instruction (straight instruction memberCode) input first later executed
      omega)
  intro state member equal
  have bound:=tailBound state member
  omega

theorem entry_count_join (entry : ℕ) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (outside : middle.pc≠entry) :
    PaperProofs.Paid.Computation.entryCount entry (joinTrace first later)=
      PaperProofs.Paid.Computation.entryCount entry first+PaperProofs.Paid.Computation.entryCount entry later := by
  have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
  have appendCount (left right : List State) :
      PaperProofs.Paid.Computation.entryCount entry (left++right)=
        PaperProofs.Paid.Computation.entryCount entry left+PaperProofs.Paid.Computation.entryCount entry right:=by
    simp only [PaperProofs.Paid.Computation.entryCount,List.filter_append,List.length_append]
  have zero : PaperProofs.Paid.Computation.entryCount entry [middle]=0:=by
    simp [PaperProofs.Paid.Computation.entryCount,outside]
  have earlier:=appendCount first.dropLast [middle]
  rw [split,zero,Nat.add_zero] at earlier
  change PaperProofs.Paid.Computation.entryCount entry (first.dropLast++later)=_
  rw [appendCount,←earlier]

end PDCompute.CorePrelude
