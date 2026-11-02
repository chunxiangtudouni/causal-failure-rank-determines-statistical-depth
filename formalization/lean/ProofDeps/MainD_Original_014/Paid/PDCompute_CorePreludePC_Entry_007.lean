module

public import Paid.PDCompute_CorePreludePC_Outer_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

/-- A straight literal body has a canonical real trace whose tail is
strictly above its actual initial PC. The PC evidence uses this SAME trace. -/
theorem linear_trace_ordered (program : Program) (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State) (fetch : FetchesCode program before.pc code)
    (run : linearExecute input code before=some after) :
    ∃ states : List State,states.head?=some before ∧ states.getLast?=some after ∧
      states.IsChain (fun first later=>step program input first=some later) ∧
      (∀ state∈states,before.pc≤state.pc) ∧ (∀ state∈states.tail,before.pc<state.pc) := by
  induction code generalizing before with
  | nil =>
    have same : before=after:=by simpa only [linearExecute,Option.some.injEq] using run
    subst after
    refine ⟨[before],rfl,rfl,.singleton before,?_,by simp⟩
    intro state member
    have equal:=List.mem_singleton.mp member
    subst state
    exact Nat.le_refl _
  | cons instruction code ih =>
    obtain ⟨middle,first,later⟩:=Option.bind_eq_some_iff.mp run
    have pc:=execute_pc_succ instruction (straight instruction (by simp)) input before middle first
    have firstFetch : program[before.pc]?=some instruction:=by simpa using fetch 0 (by simp)
    have next : step program input before=some middle:=by simpa [step,firstFetch] using first
    have laterFetch : FetchesCode program middle.pc code:=by
      intro offset inside
      have fetched:=fetch (offset+1) (by simp only [List.length_cons];omega)
      have address : middle.pc+offset=before.pc+(offset+1):=by omega
      rw [address]
      simpa only [List.getElem?_cons_succ] using fetched
    obtain ⟨tail,head,last,chain,lower,_strict⟩:=ih
      (fun opcode member=>straight opcode (by simp only [List.mem_cons];exact Or.inr member))
      middle laterFetch later
    cases tail with
    | nil => cases head
    | cons actual states =>
      have same : actual=middle:=Option.some.inj head
      subst actual
      refine ⟨before::middle::states,rfl,?_,List.isChain_cons_cons.mpr ⟨next,chain⟩,?_,?_⟩
      · simpa only [List.getLast?_cons_cons] using last
      · intro state member
        rcases List.mem_cons.mp member with equal|member
        · subst state;exact Nat.le_refl _
        · have bound:=lower state member
          omega
      · intro state member
        have bound:=lower state member
        omega

theorem entryCount_append (pc : ℕ) (left right : List State) :
    entryCount pc (left++right)=entryCount pc left+entryCount pc right := by
  simp only [entryCount,List.filter_append,List.length_append]

theorem entryCount_absent (pc : ℕ) (states : List State) (absent : ∀ state∈states,state.pc≠pc) :
    entryCount pc states=0 := by
  revert absent
  induction states with
  | nil => intro _absent;rfl
  | cons state states ih =>
    intro absent
    have first:=absent state (by simp)
    have rest:=ih (fun later member=>absent later (by simp only [List.mem_cons];exact Or.inr member))
    simpa [entryCount,first] using rest

theorem entryCount_head (pc : ℕ) (states : List State) (before : State)
    (head : states.head?=some before) (position : before.pc=pc)
    (strict : ∀ state∈states.tail,pc<state.pc) : entryCount pc states=1 := by
  cases states with
  | nil => cases head
  | cons state states =>
    have same : state=before:=Option.some.inj head
    subst state
    have zero:=entryCount_absent pc states (fun state member=>by have bound:=strict state member;omega)
    simpa [entryCount,position] using congrArg (fun count : ℕ=>count+1) zero

def EntrySegment (origin : ℕ) (input : List Cell) (before after : State) : Prop :=
  ∃ states : List State,states.head?=some before ∧ states.getLast?=some after ∧
    states.IsChain (fun first later=>step (locatedBlock origin (kernel origin)) input first=some later) ∧
    (∀ state∈states,origin≤state.pc) ∧ entryCount origin states=1

theorem EntrySegment.append_scoped {origin budget : ℕ} {input : List Cell} {before middle after : State}
    (first : EntrySegment origin input before middle)
    (later : ScopedSegment origin input middle after budget) : EntrySegment origin input before after := by
  obtain ⟨left,lh,ll,lc,lp,count⟩:=first
  obtain ⟨right,rh,rl,rc,_cost,rp⟩:=later
  have middleLow:=rp middle (List.mem_of_head? rh)
  have rightZero:=entryCount_absent origin right (fun state member=>by have bound:=rp state member;omega)
  have split : left.dropLast++[middle]=left:=List.dropLast_append_getLast? middle (by rw [ll];simp)
  have middleZero : entryCount origin [middle]=0:=entryCount_absent origin [middle] (by
    intro state member;have equal:=List.mem_singleton.mp member;subst state;omega)
  have leftCount : entryCount origin left.dropLast=1:=by
    have equal:=congrArg (entryCount origin) split
    rw [entryCount_append,middleZero,Nat.add_zero,count] at equal
    exact equal
  refine ⟨joinTrace left right,joinTrace_head left right before middle lh ll rh,
    joinTrace_last left right after rl,joinTrace_chain _ _ left right middle lc rc ll rh,
    PDCompute.Pack.joinTrace_invariant left right _ lp (fun state member=>(Nat.le_succ origin).trans (rp state member)),?_⟩
  change entryCount origin (left.dropLast++right)=1
  rw [entryCount_append,leftCount,rightZero,Nat.add_zero]

theorem enter_segment (origin : ℕ) (input : List Cell) (base : ℕ) (before : State)
    (position : before.pc=labelAddress origin .enter) (fresh : before.register .fresh=.natural base) :
    EntrySegment origin input before {prologueResult before base with pc:=labelAddress origin .enterBases} := by
  have fetch : FetchesCode (locatedBlock origin (kernel origin)) before.pc (basicBlock .enter).body:=by
    intro offset inside
    rw [position]
    exact kernel_body_fetch origin .enter offset inside
  have run:=prologue_execute input before base fresh
  obtain ⟨body,head,last,chain,lower,strict⟩:=linear_trace_ordered _ input (basicBlock .enter).body
    (basicBlock_straight .enter) before (prologueResult before base) fetch run
  have beforePC : before.pc=origin:=by change before.pc=origin at position;exact position
  have middlePC:=linearExecute_pc input (basicBlock .enter).body (basicBlock_straight .enter) before (prologueResult before base) run
  have controlled : step (locatedBlock origin (kernel origin)) input (prologueResult before base)=
      some {prologueResult before base with pc:=labelAddress origin .enterBases}:=by
    rw [kernel_control_step origin .enter input _ (by rw [middlePC,position])]
    rfl
  have appended:=chain_append_control _ input body (prologueResult before base) _ chain last controlled
  have count:=entryCount_head origin body before head beforePC (by simpa only [beforePC] using strict)
  have targetLow:=label_after_enter origin .enterBases (by decide)
  have nonempty : body≠[]:=by intro empty;rw [empty] at head;cases head
  refine ⟨body++[{prologueResult before base with pc:=labelAddress origin .enterBases}],?_,by simp,appended.1,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil body nonempty] using head
  · intro state member
    rcases List.mem_append.mp member with proper|terminal
    · simpa only [beforePC] using lower state proper
    · have equal:=List.mem_singleton.mp terminal
      subst state
      exact (Nat.le_succ origin).trans targetLow
  · rw [entryCount_append,count]
    have zero : entryCount origin [{prologueResult before base with pc:=labelAddress origin .enterBases}]=0:=
      entryCount_absent origin _ (by
        intro state member;have equal:=List.mem_singleton.mp member;subst state;change labelAddress origin .enterBases≠origin;omega)
    rw [zero,Nat.add_zero]

end PDCompute.CorePreludePC
