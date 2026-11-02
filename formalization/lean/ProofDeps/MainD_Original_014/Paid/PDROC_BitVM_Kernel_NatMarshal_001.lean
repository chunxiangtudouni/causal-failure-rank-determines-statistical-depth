module

public import Paid.PDROC_BitVM_Native_CopyRun_011
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatMarshal

open Turing PDROC.BitVM.Log.TwoStack PDROC.BitVM.Native

abbrev Label := Fin 5
abbrev Store := Option Bool × Unit
abbrev State := TM2.Cfg Alphabet Label Store

def copyLabel (label : PDROC.BitVM.Log.TwoStack.Label) : Label := ⟨label.val+1,by omega⟩

/-- Really read/remove the Nat Cell tag, copy the bare Nat bytes and
restore the source tag. Old destination bytes are retained as a suffix,
allowing right operand first, then left, to build the true two-Nat input. -/
def program (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label=0 then
    .pop 0 (fun store symbol=>(symbol,store.2))
      (.branch (fun store=>store.1==some false)
        (.load (fun _=>(none,())) (.goto (fun _=>1))) .halt)
  else if label=1 then Inline.statement copyLabel 4 (Copy.program 0)
  else if label=2 then Inline.statement copyLabel 4 (Copy.program 1)
  else if label=3 then Inline.statement copyLabel 4 (Copy.program 2)
  else .push 0 (fun _=>false) .halt

def before (word target : List Bool) (store : Option Bool) : State :=
  ⟨some 0,(store,()),threeStacks (false::word) target []⟩

def middle (word target : List Bool) : State := ⟨some 1,(none,()),threeStacks word target []⟩

def returned (word target : List Bool) : State :=
  ⟨some 4,(none,()),threeStacks word (word++target) []⟩

def final (word target : List Bool) : State :=
  ⟨none,(none,()),threeStacks (false::word) (word++target) []⟩

theorem tag_step (word target : List Bool) (store : Option Bool) :
    TM2.step program (before word target store)=some (middle word target) := by
  change (some ⟨some 1,(none,()),Function.update (threeStacks (false::word) target []) 0 word⟩ :
    Option State)=_
  rw [Copy.update_first]
  rfl

theorem restore_step (word target : List Bool) :
    TM2.step program (returned word target)=some (final word target) := by
  change (some ⟨none,(none,()),Function.update (threeStacks word (word++target) []) 0 (false::word)⟩ :
    Option State)=_
  rw [Copy.update_first]
  rfl

theorem copy_agrees : ∀ label,program (copyLabel label)=Inline.statement copyLabel 4 (Copy.program label) := by
  intro label
  fin_cases label <;> rfl

theorem copy_call (word target : List Bool) :
    ∃ run : List State,run.head?=some (middle word target) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (returned word target) ∧ run.length=2*word.length+3 := by
  obtain ⟨oldRun,oldHead,oldChain,oldLast,oldHalt,oldLength,_src,_dst,_tmp⟩ := Copy.copy_runs word target
  obtain ⟨run,after,head,chain,last,atReturn,stackData,storeEq,length⟩ :=
    Inline.actual_return_trace copyLabel 4 Copy.program program copy_agrees oldRun
      (Copy.state (some 0) none word target []) (Copy.state none none word (word++target) []) ()
      oldHead oldChain oldLast oldHalt
  have endpoint : after=returned word target := by
    rcases after with ⟨label,saved,contents⟩
    change label=some 4 at atReturn
    change saved=(none,()) at storeEq
    change contents=threeStacks word (word++target) [] at stackData
    subst label
    subst saved
    subst contents
    rfl
  exact ⟨run,head,chain,last.trans (congrArg some endpoint),length.trans oldLength⟩

/-- ONE genuine path copies only the actual operand bytes, restores the
original Cell, preserves scratch and includes both boundary operations. -/
theorem marshal_runs (word target : List Bool) (store : Option Bool) :
    ∃ run : List State,run.head?=some (before word target store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (final word target) ∧ TM2.step program (final word target)=none ∧
      run.length=2*word.length+5 ∧
      (final word target).stk 0=false::word ∧
      (final word target).stk 1=word++target ∧ (final word target).stk 2=[] := by
  obtain ⟨copyRun,head,chain,last,length⟩ := copy_call word target
  cases copyRun with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=middle word target := Option.some.inj head
    subst start
    have firstChain : (before word target store::middle word target::rest).IsChain
        (fun a b=>TM2.step program a=some b) := List.isChain_cons_cons.mpr ⟨tag_step word target store,chain⟩
    have firstLast : (before word target store::middle word target::rest).getLast?=
        some (returned word target) := by simpa only [List.getLast?_cons_cons] using last
    have finish : (returned word target::[final word target]).IsChain
        (fun a b=>TM2.step program a=some b) :=
      List.isChain_cons_cons.mpr ⟨restore_step word target,List.isChain_singleton _⟩
    refine ⟨(before word target store::middle word target::rest)++[final word target],rfl,
      PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain _ _ _ firstLast firstChain finish,
      List.getLast?_append_cons _ _ [],rfl,?_,rfl,rfl,rfl⟩
    simp only [List.length_append,List.length_cons,List.length_nil] at length ⊢
    omega

theorem official_nat_runs (value : ℕ) (target : List Bool) (store : Option Bool) :
    ∃ run : List State,
      run.head?=some (before (PaperProofs.Paid.Computation.encodeNatBits value) target store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (final (PaperProofs.Paid.Computation.encodeNatBits value) target) ∧
      TM2.step program (final (PaperProofs.Paid.Computation.encodeNatBits value) target)=none ∧
      run.length=2*(PaperProofs.Paid.Computation.encodeNatBits value).length+5 ∧
      (final (PaperProofs.Paid.Computation.encodeNatBits value) target).stk 0=
        PaperProofs.Paid.Computation.encodeCellBits (.natural value) ∧
      (final (PaperProofs.Paid.Computation.encodeNatBits value) target).stk 1=
        PaperProofs.Paid.Computation.encodeNatBits value++target ∧
      (final (PaperProofs.Paid.Computation.encodeNatBits value) target).stk 2=[] :=
  marshal_runs (PaperProofs.Paid.Computation.encodeNatBits value) target store

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · simp [program,TM2.SupportsStmt]
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 0) (Copy.supports.2 0 (Finset.mem_univ _))
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 1) (Copy.supports.2 1 (Finset.mem_univ _))
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 2) (Copy.supports.2 2 (Finset.mem_univ _))
    · trivial

end PDROC.BitVM.Kernel.NatMarshal
