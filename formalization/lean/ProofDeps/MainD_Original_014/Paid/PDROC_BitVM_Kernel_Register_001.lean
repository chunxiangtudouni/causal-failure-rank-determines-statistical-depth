module

public import Paid.PDROC_BitVM_Native_CopyRun_011
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.RegisterMove

open Turing PDROC.BitVM.Log.TwoStack
open PDROC.BitVM.Native

abbrev Label := Fin 5
abbrev Store := Option Bool × Unit
abbrev State := TM2.Cfg Alphabet Label Store

/- First really discard the old destination, then reuse the checked copy.
Source/target/scratch are fixed slots0/1/2. Caller embedding handles the
seven register choices; same-register move is a separate finite case. -/
def clearSource (_ : Unit) : TM2.Stmt Alphabet Unit (Option Bool) :=
  .pop 1 (fun _ symbol=>symbol)
    (.branch Option.isSome (.goto (fun _=>())) .halt)

def clearState (label : Option Unit) (store : Option Bool) (source target : List Bool) :
    TM2.Cfg Alphabet Unit (Option Bool) := ⟨label,store,threeStacks source target []⟩

theorem clear_cons (source target : List Bool) (bit : Bool) (store : Option Bool) :
    TM2.step clearSource (clearState (some ()) store source (bit::target))=
      some (clearState (some ()) (some bit) source target) := by
  change (some ⟨some (),some bit,Function.update (threeStacks source (bit::target) []) 1 target⟩ :
    Option (TM2.Cfg Alphabet Unit (Option Bool)))=_
  rw [Copy.update_second]
  rfl

theorem clear_nil (source : List Bool) (store : Option Bool) :
    TM2.step clearSource (clearState (some ()) store source [])=
      some (clearState none none source []) := by
  change (some ⟨none,none,Function.update (threeStacks source [] []) 1 []⟩ :
    Option (TM2.Cfg Alphabet Unit (Option Bool)))=_
  rw [Copy.update_second]
  rfl

def clearTrace (source : List Bool) : List Bool → Option Bool → List (TM2.Cfg Alphabet Unit (Option Bool))
  | [],store => [clearState (some ()) store source [],clearState none none source []]
  | bit::target,store => clearState (some ()) store source (bit::target)::clearTrace source target (some bit)

theorem clear_head (source target : List Bool) (store : Option Bool) :
    (clearTrace source target store).head?=some (clearState (some ()) store source target) := by
  cases target <;> rfl

theorem clear_last (source target : List Bool) (store : Option Bool) :
    (clearTrace source target store).getLast?=some (clearState none none source []) := by
  induction target generalizing store with
  | nil => rfl
  | cons bit target ih =>
    rw [clearTrace,List.getLast?_cons,ih]
    rfl

theorem clear_length (source target : List Bool) (store : Option Bool) :
    (clearTrace source target store).length=target.length+2 := by
  induction target generalizing store with
  | nil => rfl
  | cons bit target ih => simp only [clearTrace,List.length_cons,ih]

theorem clear_chain (source target : List Bool) (store : Option Bool) :
    (clearTrace source target store).IsChain (fun a b=>TM2.step clearSource a=some b) := by
  induction target generalizing store with
  | nil => exact List.isChain_cons_cons.mpr ⟨clear_nil source store,List.isChain_singleton _⟩
  | cons bit target ih =>
    apply List.IsChain.cons (ih (some bit))
    intro after member
    rw [clear_head] at member
    have same : after=clearState (some ()) (some bit) source target :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact clear_cons source target bit store

def copyLabel (label : PDROC.BitVM.Log.TwoStack.Label) : Label := ⟨label.val+1,by omega⟩

/-- Literal clear, checked copy and true HALT. All five labels and both
finite store components are fixed before the runtime Cell words. -/
def program (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label=0 then Inline.statement (fun _ : Unit=>(0 : Label)) 1 (clearSource ())
  else if label=1 then Inline.statement copyLabel 4 (Copy.program 0)
  else if label=2 then Inline.statement copyLabel 4 (Copy.program 1)
  else if label=3 then Inline.statement copyLabel 4 (Copy.program 2)
  else .halt

def before (source target : List Bool) (store : Option Bool) : State :=
  ⟨some 0,(store,()),threeStacks source target []⟩

def middle (source : List Bool) : State := ⟨some 1,(none,()),threeStacks source [] []⟩

def returned (source : List Bool) : State := ⟨some 4,(none,()),threeStacks source source []⟩

def final (source : List Bool) : State := ⟨none,(none,()),threeStacks source source []⟩

theorem clear_agrees : ∀ label : Unit,program ((fun _ : Unit=>(0 : Label)) label)=
    Inline.statement (fun _ : Unit=>(0 : Label)) 1 (clearSource label) := by
  intro label
  cases label
  rfl

theorem copy_agrees : ∀ label,program (copyLabel label)=Inline.statement copyLabel 4 (Copy.program label) := by
  intro label
  fin_cases label <;> rfl

theorem clear_call (source target : List Bool) (store : Option Bool) :
    ∃ run : List State,run.head?=some (before source target store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some (middle source) ∧
      run.length=target.length+2 := by
  obtain ⟨run,after,head,chain,last,atReturn,stackData,storeEq,length⟩ :=
    Inline.actual_return_trace (fun _ : Unit=>(0 : Label)) 1 clearSource program clear_agrees
      (clearTrace source target store) (clearState (some ()) store source target)
      (clearState none none source []) () (clear_head source target store)
      (clear_chain source target store) (clear_last source target store) rfl
  have endpoint : after=middle source := by
    rcases after with ⟨label,saved,contents⟩
    change label=some 1 at atReturn
    change saved=(none,()) at storeEq
    change contents=threeStacks source [] [] at stackData
    subst label
    subst saved
    subst contents
    rfl
  refine ⟨run,head,chain,?_,?_⟩
  · exact last.trans (congrArg some endpoint)
  · exact length.trans (clear_length source target store)

theorem copy_call (source : List Bool) :
    ∃ run : List State,run.head?=some (middle source) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some (returned source) ∧
      run.length=2*source.length+3 := by
  obtain ⟨localRun,localHead,localChain,localLast,localHalt,localLength,_src,_dst,_tmp⟩ := Copy.copy_runs source []
  obtain ⟨run,after,head,chain,last,atReturn,stackData,storeEq,length⟩ :=
    Inline.actual_return_trace copyLabel 4 Copy.program program copy_agrees
      localRun (Copy.state (some 0) none source [] [])
      (Copy.state none none source (source++[]) []) () localHead localChain localLast localHalt
  have endpoint : after=returned source := by
    rcases after with ⟨label,saved,contents⟩
    change label=some 4 at atReturn
    change saved=(none,()) at storeEq
    change contents=threeStacks source (source++[]) [] at stackData
    simp only [List.append_nil] at stackData
    subst label
    subst saved
    subst contents
    rfl
  refine ⟨run,head,chain,?_,length.trans localLength⟩
  exact last.trans (congrArg some endpoint)

/-- Actual replacement of an old destination by an exact copy, preserving
source and restoring scratch. Clearing old FALSE cells is charged too. -/
theorem move_word_runs (source target : List Bool) (store : Option Bool) :
    ∃ run : List State,run.head?=some (before source target store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some (final source) ∧
      TM2.step program (final source)=none ∧
      run.length=target.length+2*source.length+5 ∧
      (final source).stk 0=source ∧ (final source).stk 1=source ∧ (final source).stk 2=[] := by
  obtain ⟨clearRun,clearHead,clearChain,clearLast,clearLength⟩ := clear_call source target store
  obtain ⟨copyRun,copyHead,copyChain,copyLast,copyLength⟩ := copy_call source
  let joined := clearRun++copyRun.tail
  have joinedChain : joined.IsChain (fun a b=>TM2.step program a=some b) :=
    join_chain clearRun copyRun (middle source) clearChain copyChain clearLast copyHead
  have joinedHead : joined.head?=some (before source target store) := by
    simp only [joined,List.head?_append,clearHead,Option.some_or]
  have notOne : copyRun.length≠1 := by omega
  have joinedLast : joined.getLast?=some (returned source) := by
    simp only [joined,List.getLast?_append,List.getLast?_tail,notOne,↓reduceIte,copyLast,Option.some_or]
  have haltPair : (returned source::[final source]).IsChain (fun a b=>TM2.step program a=some b) :=
    List.isChain_cons_cons.mpr ⟨rfl,List.isChain_singleton _⟩
  refine ⟨joined++[final source],?_,?_,List.getLast?_append_cons _ _ [],rfl,?_,rfl,rfl,rfl⟩
  · simp only [List.head?_append,joinedHead,Option.some_or]
  · exact PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain _ _ _ joinedLast joinedChain haltPair
  · simp only [joined,List.length_append,List.length_tail,List.length_cons,List.length_nil,
      clearLength,copyLength]
    omega

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  have clearClosed : TM2.Supports clearSource (Finset.univ : Finset Unit) := by
    constructor
    · exact Finset.mem_univ _
    · intro label _
      cases label
      simp [clearSource,TM2.SupportsStmt]
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · exact Inline.supports_statement (fun _ : Unit=>(0 : Label)) 1 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (clearSource ())
        (clearClosed.2 () (Finset.mem_univ _))
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 0) (Copy.supports.2 0 (Finset.mem_univ _))
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 1) (Copy.supports.2 1 (Finset.mem_univ _))
    · exact Inline.supports_statement copyLabel 4 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Copy.program 2) (Copy.supports.2 2 (Finset.mem_univ _))
    · trivial

/-- The same selected move path agrees with the original RAM instruction.
The mathematical RAM state is proof data, never a runtime control store. -/
theorem cell_move_runs (input : List PaperProofs.Paid.Computation.Cell)
    (logical : PaperProofs.Paid.Computation.State)
    (target source : PaperProofs.Paid.Computation.Register) (store : Option Bool) :
    ∃ (after : PaperProofs.Paid.Computation.State) (run : List State),
      PaperProofs.Paid.Computation.Instruction.execute input (.move target source) logical=some after ∧
      run.head?=some (before (PaperProofs.Paid.Computation.encodeCellBits (logical.register source))
        (PaperProofs.Paid.Computation.encodeCellBits (logical.register target)) store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (final (PaperProofs.Paid.Computation.encodeCellBits (after.register target))) ∧
      TM2.step program (final (PaperProofs.Paid.Computation.encodeCellBits (after.register target)))=none ∧
      run.length=(PaperProofs.Paid.Computation.encodeCellBits (logical.register target)).length+
        2*(PaperProofs.Paid.Computation.encodeCellBits (logical.register source)).length+5 ∧
      after.pc=logical.pc+1 ∧ after.register target=logical.register source := by
  let after := ({logical with pc:=logical.pc+1}).set target (logical.register source)
  have value : after.register target=logical.register source := Function.update_self _ _ _
  obtain ⟨run,head,chain,last,halt,length,_source,_target,_scratch⟩ := move_word_runs
    (PaperProofs.Paid.Computation.encodeCellBits (logical.register source))
    (PaperProofs.Paid.Computation.encodeCellBits (logical.register target)) store
  refine ⟨after,run,rfl,head,chain,?_,?_,length,rfl,value⟩
  · simpa only [value] using last
  · simpa only [value] using halt

/- Fixed source-program constants, including the seven initial Nat0
register values, are physically written. The literal is chosen when code
is built before input; its bytes are not runtime Nat/Rat host variables. -/
def literalCode (bits : List Bool) (tail : TM2.Stmt Alphabet Unit (Option Bool)) :
    TM2.Stmt Alphabet Unit (Option Bool) :=
  bits.foldr (fun bit code=>.push 1 (fun _=>bit) code) tail

theorem literal_stepAux (bits source target : List Bool)
    (tail : TM2.Stmt Alphabet Unit (Option Bool)) (store : Option Bool) :
    TM2.stepAux (literalCode bits tail) store (threeStacks source target [])=
      TM2.stepAux tail store (threeStacks source (bits.reverse++target) []) := by
  induction bits generalizing target with
  | nil => rfl
  | cons bit bits ih =>
    change TM2.stepAux (literalCode bits tail) store
      (Function.update (threeStacks source target []) 1 (bit::target))=_
    rw [Copy.update_second,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

def literalProgram (literal : List Bool) (_ : Unit) : TM2.Stmt Alphabet Unit (Option Bool) :=
  .pop 1 (fun _ symbol=>symbol)
    (.branch Option.isSome (.goto (fun _=>())) (literalCode literal.reverse .halt))

theorem literal_cons (literal source target : List Bool) (bit : Bool) (store : Option Bool) :
    TM2.step (literalProgram literal) (clearState (some ()) store source (bit::target))=
      some (clearState (some ()) (some bit) source target) := by
  change (some ⟨some (),some bit,Function.update (threeStacks source (bit::target) []) 1 target⟩ :
    Option (TM2.Cfg Alphabet Unit (Option Bool)))=_
  rw [Copy.update_second]
  rfl

theorem literal_nil (literal source : List Bool) (store : Option Bool) :
    TM2.step (literalProgram literal) (clearState (some ()) store source [])=
      some (clearState none none source literal) := by
  change some (TM2.stepAux (literalCode literal.reverse .halt) none
    (Function.update (threeStacks source [] []) 1 []))=_
  rw [Copy.update_second,literal_stepAux]
  simp only [List.reverse_reverse,List.append_nil]
  rfl

def literalTrace (literal source : List Bool) :
    List Bool → Option Bool → List (TM2.Cfg Alphabet Unit (Option Bool))
  | [],store => [clearState (some ()) store source [],clearState none none source literal]
  | bit::target,store => clearState (some ()) store source (bit::target)::
      literalTrace literal source target (some bit)

theorem literal_head (literal source target : List Bool) (store : Option Bool) :
    (literalTrace literal source target store).head?=some (clearState (some ()) store source target) := by
  cases target <;> rfl

theorem literal_last (literal source target : List Bool) (store : Option Bool) :
    (literalTrace literal source target store).getLast?=some (clearState none none source literal) := by
  induction target generalizing store with
  | nil => rfl
  | cons bit target ih =>
    rw [literalTrace,List.getLast?_cons,ih]
    rfl

theorem literal_length (literal source target : List Bool) (store : Option Bool) :
    (literalTrace literal source target store).length=target.length+2 := by
  induction target generalizing store with
  | nil => rfl
  | cons bit target ih => simp only [literalTrace,List.length_cons,ih]

theorem literal_chain (literal source target : List Bool) (store : Option Bool) :
    (literalTrace literal source target store).IsChain
      (fun a b=>TM2.step (literalProgram literal) a=some b) := by
  induction target generalizing store with
  | nil => exact List.isChain_cons_cons.mpr ⟨literal_nil literal source store,List.isChain_singleton _⟩
  | cons bit target ih =>
    apply List.IsChain.cons (ih (some bit))
    intro after member
    rw [literal_head] at member
    have same : after=clearState (some ()) (some bit) source target :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact literal_cons literal source target bit store

theorem literal_supports (literal : List Bool) :
    TM2.Supports (literalProgram literal) (Finset.univ : Finset Unit) := by
  have supported (bits : List Bool) : TM2.SupportsStmt (Finset.univ : Finset Unit)
      (literalCode bits (.halt : TM2.Stmt Alphabet Unit (Option Bool))) := by
    induction bits with
    | nil => trivial
    | cons bit bits ih => exact ih
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    exact ⟨fun _=>Finset.mem_univ _,supported literal.reverse⟩

/-- True target clear and literal initialization, including actual HALT.
Source and scratch are unchanged, while false bits are physically present. -/
theorem literal_runs (literal source target : List Bool) (store : Option Bool) :
    ∃ run : List (TM2.Cfg Alphabet Unit (Option Bool)),
      run.head?=some (clearState (some ()) store source target) ∧
      run.IsChain (fun a b=>TM2.step (literalProgram literal) a=some b) ∧
      run.getLast?=some (clearState none none source literal) ∧
      TM2.step (literalProgram literal) (clearState none none source literal)=none ∧
      run.length=target.length+2 ∧
      (clearState none none source literal).stk 0=source ∧
      (clearState none none source literal).stk 1=literal ∧
      (clearState none none source literal).stk 2=[] :=
  ⟨literalTrace literal source target store,literal_head literal source target store,
    literal_chain literal source target store,literal_last literal source target store,rfl,
    literal_length literal source target store,rfl,rfl,rfl⟩

end PDROC.BitVM.Kernel.RegisterMove
