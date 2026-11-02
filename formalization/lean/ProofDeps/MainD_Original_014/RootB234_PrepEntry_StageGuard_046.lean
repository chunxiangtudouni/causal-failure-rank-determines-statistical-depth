module

public import RootB234_PrepEntry_FirstRawWirePublic_044

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageGuard

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

abbrev Store (C : Type*) := C × Bool
abbrev Label := Fin 3
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def capture (memory : Store C) (value : Option Bool) : Store C := (memory.1,value.getD false)

/-- Read the actual most significant bit of the canonical original N
archive, restoring both physically popped marker cells. This source is
not a zero test for an untrimmed Round counter. Both exits stay ACTIVE. -/
def program (zero positive : Statement C) (point : Label) : Statement C :=
  if point=0 then .pop 1 (fun memory _ => memory) (.pop 1 (fun memory _ => memory)
    (.peek 1 capture (.push 1 (fun _ => true) (.push 1 (fun _ => false)
      (.goto (fun memory => if memory.2 then 2 else 1))))))
  else if point=1 then zero else positive

theorem highBit (number : Nat) : number.testBit (natBits number-1)=decide (number≠0) := by
  simp only [natBits,Nat.add_sub_cancel]
  by_cases zero : number=0
  · subst number; rfl
  · rw [Nat.testBit_log2 zero]
    simp [zero]

theorem payload_reverse (number : Nat) :
    ∃ later,(PSTRTMNatValue017.rawPayload number).reverse=decide (number≠0)::later := by
  have nonempty:=PSTRSymbolicLaneArchive.rawPayload_nonempty number
  have highest : (PSTRTMNatValue017.rawPayload number).getLast nonempty=decide (number≠0) := by
    have nonemptyFn : (List.ofFn (fun i : Fin (natBits number) => number.testBit i.val))≠[] := nonempty
    have standard : (List.ofFn (fun i : Fin (natBits number) => number.testBit i.val)).getLast nonemptyFn=
        decide (number≠0) := by
      rw [List.getLast_ofFn]
      exact highBit number
    exact standard
  cases shape : (PSTRTMNatValue017.rawPayload number).reverse with
  | nil =>
    have original:=congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at original
    exact False.elim (nonempty original)
  | cons bit later =>
    have nonemptyReverse : (PSTRTMNatValue017.rawPayload number).reverse≠[] := by rw [shape]; simp
    have head:=List.head_reverse nonemptyReverse
    have selected : bit=(PSTRTMNatValue017.rawPayload number).getLast nonempty := by
      simpa only [shape,List.head_cons] using head
    refine ⟨later,?_⟩
    rw [selected,highest]

theorem physical_header (bank : RatInput.Stack → List Bool) (count number : Nat)
    (whole : ListBlank.mk (bank 1)=ListBlank.mk (fieldLeft [] count number)) :
    ∃ tail,bank 1=false::true::decide (number≠0)::tail := by
  obtain ⟨tail,physical⟩:=Header.finite_archive count number bank whole
  obtain ⟨later,digits⟩:=payload_reverse number
  rw [digits] at physical
  refine ⟨PSTRTMRawNat010.leftBlocks later++false::tail,?_⟩
  exact physical

def before (context : C) (flag : Bool) (bank : RatInput.Stack → List Bool) : State C := ⟨some 0,(context,flag),bank⟩
def final (context : C) (bank : RatInput.Stack → List Bool) (number : Nat) : State C :=
  ⟨some (if number=0 then 1 else 2),(context,decide (number≠0)),bank⟩
def actualTrace (context : C) (flag : Bool) (bank : RatInput.Stack → List Bool) (number : Nat) : List (State C) :=
  [before context flag bank,final context bank number]

theorem actual_step (zero positive : Statement C) (context : C) (flag : Bool)
    (bank : RatInput.Stack → List Bool) (number : Nat)
    (physical : ∃ tail,bank 1=false::true::decide (number≠0)::tail) :
    TM2.step (program zero positive) (before context flag bank)=some (final context bank number) := by
  obtain ⟨tail,shape⟩:=physical
  change some (TM2.stepAux (program zero positive 0) (context,flag) bank)=_
  simp only [program,ite_true,TM2.stepAux,Function.update_self,shape,List.head?_cons,List.tail_cons,Option.getD_some,capture]
  by_cases empty : number=0
  · subst number
    dsimp only [final]
    congr 1
    congr 1
    funext slot
    fin_cases slot <;> simp_all
  · have nonzero : decide (number≠0)=true := by simp [empty]
    rw [nonzero]
    simp only [final,empty,ite_false,nonzero]
    congr 1
    congr 1
    funext slot
    fin_cases slot <;> simp_all

theorem actual (zero positive : Statement C) (context : C) (flag : Bool)
    (bank : RatInput.Stack → List Bool) (number : Nat)
    (physical : ∃ tail,bank 1=false::true::decide (number≠0)::tail) :
    (actualTrace context flag bank number).head?=some (before context flag bank) ∧
    (actualTrace context flag bank number).IsChain (fun a b => TM2.step (program zero positive) a=some b) ∧
    (actualTrace context flag bank number).getLast?=some (final context bank number) ∧
    (actualTrace context flag bank number).length=2 ∧
    (final context bank number).stk=bank ∧ (final context bank number).var.1=context ∧
    (final context bank number).var.2=decide (number≠0) :=
  ⟨rfl,List.isChain_cons_cons.mpr ⟨actual_step zero positive context flag bank number physical,
    List.isChain_singleton _⟩,rfl,rfl,rfl,rfl,rfl⟩

def Work (slot : RatInput.Stack) : Prop := slot=1
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses : Frame.AccessesOnly Work (program (C := C) .halt .halt 0) := of_decide_eq_true rfl
theorem program_actions : ScannerClock.actions (program (C := C) .halt .halt 0)≤5 := of_decide_eq_true rfl
theorem program_pushes : AuxWorkspace.pushes (program (C := C) .halt .halt 0)≤2 := of_decide_eq_true rfl

theorem program_readonly : RawGetter.Readonly (Prod.fst (α := C) (β := Bool)) (program .halt .halt 0) := by
  dsimp [RawGetter.Readonly,program,capture]
  repeat' constructor
  all_goals (intros; rfl)

theorem actual_internal (context : C) (flag : Bool) (bank : RatInput.Stack → List Bool) :
    (∀ node∈AuxWorkspace.nodes (program .halt .halt 0) (context,flag) bank,
      node.1.1=context ∧
      (∀ slot,(node.2 slot).length≤RatInput.occupied bank+2) ∧
      RatInput.occupied node.2≤16*(RatInput.occupied bank+2) ∧
      ∀ slot,slot≠1→node.2 slot=bank slot) ∧
    ScannerStatement.clock (program .halt .halt 0) (context,flag) bank≤10*(RatInput.occupied bank+3) := by
  have initialBound:=RatInput.Encoder.point_mass bank
  refine ⟨?_,?_⟩
  · intro node inside
    have bounded : ∀ slot,(node.2 slot).length≤RatInput.occupied bank+2 := by
      intro slot
      exact (AuxWorkspace.node_bound _ _ _ _ initialBound node inside slot).trans
        (Nat.add_le_add_left program_pushes _)
    refine ⟨RawGetter.nodes_readonly Prod.fst _ program_readonly _ _ node inside,bounded,
      RatInput.Encoder.occupied_bound node.2 _ bounded,?_⟩
    intro slot untouched
    have writes : StackIso.WritesOnly Work (program (C := C) .halt .halt 0) := by
      dsimp [StackIso.WritesOnly,program,Work]
      repeat' constructor
    exact StackIso.nodes_frame _ _ writes _ _ slot untouched node inside
  · exact (ScannerClock.clock_bound (program .halt .halt 0) (context,flag) bank _ initialBound).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 program_actions)
        (Nat.add_le_add_right (Nat.add_le_add_left program_pushes _) 1))

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end RootB234.PrepEntry.StageGuard
