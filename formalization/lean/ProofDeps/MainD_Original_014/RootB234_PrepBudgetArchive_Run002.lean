module

public import RootB234_PrepBudgetArchive_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepBudgetArchive

open Turing
variable {C : Type*}

def numTrace (background : Stack → List Bool) (context : C) :
    Bool → Bool → Bool → List Bool → Bool → Bool → List Bool → List Bool → List (State C)
  | bit,flag,pending,[],negative,boundary,left,target =>
      [state background 3 context bit flag pending (negative::false::boundary::true::left) target,
       state background 3 context negative false negative (boundary::true::left) (true::pending::target),
       state background 4 context boundary true negative (boundary::true::left)
         (true::negative::true::pending::target)]
  | bit,flag,pending,digit::later,negative,boundary,left,target =>
      state background 3 context bit flag pending
        (digit::false::(backCells later ++ negative::false::boundary::true::left)) target ::
      numTrace background context digit false digit later negative boundary left (true::pending::target)

theorem num_head (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (numTrace background context bit flag pending older negative boundary left target).head? =
      some (state background 3 context bit flag pending
        (backCells older ++ negative::false::boundary::true::left) target) := by
  cases older <;> rfl

theorem num_nonempty (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    numTrace background context bit flag pending older negative boundary left target ≠ [] := by
  intro empty
  have first := num_head background context bit flag pending older negative boundary left target
  rw [empty] at first
  cases first

theorem num_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (numTrace background context bit flag pending older negative boundary left target).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction older generalizing bit flag pending target with
  | nil =>
      exact List.isChain_cons_cons.mpr ⟨step_num_later caller background context bit flag pending negative _ _,
        List.isChain_cons_cons.mpr ⟨step_boundary caller background context negative false negative boundary _ _,by simp⟩⟩
  | cons digit later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_,ih _ _ _ _⟩
      intro next first
      rw [num_head] at first
      have same := (Option.mem_some_iff.mp first).symm
      subst next
      exact step_num_later caller background context bit flag pending digit _ _

theorem num_last (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (numTrace background context bit flag pending older negative boundary left target).getLast? =
      some (state background 4 context boundary true negative (boundary::true::left)
        (true::negative::(frontCells older.reverse ++ true::pending::target))) := by
  induction older generalizing bit flag pending target with
  | nil => rfl
  | cons digit later ih =>
      rw [numTrace,List.getLast?_cons_of_ne_nil (num_nonempty _ _ _ _ _ _ _ _ _ _),ih]
      simp only [List.reverse_cons,frontCells,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem num_length (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (numTrace background context bit flag pending older negative boundary left target).length = older.length+3 := by
  induction older generalizing bit flag pending target with
  | nil => rfl
  | cons digit later ih => simp only [numTrace,List.length_cons,ih]

def denSource (later : List Bool) (first near negative boundary : Bool) (older left : List Bool) : List Bool :=
  backCells later ++ first::true::(backCells (near::older) ++ negative::false::boundary::true::left)

def denTrace (background : Stack → List Bool) (context : C) :
    Bool → Bool → Bool → List Bool → Bool → Bool → List Bool → Bool → Bool →
      List Bool → List Bool → List (State C)
  | bit,flag,pending,[],first,near,older,negative,boundary,left,target =>
      state background 1 context bit flag pending (denSource [] first near negative boundary older left) target ::
      state background 2 context first true pending
        (backCells (near::older) ++ negative::false::boundary::true::left)
        (false::false::true::first::target) ::
      numTrace background context near false near older negative boundary left (false::false::true::first::target)
  | bit,flag,pending,digit::later,first,near,older,negative,boundary,left,target =>
      state background 1 context bit flag pending (denSource (digit::later) first near negative boundary older left) target ::
      denTrace background context digit false pending later first near older negative boundary left (true::digit::target)

theorem den_head (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (denTrace background context bit flag pending later first near older negative boundary left target).head? =
      some (state background 1 context bit flag pending (denSource later first near negative boundary older left) target) := by
  cases later <;> rfl

theorem den_nonempty (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    denTrace background context bit flag pending later first near older negative boundary left target ≠ [] := by
  intro empty
  have head := den_head background context bit flag pending later first near older negative boundary left target
  rw [empty] at head
  cases head

theorem den_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (later : List Bool) (first near : Bool) (older : List Bool)
    (negative boundary : Bool) (left target : List Bool) :
    (denTrace background context bit flag pending later first near older negative boundary left target).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction later generalizing bit flag pending target with
  | nil =>
      apply List.isChain_cons_cons.mpr
      refine ⟨step_den_first caller background context bit flag pending first _ _,?_⟩
      apply List.isChain_cons.mpr
      refine ⟨?_,num_chain caller _ _ _ _ _ _ _ _ _ _⟩
      intro next head
      rw [num_head] at head
      have same := (Option.mem_some_iff.mp head).symm
      subst next
      exact step_num_first caller background context first true pending near _ _
  | cons digit rest ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_,ih _ _ _ _⟩
      intro next head
      rw [den_head] at head
      have same := (Option.mem_some_iff.mp head).symm
      subst next
      exact step_den_later caller background context bit flag pending digit _ _

theorem den_last (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (denTrace background context bit flag pending later first near older negative boundary left target).getLast? =
      some (state background 4 context boundary true negative (boundary::true::left)
        (true::negative::(frontCells (near::older).reverse ++ false::false::
          (frontCells (first::later.reverse) ++ target)))) := by
  induction later generalizing bit flag pending target with
  | nil =>
      rw [denTrace,List.getLast?_cons_of_ne_nil (by simp),
        List.getLast?_cons_of_ne_nil (num_nonempty _ _ _ _ _ _ _ _ _ _),num_last]
      simp only [List.reverse_nil,List.reverse_cons,frontCells,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.nil_append,List.cons_append,List.append_assoc]
  | cons digit rest ih =>
      rw [denTrace,List.getLast?_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _),ih]
      simp only [List.reverse_cons,frontCells,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem den_length (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (denTrace background context bit flag pending later first near older negative boundary left target).length =
      later.length+older.length+5 := by
  induction later generalizing bit flag pending target with
  | nil => simp only [denTrace,List.length_cons,num_length,List.length_nil]; omega
  | cons digit rest ih => simp only [denTrace,List.length_cons,ih]; omega

def actualTrace (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool)
    (left target : List Bool) : List (State C) :=
  state background 0 context bit flag pending
    (true::true::denSource later first near negative boundary older left) target ::
  denTrace background context bit flag pending later first near older negative boundary left (false::false::target)

theorem actual (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (later : List Bool) (first near : Bool) (older : List Bool)
    (negative boundary : Bool) (left target : List Bool) :
    ∃ run : List (State C),
      run.head? = some (state background 0 context bit flag pending
        (true::true::denSource later first near negative boundary older left) target) ∧
      run.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      run.getLast? = some (state background 4 context boundary true negative (boundary::true::left)
        (true::negative::(frontCells (near::older).reverse ++ false::false::
          (frontCells (first::later.reverse) ++ false::false::target)))) ∧
      run.length = later.length+older.length+6 := by
  refine ⟨actualTrace background context bit flag pending later first near older negative boundary left target,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,den_chain caller _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    intro next head
    rw [den_head] at head
    have same := (Option.mem_some_iff.mp head).symm
    subst next
    exact step_entry caller background context bit flag pending _ _
  · rw [actualTrace,List.getLast?_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _),den_last]
  · simp only [actualTrace,List.length_cons,den_length]

end RootB234.PrepBudgetArchive
