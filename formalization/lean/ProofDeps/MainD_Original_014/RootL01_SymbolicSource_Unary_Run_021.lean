module

public import RootL01_SymbolicSource_Unary_Code_020

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.Unary

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

def unary (value : Nat) : List Bool := List.replicate value true
def bitValue (bit : Bool) : Nat := if bit then 1 else 0

structure Path (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  first : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget

def Path.single {caller : Statement C} (before final : State C)
    (edge : TM2.step (program caller) before = some final) : Path caller before final 2 :=
  ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩

def Path.prepend {caller : Statement C} {middle final : State C} {budget : Nat}
    (tail : Path caller middle final budget) (before : State C)
    (edge : TM2.step (program caller) before = some middle) : Path caller before final (budget+1) := by
  have nonempty : tail.trace ≠ [] := by
    intro empty
    have first := tail.first
    simp [empty] at first
  refine ⟨before :: tail.trace,rfl,?_,?_,?_⟩
  · apply List.isChain_cons.mpr
    refine ⟨?_,tail.chain⟩
    intro next member
    have same : middle = next := by simpa only [tail.first,Option.mem_some_iff] using member
    subst next
    exact edge
  · rw [List.getLast?_cons_of_ne_nil nonempty,tail.last]
  · simpa only [List.length_cons] using Nat.add_le_add_right tail.count 1

def Path.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Path caller before middle A) (back : Path caller middle final B) : Path caller before final (A+B-1) := by
  have shape : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]
    rfl
  have size := congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace ++ back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]
    rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append]
    omega

theorem double_actual (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits : List Bool) (amount work : Nat) :
    Nonempty (Path caller
      (state frame .double context (bit,flag) digits (unary amount) (unary work))
      (state frame .restore context (bit,false) digits [] (unary (work+2*amount))) (amount+2)) := by
  induction amount generalizing work flag with
  | zero =>
    exact ⟨Path.single _ _ (by simpa only [unary,Nat.mul_zero,Nat.add_zero,List.replicate_zero] using
      (double_end caller frame context bit flag digits (unary work)))⟩
  | succ amount ih =>
    obtain ⟨tail⟩ := ih true (work+2)
    have edge : TM2.step (program caller)
        (state frame .double context (bit,flag) digits (unary (amount+1)) (unary work)) =
        some (state frame .double context (bit,true) digits (unary amount) (unary (work+2))) := by
      simpa [unary,List.replicate_succ] using
        double_bit caller frame context bit flag digits (unary amount) (unary work)
    have sum : work+2+2*amount = work+2*(amount+1) := by omega
    have next := tail.prepend _ edge
    rw [sum] at next
    have budget : amount+2+1 = amount+1+2 := by omega
    rw [budget] at next
    exact ⟨next⟩

theorem restore_actual (caller : Statement C) (frame : Bank) (context : C) (bit flag : Bool)
    (digits : List Bool) (amount work : Nat) :
    Nonempty (Path caller
      (state frame .restore context (bit,flag) digits (unary amount) (unary work))
      (state frame .read context (bit,false) digits (unary (amount+work+bitValue bit)) []) (work+2)) := by
  induction work generalizing amount flag with
  | zero =>
    have edge := restore_end caller frame context bit flag digits (unary amount)
    have value : (if bit then true::unary amount else unary amount) = unary (amount+bitValue bit) := by
      cases bit <;> rfl
    rw [value] at edge
    exact ⟨Path.single _ _ (by simpa only [Nat.add_zero,unary,List.replicate_zero] using edge)⟩
  | succ work ih =>
    obtain ⟨tail⟩ := ih true (amount+1)
    have edge : TM2.step (program caller)
        (state frame .restore context (bit,flag) digits (unary amount) (unary (work+1))) =
        some (state frame .restore context (bit,true) digits (unary (amount+1)) (unary work)) := by
      simpa [unary,List.replicate_succ] using
        restore_bit caller frame context bit flag digits (unary amount) (unary work)
    have sum : amount+1+work+bitValue bit = amount+(work+1)+bitValue bit := by omega
    have next := tail.prepend _ edge
    rw [sum] at next
    have budget : work+2+1 = work+1+2 := by omega
    rw [budget] at next
    exact ⟨next⟩

theorem digit_actual (caller : Statement C) (frame : Bank) (context : C) (memory : Registers)
    (digit : Bool) (digits : List Bool) (amount : Nat) :
    Nonempty (Path caller
      (state frame .read context memory (digit::digits) (unary amount) [])
      (state frame .read context (digit,false) digits (unary (2*amount+bitValue digit)) []) (3*amount+4)) := by
  let start := Path.single _ _ (read_bit caller frame context memory digit digits (unary amount) [])
  obtain ⟨double⟩ := double_actual caller frame context digit true digits amount 0
  obtain ⟨restore⟩ := restore_actual caller frame context digit false digits 0 (2*amount)
  have middle : state frame .restore context (digit,false) digits [] (unary (0+2*amount)) =
      state frame .restore context (digit,false) digits (unary 0) (unary (2*amount)) := by
    simp only [unary,Nat.zero_add,List.replicate_zero]
  let full := (start.append double).append (middle.symm ▸ restore)
  refine ⟨{trace:=full.trace,first:=full.first,chain:=full.chain,last:=?_,count:=?_}⟩
  · simpa only [Nat.zero_add] using full.last
  · have count := full.count
    omega

def evaluate : List Bool → Nat → Nat
  | [],amount => amount
  | bit::digits,amount => evaluate digits (2*amount+bitValue bit)

def time : List Bool → Nat → Nat
  | [],_ => 2
  | bit::digits,amount => 3*amount+3+time digits (2*amount+bitValue bit)

theorem actual (caller : Statement C) (frame : Bank) (context : C) (memory : Registers)
    (digits : List Bool) (amount : Nat) :
    Nonempty (Path caller
      (state frame .read context memory digits (unary amount) [])
      (state frame .done context (false,false) [] (unary (evaluate digits amount)) []) (time digits amount)) := by
  induction digits generalizing memory amount with
  | nil => exact ⟨Path.single _ _ (read_end caller frame context memory (unary amount) [])⟩
  | cons digit digits ih =>
    obtain ⟨front⟩ := digit_actual caller frame context memory digit digits amount
    obtain ⟨back⟩ := ih (digit,false) (2*amount+bitValue digit)
    let full := front.append back
    refine ⟨{trace:=full.trace,first:=full.first,chain:=full.chain,last:=full.last,count:=?_}⟩
    have count := full.count
    change full.trace.length ≤ 3*amount+3+time digits (2*amount+bitValue digit)
    omega

theorem evaluate_ge (digits : List Bool) (amount : Nat) : amount ≤ evaluate digits amount := by
  induction digits generalizing amount with
  | nil => exact Nat.le_refl _
  | cons bit digits ih =>
    have tail := ih (2*amount+bitValue bit)
    change amount ≤ evaluate digits (2*amount+bitValue bit)
    omega

theorem time_le (digits : List Bool) (amount : Nat) :
    time digits amount ≤ (3*evaluate digits amount+3)*digits.length+2 := by
  induction digits generalizing amount with
  | nil => simp [time]
  | cons bit digits ih =>
    have tail := ih (2*amount+bitValue bit)
    have lower := evaluate_ge (bit::digits) amount
    simp only [time,evaluate,List.length_cons] at tail lower ⊢
    nlinarith

end RootL01.SymbolicSource.Unary
