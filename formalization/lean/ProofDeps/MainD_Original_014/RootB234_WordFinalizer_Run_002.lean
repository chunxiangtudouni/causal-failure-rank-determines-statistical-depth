module

public import RootB234_WordFinalizer_Code_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.WordFinalizer

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

structure Path (before final : State C) (budget : Nat) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step program a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Path.edge (before after : State C) (edge : TM2.step program before=some after) :
    Path before after 2 :=
  ⟨[before,after],rfl,List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩

def Path.append {before middle final : State C} {a b : Nat}
    (front : Path before middle a) (back : Path middle final b) :
    Path before final (a+b-1) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  have size := congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have h1 := front.count
    have h2 := back.count
    simp only [List.length_append]
    omega

theorem actual_clear (frame : Stack → List Bool) (memory : Store C)
    (old parked source : List Bool) :
    Nonempty (Path (state frame .clear memory old parked source)
      (state frame .collect (memory.1,false,false) [] parked source) (old.length+2)) := by
  induction old generalizing memory with
  | nil => exact ⟨Path.edge _ _ (clear_end frame memory parked source)⟩
  | cons digit old ih =>
    obtain ⟨tail⟩ := ih (memory.1,true,digit)
    let front := Path.edge _ _ (clear_bit frame memory digit old parked source)
    let whole := front.append tail
    refine ⟨⟨whole.trace,whole.first,whole.chain,whole.last,?_⟩⟩
    have count := whole.count
    simp only [List.length_cons]
    omega

theorem actual_collect (frame : Stack → List Bool) (memory : Store C)
    (out parked source : List Bool) :
    Nonempty (Path (state frame .collect memory out parked source)
      (state frame .restore (memory.1,false,false) out (source.reverse++parked) []) (source.length+2)) := by
  induction source generalizing memory parked with
  | nil => exact ⟨Path.edge _ _ (collect_end frame memory out parked)⟩
  | cons digit source ih =>
    obtain ⟨tail⟩ := ih (memory.1,true,digit) (digit::parked)
    let front := Path.edge _ _ (collect_bit frame memory digit out parked source)
    let whole := front.append tail
    have last : whole.trace.getLast?=some
        (state frame .restore (memory.1,false,false) out ((digit::source).reverse++parked) []) := by
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using whole.last
    refine ⟨⟨whole.trace,whole.first,whole.chain,last,?_⟩⟩
    have count := whole.count
    simp only [List.length_cons]
    omega

theorem actual_restore (frame : Stack → List Bool) (memory : Store C)
    (out parked source : List Bool) :
    Nonempty (Path (state frame .restore memory out parked source)
      (⟨none,(memory.1,false,false),cells frame (parked.reverse++out) [] source⟩ : State C)
      (parked.length+2)) := by
  induction parked generalizing memory out with
  | nil => exact ⟨Path.edge _ _ (restore_end frame memory out source)⟩
  | cons digit parked ih =>
    obtain ⟨tail⟩ := ih (memory.1,true,digit) (digit::out)
    let front := Path.edge _ _ (restore_bit frame memory digit out parked source)
    let whole := front.append tail
    have last : whole.trace.getLast?=some
        (⟨none,(memory.1,false,false),cells frame ((digit::parked).reverse++out) [] source⟩ : State C) := by
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using whole.last
    refine ⟨⟨whole.trace,whole.first,whole.chain,last,?_⟩⟩
    have count := whole.count
    simp only [List.length_cons]
    omega

/-- The only supplied lists are actual old/output stack contents. Every
edge of the witness is proved to be a real step of the same fixed source. -/
theorem actual_run (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (entry frame memory old bits) ∧
      trace.IsChain (fun a b => TM2.step program a=some b) ∧
      trace.getLast?=some (result frame memory.1 bits) ∧
      trace.length≤old.length+2*bits.length+4 := by
  obtain ⟨clear⟩ := actual_clear frame memory old [] bits
  obtain ⟨collect⟩ := actual_collect frame (memory.1,false,false) [] [] bits
  have collect' : Nonempty (Path (state frame .collect (memory.1,false,false) [] [] bits)
      (state frame .restore (memory.1,false,false) [] bits.reverse []) (bits.length+2)) := by
    simpa only [List.append_nil] using (⟨collect⟩ : Nonempty _)
  obtain ⟨collect⟩ := collect'
  obtain ⟨restore⟩ := actual_restore frame (memory.1,false,false) [] bits.reverse []
  let whole := (clear.append collect).append restore
  refine ⟨whole.trace,whole.first,whole.chain,?_,?_⟩
  · simpa only [result,List.reverse_reverse,List.append_nil] using whole.last
  · have count := whole.count
    simp only [List.length_reverse] at count
    omega

end RootB234.WordFinalizer
