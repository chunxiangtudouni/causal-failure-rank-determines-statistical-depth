module

public import RootB234_RuntimeCounter_Round_Code_002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRTMIncrement009

structure Path (before final : BaseState) (budget : Nat) where
  trace : List BaseState
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step baseProgram a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Path.edge (before after : BaseState) (edge : TM2.step baseProgram before=some after) : Path before after 2 :=
  ⟨[before,after],rfl,List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩

def Path.append {before middle final : BaseState} {a b : Nat}
    (front : Path before middle a) (back : Path middle final b) : Path before final (a+b-1) := by
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

theorem collect_bit (frame : Stack → List Bool) (memory : Registers) (digit : Bool)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 2 memory (digit::true::right) left scratch)=
      some (baseState frame 2 ((true,true),memory.2) right left (true::digit::scratch)) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,bit,jump,right_at,scratch_at,update_right,update_scratch]

theorem collect_end (frame : Stack → List Bool) (memory : Registers)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 2 memory (false::false::right) left scratch)=
      some (baseState frame 3 ((true,false),memory.2) right left (false::false::scratch)) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,bit,jump,right_at,scratch_at,update_right,update_scratch]

theorem actual_collect (frame : Stack → List Bool) (memory : Registers)
    (digits right left scratch : List Bool) :
    Nonempty (Path (baseState frame 2 memory (blocks digits++false::false::right) left scratch)
      (baseState frame 3 ((true,false),memory.2) right left
        (false::false::((blocks digits).reverse++scratch))) (digits.length+2)) := by
  induction digits generalizing memory scratch with
  | nil => exact ⟨Path.edge _ _ (collect_end frame memory right left scratch)⟩
  | cons digit digits ih =>
    obtain ⟨tail⟩ := ih ((true,true),memory.2) (true::digit::scratch)
    let step := Path.edge _ _ (collect_bit frame memory digit (blocks digits++false::false::right) left scratch)
    let whole := step.append tail
    refine ⟨⟨whole.trace,whole.first,whole.chain,?_,?_⟩⟩
    · simpa only [blocks,List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using whole.last
    · have count := whole.count
      simp only [List.length_cons]
      omega

theorem marker_step (frame : Stack → List Bool) (memory : Registers)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 3 memory (true::right) left scratch)=
      some (baseState frame 4 ((true,true),memory.2) right left (true::scratch)) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,bit,jump,right_at,scratch_at,update_right,update_scratch]

theorem clear_right_bit (frame : Stack → List Bool) (memory : Registers) (digit : Bool)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 4 memory (digit::right) left scratch)=
      some (baseState frame 4 ((true,digit),memory.2) right left scratch) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,jump,right_at,update_right]

theorem clear_right_end (frame : Stack → List Bool) (memory : Registers) (left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 4 memory [] left scratch)=
      some (baseState frame 5 ((false,false),memory.2) [] left scratch) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,jump,right_at,update_right]

theorem actual_clear_right (frame : Stack → List Bool) (memory : Registers) (right left scratch : List Bool) :
    Nonempty (Path (baseState frame 4 memory right left scratch)
      (baseState frame 5 ((false,false),memory.2) [] left scratch) (right.length+2)) := by
  induction right generalizing memory with
  | nil => exact ⟨Path.edge _ _ (clear_right_end frame memory left scratch)⟩
  | cons digit right ih =>
    obtain ⟨tail⟩ := ih ((true,digit),memory.2)
    let whole := (Path.edge _ _ (clear_right_bit frame memory digit right left scratch)).append tail
    refine ⟨⟨whole.trace,whole.first,whole.chain,whole.last,?_⟩⟩
    have count := whole.count
    simp only [List.length_cons]
    omega

theorem clear_left_bit (frame : Stack → List Bool) (memory : Registers) (digit : Bool)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 5 memory right (digit::left) scratch)=
      some (baseState frame 5 ((true,digit),memory.2) right left scratch) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,jump,left_at,update_left]

theorem clear_left_end (frame : Stack → List Bool) (memory : Registers) (right scratch : List Bool) :
    TM2.step baseProgram (baseState frame 5 memory right [] scratch)=
      some (baseState frame 6 ((false,false),memory.2) right [false] scratch) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,jump,left_at,update_left]

theorem actual_clear_left (frame : Stack → List Bool) (memory : Registers) (right left scratch : List Bool) :
    Nonempty (Path (baseState frame 5 memory right left scratch)
      (baseState frame 6 ((false,false),memory.2) right [false] scratch) (left.length+2)) := by
  induction left generalizing memory with
  | nil => exact ⟨Path.edge _ _ (clear_left_end frame memory right scratch)⟩
  | cons digit left ih =>
    obtain ⟨tail⟩ := ih ((true,digit),memory.2)
    let whole := (Path.edge _ _ (clear_left_bit frame memory digit right left scratch)).append tail
    refine ⟨⟨whole.trace,whole.first,whole.chain,whole.last,?_⟩⟩
    have count := whole.count
    simp only [List.length_cons]
    omega

theorem restore_bit (frame : Stack → List Bool) (memory : Registers) (digit : Bool)
    (right left scratch : List Bool) :
    TM2.step baseProgram (baseState frame 6 memory right left (digit::scratch))=
      some (baseState frame 6 ((true,digit),memory.2) (digit::right) left scratch) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,bit,jump,right_at,scratch_at,
    update_right,update_scratch]

theorem restore_end (frame : Stack → List Bool) (memory : Registers) (right left : List Bool) :
    TM2.step baseProgram (baseState frame 6 memory right left [])=
      some (baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2) right left []) := by
  simp [baseState,baseProgram,TM2.step,TM2.stepAux,capture,present,jump,scratch_at,update_scratch]
  rw [show initialZero ((false,false),memory.2)=initialZero memory from rfl]
  cases initialZero memory <;> rfl

theorem actual_restore (frame : Stack → List Bool) (memory : Registers) (right left scratch : List Bool) :
    Nonempty (Path (baseState frame 6 memory right left scratch)
      (baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2)
        (scratch.reverse++right) left []) (scratch.length+2)) := by
  induction scratch generalizing memory right with
  | nil => exact ⟨Path.edge _ _ (restore_end frame memory right left)⟩
  | cons digit scratch ih =>
    obtain ⟨tail⟩ := ih ((true,digit),memory.2) (digit::right)
    let whole := (Path.edge _ _ (restore_bit frame memory digit right left scratch)).append tail
    refine ⟨⟨whole.trace,whole.first,whole.chain,?_,?_⟩⟩
    · have endpoint :
          baseState frame (if initialZero ((true,digit),memory.2) then 7 else 8) ((false,false),memory.2)
            (scratch.reverse++digit::right) left []=
          baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2)
            ((digit::scratch).reverse++right) left [] := by
        rw [show initialZero ((true,digit),memory.2)=initialZero memory from rfl]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      exact whole.last.trans (congrArg some endpoint)
    · have count := whole.count
      simp only [List.length_cons]
      omega

theorem actual_normalize (frame : Stack → List Bool) (memory : Registers)
    (digits tail left : List Bool) :
    Nonempty (Path (baseState frame 2 memory (Raw.packet digits++tail) left [])
      (baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2)
        (Raw.packet digits) [false] []) (3*digits.length+tail.length+left.length+10)) := by
  obtain ⟨collect⟩ := actual_collect frame memory digits (true::tail) left []
  let mark := Path.edge _ _ (marker_step frame ((true,false),memory.2) tail left
    (false::false::(blocks digits).reverse))
  obtain ⟨clearR⟩ := actual_clear_right frame ((true,true),memory.2) tail left (Raw.packet digits).reverse
  obtain ⟨clearL⟩ := actual_clear_left frame ((false,false),memory.2) [] left (Raw.packet digits).reverse
  obtain ⟨restore⟩ := actual_restore frame ((false,false),memory.2) [] [false] (Raw.packet digits).reverse
  have collect' : Nonempty (Path (baseState frame 2 memory (Raw.packet digits++tail) left [])
      (baseState frame 3 ((true,false),memory.2) (true::tail) left (false::false::(blocks digits).reverse))
      (digits.length+2)) := by
    simpa only [Raw.packet,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using
      (⟨collect⟩ : Nonempty _)
  obtain ⟨collect⟩ := collect'
  have mark' : Nonempty (Path
      (baseState frame 3 ((true,false),memory.2) (true::tail) left (false::false::(blocks digits).reverse))
      (baseState frame 4 ((true,true),memory.2) tail left (Raw.packet digits).reverse) 2) := by
    simpa only [Raw.packet,List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,
      List.nil_append] using (⟨mark⟩ : Nonempty _)
  obtain ⟨mark⟩ := mark'
  let whole := (((collect.append mark).append clearR).append clearL).append restore
  have last : whole.trace.getLast?=some
      (baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2)
        (Raw.packet digits) [false] []) := by
    have endpoint :
        baseState frame (if initialZero ((false,false),memory.2) then 7 else 8) ((false,false),memory.2)
          ((Raw.packet digits).reverse.reverse++[]) [false] []=
        baseState frame (if initialZero memory then 7 else 8) ((false,false),memory.2)
          (Raw.packet digits) [false] [] := by
      rw [show initialZero ((false,false),memory.2)=initialZero memory from rfl,
        List.reverse_reverse,List.append_nil]
    exact whole.last.trans (congrArg some endpoint)
  refine ⟨⟨whole.trace,whole.first,whole.chain,last,?_⟩⟩
  have count := whole.count
  have width := packet_length digits
  have reversed : (Raw.packet digits).reverse.length=(Raw.packet digits).length := List.length_reverse
  omega

end RootB234.RuntimeCounter.Round
