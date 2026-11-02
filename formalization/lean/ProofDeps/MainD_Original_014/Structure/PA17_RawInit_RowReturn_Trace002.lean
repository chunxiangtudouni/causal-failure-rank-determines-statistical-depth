module
public import Structure.PA17_RawInit_RowReturn_Core001

/-! Actual whole-tape return traces: fixed33 LEFTs per row, charged
ordinary-row write-self, bottom LEFT and real-sentinel gap scan. -/
@[expose] public section
namespace PaperProofs.Common.Native.PA17RawInitRowReturn
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open PSTRWordBool.RawInit (rowBits rowBits_length)

def Path (initial : MachineState 34) (trace : List (MachineState 34)) (final : MachineState 34) : Prop :=
  trace.head?=some initial ∧ trace.IsChain (fun first last=>TM0.step machine first=some last) ∧ trace.getLast?=some final

theorem append_path (initial middle next final : MachineState 34) (first second : List (MachineState 34))
    (one : Path initial first middle) (two : Path next second final) (edge : TM0.step machine middle=some next) :
    Path initial (first++second) final := by
  refine ⟨by simp [List.head?_append,one.1],?_,by simp [List.getLast?_append,two.2.2]⟩
  apply List.IsChain.append one.2.1 two.2.1
  intro before atLast after atHead
  simp only [one.2.2,Option.mem_some_iff] at atLast
  simp only [two.1,Option.mem_some_iff] at atHead
  subst before
  subst after
  exact edge

theorem row_path (bottom bit : Bool) (left suffix : List Bool) :
    Path (state 0 (Tape.mk₂ ((rowBits bottom bit).reverse++left) suffix))
      (moveTrace 33 0 (by decide) (Tape.mk₂ ((rowBits bottom bit).reverse++left) suffix))
      (state 33 (Tape.mk₂ left (rowBits bottom bit++suffix))) := by
  refine ⟨moveTrace_head 33 0 (by decide) _,moveTrace_chain 33 0 (by decide) _,?_⟩
  have last:=moveTrace_last 33 0 (by decide) (Tape.mk₂ ((rowBits bottom bit).reverse++left) suffix)
  rw [row_moves] at last
  exact last

def scanStart : Nat → List Bool → List Bool → Tape Bool
  | 0,left,right => Tape.mk₂ left (true::right)
  | gap+1,left,right => Tape.mk₂ (List.replicate gap false++true::left) (false::right)

def seekTrace : Nat → List Bool → List Bool → List (MachineState 34)
  | 0,left,right => [state 34 (scanStart 0 left right)]
  | gap+1,left,right => state 34 (scanStart (gap+1) left right)::seekTrace gap left (false::right)

theorem seekTrace_head (gap : Nat) (left right : List Bool) :
    (seekTrace gap left right).head?=some (state 34 (scanStart gap left right)) := by
  cases gap <;> rfl

theorem zeros_snoc (gap : Nat) (right : List Bool) :
    List.replicate gap false++(false::right)=List.replicate (gap+1) false++right := by
  induction gap with
  | zero => rfl
  | succ gap ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih

theorem seekTrace_last (gap : Nat) (left right : List Bool) :
    (seekTrace gap left right).getLast?=
      some (state 34 (Tape.mk₂ left (true::(List.replicate gap false++right)))) := by
  induction gap generalizing right with
  | zero => rfl
  | succ gap ih =>
    rw [seekTrace,List.getLast?_cons,ih]
    simp only [Option.getD_some,zeros_snoc]

theorem seekTrace_chain (gap : Nat) (left right : List Bool) :
    (seekTrace gap left right).IsChain (fun first last=>TM0.step machine first=some last) := by
  induction gap generalizing right with
  | zero => exact List.IsChain.singleton _
  | succ gap ih =>
    apply List.IsChain.cons (ih (false::right))
    intro next member
    rw [seekTrace_head] at member
    have same : next=state 34 (scanStart gap left (false::right)) := (Option.mem_some_iff.mp member).symm
    subst next
    cases gap <;> simp [state,TM0.step,machine,scanStart,Tape.mk₂,List.replicate_succ]

theorem seekTrace_length (gap : Nat) (left right : List Bool) : (seekTrace gap left right).length=gap+1 := by
  induction gap generalizing right with
  | zero => rfl
  | succ gap ih => simp only [seekTrace,List.length_cons,ih]

def rows (bits : List Bool) : List Bool := rowBits true true++bits.flatMap (rowBits false)

def initialTape (bits : List Bool) (gap : Nat) (left suffix : List Bool) : Tape Bool :=
  Tape.mk₂ ((rows bits).reverse++List.replicate gap false++true::left) suffix

def finalTape (bits : List Bool) (gap : Nat) (left suffix : List Bool) : Tape Bool :=
  Tape.mk₂ left (true::(List.replicate gap false++rows bits++suffix))

theorem bottom_run (gap : Nat) (left suffix : List Bool) :
    ∃ trace,RunsFrom machine (state 0 (initialTape [] gap left suffix)) trace
      (state 34 (finalTape [] gap left suffix)) ∧ trace.length=gap+35 := by
  let base:=List.replicate gap false++true::left
  let word:=rowBits true true
  let first:=moveTrace 33 0 (by decide) (Tape.mk₂ (word.reverse++base) suffix)
  let second:=seekTrace gap left (word++suffix)
  have one : Path (state 0 (Tape.mk₂ (word.reverse++base) suffix)) first
      (state 33 (Tape.mk₂ base (word++suffix))) := row_path true true base suffix
  have two : Path (state 34 (scanStart gap left (word++suffix))) second
      (state 34 (Tape.mk₂ left (true::(List.replicate gap false++(word++suffix))))) :=
    ⟨seekTrace_head _ _ _,seekTrace_chain _ _ _,seekTrace_last _ _ _⟩
  have edge : TM0.step machine (state 33 (Tape.mk₂ base (word++suffix)))=
      some (state 34 (scanStart gap left (word++suffix))) := by
    cases gap <;> simp [state,base,word,rowBits,machine,TM0.step,scanStart,Tape.mk₂,List.replicate_succ]
  have path:=append_path _ _ _ _ first second one two edge
  have actual : RunsFrom machine (state 0 (initialTape [] gap left suffix)) (first++second)
      (state 34 (finalTape [] gap left suffix)) := by
    refine ⟨?_,path.2.1,?_,scan_halt _ _⟩
    · simpa only [initialTape,rows,List.flatMap_nil,List.append_nil,word,base,List.append_assoc] using path.1
    · simpa only [finalTape,rows,List.flatMap_nil,List.append_nil,word,List.append_assoc] using path.2.2
  refine ⟨first++second,actual,?_⟩
  simp only [List.length_append,first,second,moveTrace_length,seekTrace_length]
  omega

theorem rows_append (bits : List Bool) (bit : Bool) : rows (bits++[bit])=rows bits++rowBits false bit := by
  simp only [rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

theorem rows_run (bits : List Bool) (gap : Nat) (left suffix : List Bool) :
    ∃ trace,RunsFrom machine (state 0 (initialTape bits gap left suffix)) trace
      (state 34 (finalTape bits gap left suffix)) ∧ trace.length=34*bits.length+gap+35 := by
  induction bits using List.reverseRecOn generalizing suffix with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add] using bottom_run gap left suffix
  | append_singleton bits bit ih =>
    let word:=rowBits false bit
    let base:=(rows bits).reverse++List.replicate gap false++true::left
    obtain ⟨rest,restRun,restTime⟩:=ih (word++suffix)
    let first:=moveTrace 33 0 (by decide) (Tape.mk₂ (word.reverse++base) suffix)
    have one : Path (state 0 (Tape.mk₂ (word.reverse++base) suffix)) first
        (state 33 (Tape.mk₂ base (word++suffix))) := row_path false bit base suffix
    have inputEq : initialTape (bits++[bit]) gap left suffix=Tape.mk₂ (word.reverse++base) suffix := by
      simp only [initialTape,rows_append,List.reverse_append,word,base,List.append_assoc]
    have outputEq : finalTape (bits++[bit]) gap left suffix=finalTape bits gap left (word++suffix) := by
      simp only [finalTape,rows_append,word,List.append_assoc]
    have middleEq : Tape.mk₂ base (word++suffix)=initialTape bits gap left (word++suffix) := rfl
    have edge : TM0.step machine (state 33 (Tape.mk₂ base (word++suffix)))=
        some (state 0 (initialTape bits gap left (word++suffix))) := by
      rw [←middleEq]
      simp [state,word,rowBits,machine,TM0.step,Tape.mk₂]
    have path:=append_path _ _ _ _ first rest one ⟨restRun.1,restRun.2.1,restRun.2.2.1⟩ edge
    refine ⟨first++rest,?_,?_⟩
    · rw [inputEq,outputEq]
      exact ⟨path.1,path.2.1,path.2.2,restRun.2.2.2⟩
    · simp only [List.length_append,first,moveTrace_length,restTime,List.length_singleton]
      omega

end PaperProofs.Common.Native.PA17RawInitRowReturn
