module
public import Structure.B23_5_RawInit_ReverseResources009

/-! Actual source disposal after the reverse-export loop. Both TRUE
boundary cells, all restored source pairs, and the right sentinel are
really erased; the real output bottom marker stops the FALSE-gap scan.
The final whole Tape is precisely the row word with blank west tape. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseCleanup
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def machine : Machine 9 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write false)
  | 2 => some (3,.move .right)
  | 3 => some (4,.write false)
  | 4 => some (5,.move .right)
  | 5 => if symbol then some (8,.write false) else some (6,.move .right)
  | 6 => some (7,.write false)
  | 7 => some (5,.move .right)
  | 8 => some (9,.move .right)
  | _ => if symbol then none else some (9,.move .right)

def state (q : Fin 10) (left right : List Bool) : MachineState 9 := ⟨q,Tape.mk₂ left right⟩

theorem zeros_succ (gap : Nat) (left : List Bool) :
    List.replicate gap false++false::left=false::(List.replicate gap false++left) := by
  have eq := PA17RawInitRowReturn.zeros_snoc gap left
  simpa only [List.replicate_succ,List.cons_append] using eq

def gapTrace (left : List Bool) : Nat → List Bool → List (MachineState 9)
  | 0,tail => [state 9 left (true::tail)]
  | gap+1,tail => state 9 left (false::(List.replicate gap false++true::tail)) ::
      gapTrace (false::left) gap tail

theorem gap_head (left tail : List Bool) (gap : Nat) :
    (gapTrace left gap tail).head?=some (state 9 left (List.replicate gap false++true::tail)) := by
  cases gap <;> rfl
theorem gap_last (left tail : List Bool) (gap : Nat) :
    (gapTrace left gap tail).getLast?=some (state 9 (List.replicate gap false++left) (true::tail)) := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih =>
    rw [gapTrace,List.getLast?_cons,ih]
    simp only [Option.getD_some,List.replicate_succ,List.cons_append]
    rw [zeros_succ]

theorem gap_chain (left tail : List Bool) (gap : Nat) :
    (gapTrace left gap tail).IsChain (fun before after => TM0.step machine before=some after) := by
  induction gap generalizing left with
  | zero => exact .singleton _
  | succ gap ih =>
    apply List.IsChain.cons (ih (false::left))
    intro after member
    rw [gap_head] at member
    have eq : after=state 9 (false::left) (List.replicate gap false++true::tail) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    simp [state,TM0.step,machine,Tape.mk₂]
theorem gap_length (left tail : List Bool) (gap : Nat) :
    (gapTrace left gap tail).length=gap+1 := by
  induction gap generalizing left with
  | zero => rfl
  | succ gap ih => simp only [gapTrace,List.length_cons,ih]

def pairTrace (left : List Bool) : List Bool → List Bool → Nat → List (MachineState 9)
  | [],tail,gap =>
      [state 5 left (true::(List.replicate (gap+1) false++true::tail)),
       state 8 left (false::(List.replicate (gap+1) false++true::tail))] ++
        gapTrace (false::left) (gap+1) tail
  | bit::later,tail,gap =>
      [state 5 left (false::bit::(MarkSeek.pairs later++true::(List.replicate (gap+1) false++true::tail))),
       state 6 (false::left) (bit::(MarkSeek.pairs later++true::(List.replicate (gap+1) false++true::tail))),
       state 7 (false::left) (false::(MarkSeek.pairs later++true::(List.replicate (gap+1) false++true::tail)))] ++
        pairTrace (false::false::left) later tail gap

theorem pair_head (left bits tail : List Bool) (gap : Nat) :
    (pairTrace left bits tail gap).head?=some (state 5 left
      (MarkSeek.pairs bits++true::(List.replicate (gap+1) false++true::tail))) := by
  cases bits <;> rfl

theorem pair_length (left bits tail : List Bool) (gap : Nat) :
    (pairTrace left bits tail gap).length=3*bits.length+gap+4 := by
  induction bits generalizing left with
  | nil => simp only [pairTrace,List.length_append,List.length_cons,List.length_nil,gap_length]; omega
  | cons bit later ih =>
    simp only [pairTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem pair_last (left bits tail : List Bool) (gap : Nat) :
    (pairTrace left bits tail gap).getLast?=some (state 9
      (List.replicate (gap+1) false++false::(List.replicate (2*bits.length) false++left))
      (true::tail)) := by
  induction bits generalizing left with
  | nil =>
    simp only [pairTrace,List.getLast?_append,gap_last,Option.some_or,List.length_nil,
      Nat.mul_zero,List.replicate_zero,List.nil_append]
  | cons bit later ih =>
    have eq := ih (false::false::left)
    simp only [pairTrace,List.getLast?_append,eq,Option.some_or]
    have padding : List.replicate (2*later.length) false++false::false::left =
        List.replicate (2*(bit::later).length) false++left := by
      rw [zeros_succ,zeros_succ]
      simp only [List.length_cons]
      have count : 2*(later.length+1)=2*later.length+2 := by omega
      rw [count,List.replicate_succ,List.replicate_succ]
      rfl
    rw [padding]

theorem pair_chain (left bits tail : List Bool) (gap : Nat) :
    (pairTrace left bits tail gap).IsChain
      (fun before after => TM0.step machine before=some after) := by
  induction bits generalizing left with
  | nil =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,state,TM0.step,machine,Tape.mk₂]
    · exact gap_chain (false::left) tail (gap+1)
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [gap_head,Option.mem_some_iff] at ha
      subst before; subst after
      simp [state,TM0.step,machine,Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,state,TM0.step,machine,Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [pair_head,Option.mem_some_iff] at ha
      subst before; subst after
      simp [state,TM0.step,machine,Tape.mk₂]

def initial (bits output : List Bool) (gap : Nat) : MachineState 9 :=
  ⟨0,ReverseLoop.tape [] bits gap output⟩
def final (output : List Bool) : MachineState 9 := ⟨9,Tape.mk₁ (RowEnd.rows output)⟩

theorem actual (bits output : List Bool) (gap inputLength : Nat) :
    ∃ path, RunsFrom machine (initial bits output gap) path (final output) ∧
      path.length=3*bits.length+gap+9 ∧ ∀ clock,
        visitedSpace machine inputLength (path.take clock) ≤ inputLength+2*(3*bits.length+gap+9)+1 := by
  let right := MarkSeek.pairs bits++true::(List.replicate (gap+1) false++RowEnd.rows output)
  let lead := [initial bits output gap,
    state 1 [] (true::true::right),state 2 [] (false::true::right),
    state 3 [false] (true::right),state 4 [false] (false::right)]
  let body := pairTrace [false,false] bits (RowEnd.rows output).tail gap
  have rowHead : true::(RowEnd.rows output).tail=RowEnd.rows output := by rfl
  have initialEq : initial bits output gap=state 0 [true] (true::right) := by
    simp only [initial,ReverseLoop.tape,ReverseLoop.suffix,right,List.replicate_succ,List.cons_append]
    rfl
  have leadChain : lead.IsChain (fun before after => TM0.step machine before=some after) := by
    simp [lead,initialEq,List.isChain_cons_cons,state,TM0.step,machine,Tape.mk₂]
  have bodyChain := pair_chain [false,false] bits (RowEnd.rows output).tail gap
  have chain : (lead++body).IsChain (fun before after => TM0.step machine before=some after) := by
    apply List.IsChain.append leadChain bodyChain
    intro before hb after ha
    simp only [lead,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
    simp only [pair_head,Option.mem_some_iff] at ha
    subst before; subst after
    simp [right,rowHead,state,TM0.step,machine,Tape.mk₂]
  have last := pair_last [false,false] bits (RowEnd.rows output).tail gap
  have leftBlank : ListBlank.mk
      (List.replicate (gap+1) false++false::(List.replicate (2*bits.length) false++[false,false])) =
        ListBlank.mk ([] : List Bool) := by
    have empty (n : Nat) : ListBlank.mk (List.replicate n false)=ListBlank.mk ([] : List Bool) :=
      Quotient.sound (Or.inr ⟨n,rfl⟩)
    have padding : List.replicate (gap+1) false++false::(List.replicate (2*bits.length) false++[false,false])=
        List.replicate (gap+1+(1+(2*bits.length+2))) false := by
      rw [show ([false,false] : List Bool)=List.replicate 2 false by rfl,
        ← List.replicate_add]
      change List.replicate (gap+1) false++List.replicate (2*bits.length+2+1) false = _
      rw [← List.replicate_add]
      congr 1
      omega
    rw [padding]
    exact empty _
  have lastEq : body.getLast?=some (final output) := by
    change (pairTrace [false,false] bits (RowEnd.rows output).tail gap).getLast?=_
    rw [last]
    simp only [final,state,Tape.mk₂,Tape.mk₁,rowHead]
    rw [leftBlank]
  have time : (lead++body).length=3*bits.length+gap+9 := by
    simp only [lead,body,List.length_append,List.length_cons,List.length_nil,pair_length]
    omega
  refine ⟨lead++body,⟨?_,chain,?_,?_⟩,time,?_⟩
  · simp only [lead,List.head?_append,List.head?_cons,Option.some_or]
  · simp only [List.getLast?_append,lastEq,Option.some_or]
  · simp [final,TM0.step,machine,RowEnd.rows,rowBits,Tape.mk₁,Tape.mk₂]
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le machine inputLength ((lead++body).take clock)
    have take := List.length_take_le' clock (lead++body)
    rw [time] at take
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseCleanup
