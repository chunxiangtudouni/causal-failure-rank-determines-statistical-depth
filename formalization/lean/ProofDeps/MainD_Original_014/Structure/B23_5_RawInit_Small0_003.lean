module
public import Common.PSTR_TM_Trace_002
public import Common.PSTR_WordBool_Emit33_Core001
public import Structure.PA17_RawInit_RowReturn_Core001

/-! Literal empty-list branch. Four frozen Emit33 calls really WRITE/RIGHT
132 cells, then a fixed 132 LEFT table restores the original head position.
All words used in the finite code below are compile-time constants. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small0Fixed
open Turing
open RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def emitLabel (q : Fin 85) : Fin 86 := ⟨q.val+1,by omega⟩
def emitCfg (cfg : MachineState 84) : MachineState 85 := ⟨emitLabel cfg.q,cfg.Tape⟩

/-- New entry0 performs a charged write-self to the frozen finite bit port. -/
def emit (bottom bit : Bool) : Machine 85 := fun q symbol =>
  if entry : q.val=0 then some (emitLabel (Emit33.entry bottom bit),.write symbol)
  else (Emit33.code ⟨q.val-1,by omega⟩ symbol).map
    (fun (next,op) => (emitLabel next,op))

theorem emit_step (bottom bit : Bool) (cfg : MachineState 84) :
    TM0.step (emit bottom bit) (emitCfg cfg) =
      (TM0.step Emit33.code cfg).map emitCfg := by
  cases cfg with
  | mk q tape =>
    have positive : q.val+1≠0 := by omega
    simp only [TM0.step,emitCfg,emit,emitLabel,positive,↓reduceDIte,
      Nat.add_sub_cancel_right,Fin.eta]
    cases action : Emit33.code q tape.head with
    | none => rfl
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

theorem emit_actual (bottom bit : Bool) (left old suffix : List Bool)
    (size : old.length=33) :
    ∃ path, RunsFrom (emit bottom bit) ⟨0,Tape.mk₂ left (old++suffix)⟩ path
        (emitCfg ⟨Emit33.haltPort,Tape.mk₂ ((rowBits bottom bit).reverse++left) suffix⟩) ∧
      path.length=68 := by
  obtain ⟨body,run,time⟩ := Emit33.runs_list bottom bit left old suffix size
  let first : MachineState 85 := ⟨0,Tape.mk₂ left (old++suffix)⟩
  let path := first :: body.map emitCfg
  have chain : path.IsChain (fun before after => TM0.step (emit bottom bit) before=some after) := by
    apply List.IsChain.cons
    · apply (List.isChain_map _).mpr
      exact run.2.1.imp (fun before after edge => by simp [emit_step,edge])
    · intro next member
      simp only [List.head?_map,run.1,Option.map_some,Option.mem_some_iff] at member
      subst next
      simp [TM0.step,emit,first,emitCfg,Tape.write_self]
  refine ⟨path,⟨rfl,chain,?_,?_⟩,?_⟩
  · have nonempty : body.map emitCfg ≠ [] := by
      intro empty
      have length := congrArg List.length empty
      simp only [List.length_map,time,List.length_nil] at length
      omega
    simp only [path,List.getLast?_cons_of_ne_nil nonempty,List.getLast?_map,
      run.2.2.1,Option.map_some]
  · simp only [emit_step,run.2.2.2,Option.map_none]
  · simp only [path,List.length_cons,List.length_map,time]

def rewind : Machine 132 := fun q _ =>
  if before : q.val<132 then some (⟨q.val+1,by omega⟩,.move .left) else none

def rewindTrace : (steps start : Nat) → start+steps≤132 → Tape Bool → List (MachineState 132)
  | 0,start,bound,tape => [⟨⟨start,by omega⟩,tape⟩]
  | steps+1,start,bound,tape =>
      ⟨⟨start,by omega⟩,tape⟩ :: rewindTrace steps (start+1) (by omega) (tape.move .left)

theorem rewind_head (steps start : Nat) (bound : start+steps≤132) (tape : Tape Bool) :
    (rewindTrace steps start bound tape).head?=some ⟨⟨start,by omega⟩,tape⟩ := by
  cases steps <;> rfl

theorem rewind_last (steps start : Nat) (bound : start+steps≤132) (tape : Tape Bool) :
    (rewindTrace steps start bound tape).getLast?=
      some ⟨⟨start+steps,by omega⟩,((Tape.move .left)^[steps] tape)⟩ := by
  induction steps generalizing start tape with
  | zero => simp only [rewindTrace,List.getLast?_singleton,Nat.add_zero,Function.iterate_zero_apply]
  | succ steps ih =>
    rw [rewindTrace,List.getLast?_cons,ih]
    have add : start+1+steps=start+(steps+1) := by omega
    simp only [Option.getD_some,add,Function.iterate_succ_apply]

theorem rewind_chain (steps start : Nat) (bound : start+steps≤132) (tape : Tape Bool) :
    (rewindTrace steps start bound tape).IsChain
      (fun before after => TM0.step rewind before=some after) := by
  induction steps generalizing start tape with
  | zero => exact .singleton _
  | succ steps ih =>
    apply List.IsChain.cons (ih (start+1) (by omega) (tape.move .left))
    intro next member
    rw [rewind_head] at member
    have eq : next=⟨⟨start+1,by omega⟩,tape.move .left⟩ := (Option.mem_some_iff.mp member).symm
    subst next
    have before : start<132 := by omega
    simp [TM0.step,rewind,before]

theorem rewind_length (steps start : Nat) (bound : start+steps≤132) (tape : Tape Bool) :
    (rewindTrace steps start bound tape).length=steps+1 := by
  induction steps generalizing start tape with
  | zero => rfl
  | succ steps ih => simp only [rewindTrace,List.length_cons,ih]

def row1 : List Bool := rowBits true true
def row2 : List Bool := rowBits false false
def row3 : List Bool := rowBits false false
def row4 : List Bool := rowBits false true
def target : List Bool := row1++row2++row3++row4
def rows12 : Machine 171 := seqMachine (emit true true) (emit false false)
def rows123 : Machine 257 := seqMachine rows12 (emit false false)
def rows1234 : Machine 343 := seqMachine rows123 (emit false true)
def machine : Machine 476 := seqMachine rows1234 rewind

theorem pad_right (left right : List Bool) (n : Nat) :
    Tape.mk₂ left right = Tape.mk₂ left (right++List.replicate n false) := by
  have eq : ListBlank.mk right = ListBlank.mk (right++List.replicate n false) :=
    Quotient.sound (Or.inl ⟨n,rfl⟩)
  change Tape.mk' (ListBlank.mk left) (ListBlank.mk right)=_
  rw [eq]
  rfl

theorem blank_right (left : List Bool) :
    Tape.mk₂ left []=Tape.mk₂ left (List.replicate 33 false++[]) := by
  simpa only [List.nil_append,List.append_nil] using pad_right left [] 33

theorem input_eq : encode [] = [true,false,false,true] := by rfl
theorem target_eq : target = FiniteTrackCodec.encodedInput (0 : Fin 16) (encode []) := by
  rw [encoded_raw_shape]
  rfl
theorem target_length : target.length=132 := by rfl

theorem write_actual :
    ∃ path final, Runs rows1234 (encode []) path final ∧
      final.Tape=Tape.mk₂ target.reverse [] ∧ path.length=272 := by
  let old := [true,false,false,true]++List.replicate 29 false
  obtain ⟨p1,r1,t1⟩ := emit_actual true true [] old [] (by rfl)
  have inputTape : Tape.mk₁ (encode [])=Tape.mk₂ [] (old++[]) := by
    rw [input_eq]
    simpa only [old,List.append_nil,Tape.mk₁] using pad_right [] [true,false,false,true] 29
  have r1' : Runs (emit true true) (encode []) p1
      (emitCfg ⟨Emit33.haltPort,Tape.mk₂ row1.reverse []⟩) := by
    apply PSTRTMTrace002.runs_of_chain
    · rw [r1.1]; congr 1; exact congrArg (fun t => (⟨0,t⟩ : MachineState 85)) inputTape.symm
    · exact r1.2.1
    · simpa only [row1,List.append_nil] using r1.2.2.1
    · simpa only [row1,List.append_nil] using r1.2.2.2
  obtain ⟨p2,r2,t2⟩ := emit_actual false false row1.reverse (List.replicate 33 false) [] (by simp)
  have r2' : RunsFrom (emit false false) ⟨0,Tape.mk₂ row1.reverse []⟩ p2
      (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row2.reverse++row1.reverse) []⟩) := by
    rw [blank_right row1.reverse]; exact r2
  let p12 := p1.map (leftCfg (b:=85))++p2.map (rightCfg (a:=85))
  let f12 := rightCfg (a:=85) (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row2.reverse++row1.reverse) []⟩)
  have r12 : Runs rows12 (encode []) p12 f12 :=
    seq_runs (emit true true) (emit false false) (encode []) _ _ p1 p2 r1' r2'
  obtain ⟨p3,r3,t3⟩ := emit_actual false false (row2.reverse++row1.reverse) (List.replicate 33 false) [] (by simp)
  have r3' : RunsFrom (emit false false) ⟨0,f12.Tape⟩ p3
      (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row3.reverse++(row2.reverse++row1.reverse)) []⟩) := by
    change RunsFrom _ ⟨0,Tape.mk₂ (row2.reverse++row1.reverse) []⟩ _ _
    rw [blank_right]; exact r3
  let p123 := p12.map (leftCfg (b:=85))++p3.map (rightCfg (a:=171))
  let f123 := rightCfg (a:=171) (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row3.reverse++(row2.reverse++row1.reverse)) []⟩)
  have r123 : Runs rows123 (encode []) p123 f123 :=
    seq_runs rows12 (emit false false) (encode []) _ _ p12 p3 r12 r3'
  obtain ⟨p4,r4,t4⟩ := emit_actual false true (row3.reverse++(row2.reverse++row1.reverse)) (List.replicate 33 false) [] (by simp)
  have r4' : RunsFrom (emit false true) ⟨0,f123.Tape⟩ p4
      (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row4.reverse++(row3.reverse++(row2.reverse++row1.reverse))) []⟩) := by
    change RunsFrom _ ⟨0,Tape.mk₂ (row3.reverse++(row2.reverse++row1.reverse)) []⟩ _ _
    rw [blank_right]; exact r4
  let path := p123.map (leftCfg (b:=85))++p4.map (rightCfg (a:=257))
  let final := rightCfg (a:=257) (emitCfg ⟨Emit33.haltPort,Tape.mk₂ (row4.reverse++(row3.reverse++(row2.reverse++row1.reverse))) []⟩)
  refine ⟨path,final,seq_runs rows123 (emit false true) (encode []) _ _ p123 p4 r123 r4',?_,?_⟩
  · change Tape.mk₂ _ []=Tape.mk₂ target.reverse []
    simp only [target,List.reverse_append,List.append_assoc]
  · simp only [path,p123,p12,List.length_map,List.length_append,t1,t2,t3,t4]

theorem actual : ∃ path final, Runs machine (encode []) path final ∧
    final.q=476 ∧ final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode [])) ∧
    path.length=405 ∧ ∀ clock,
      visitedSpace machine (encode []).length (path.take clock)≤815 := by
  obtain ⟨front,mid,frontRun,midTape,frontTime⟩ := write_actual
  let back := rewindTrace 132 0 (by omega) (Tape.mk₂ target.reverse [])
  have backRun : RunsFrom rewind ⟨0,mid.Tape⟩ back ⟨132,Tape.mk₁ target⟩ := by
    rw [midTape]
    refine ⟨rewind_head _ _ _ _,rewind_chain _ _ _ _,?_,?_⟩
    · have last := rewind_last 132 0 (by omega) (Tape.mk₂ target.reverse [])
      have moved := PA17RawInitRowReturn.move_left_word target [] []
      have moved' : (Tape.move .left)^[132] (Tape.mk₂ target.reverse [])=Tape.mk₁ target := by
        simpa only [target_length,List.append_nil,Tape.mk₁] using moved
      change (rewindTrace 132 0 (by omega) (Tape.mk₂ target.reverse [])).getLast? = _
      convert last using 1
      simp only [moved',Nat.zero_add]
      congr 2
    · simp [TM0.step,rewind]
  let path := front.map (leftCfg (b:=132))++back.map (rightCfg (a:=343))
  let final : MachineState 476 := rightCfg (a:=343) (b:=132) ⟨132,Tape.mk₁ target⟩
  refine ⟨path,final,seq_runs rows1234 rewind (encode []) mid _ front back frontRun backRun,rfl,?_,?_,?_⟩
  · change Tape.mk₁ target = _; rw [target_eq]
  · simp only [path,back,List.length_append,List.length_map,frontTime,rewind_length]
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine (encode []).length (path.take clock)
    have short := List.length_take_le' clock path
    have length : path.length=405 := by simp only [path,back,List.length_append,List.length_map,frontTime,rewind_length]
    have inputLength : (encode []).length=4 := by rfl
    rw [length] at short
    rw [inputLength] at space ⊢
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small0Fixed
