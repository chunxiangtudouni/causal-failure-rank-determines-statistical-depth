module

public import RootB234_RuntimeCounter_Round_Native_004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRTMIncrement009 PSTRTMThresholdCountdownCode164
open scoped BigOperators

def occupied (slots : Stack → List Bool) : Nat := ∑ slot,(slots slot).length

theorem point_mass (slots : Stack → List Bool) (slot : Stack) : (slots slot).length≤occupied slots :=
  Finset.single_le_sum (fun other _ => Nat.zero_le (slots other).length) (Finset.mem_univ slot)

def scale (frame : Stack → List Bool) (digits : List Bool) : Nat :=
  occupied (cells frame (Raw.packet digits) [false] [])+1

theorem scale_pos (frame : Stack → List Bool) (digits : List Bool) : 0<scale frame digits := by
  dsimp only [scale]
  omega

theorem width_room (frame : Stack → List Bool) (digits : List Bool) : digits.length+1≤scale frame digits := by
  have right := point_mass (cells frame (Raw.packet digits) [false] []) 10
  change (Raw.packet digits).length≤occupied (cells frame (Raw.packet digits) [false] []) at right
  rw [packet_length] at right
  dsimp only [scale]
  omega

theorem output_width (digits : List Bool) : (Raw.outputDigits digits).length=digits.length := by
  by_cases zero : valueDigits digits=0
  · simp only [Raw.outputDigits,zero,ite_true]
  · simp only [Raw.outputDigits,zero,ite_false,pred_length]

theorem output_value (digits : List Bool) : valueDigits (Raw.outputDigits digits)=valueDigits digits-1 := by
  by_cases zero : valueDigits digits=0
  · simp only [Raw.outputDigits,zero,ite_true,Nat.zero_sub]
  · have positive := has_true_of_value_pos digits (Nat.pos_of_ne_zero zero)
    have value := pred_value digits positive
    simp only [Raw.outputDigits,zero,ite_false]
    omega

theorem step_slot_bound {σ Λ : Type*} (source : Λ → TM2.Stmt Alphabet Λ σ)
    (pushes : ∀ point,AuxWorkspace.pushes (source point)≤2)
    (before after : TM2.Cfg Alphabet Λ σ) (bound : Nat)
    (edge : TM2.step source before=some after) (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ slot,(after.stk slot).length≤bound+2 := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (source point) memory slots := (Option.some.inj edge).symm
      subst after
      intro slot
      exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (pushes point) bound)

theorem trace_slot_bound {σ Λ : Type*} (source : Λ → TM2.Stmt Alphabet Λ σ)
    (pushes : ∀ point,AuxWorkspace.pushes (source point)≤2)
    (trace : List (TM2.Cfg Alphabet Λ σ)) (before : TM2.Cfg Alphabet Λ σ) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step source a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ current∈trace,∀ slot,(current.stk slot).length≤bound+2*trace.length := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member slot
      have same := List.mem_singleton.mp member
      subst current
      exact (bounded slot).trans (by simp)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have nextBound := step_slot_bound source pushes before next bound edge bounded
      intro current member slot
      rcases List.mem_cons.mp member with same | later
      · subst current
        exact (bounded slot).trans (Nat.le_add_right _ _)
      · have tail := ih next (bound+2) rfl tailChain nextBound current later slot
        simp only [List.length_cons] at tail ⊢
        omega

theorem actual_base (frame : Stack → List Bool) (memory : Registers) (digits : List Bool) :
    ∃ (trace : List BaseState) (final : BaseState),
      trace.head?=some (baseState frame 0 memory (Raw.packet digits) [false] []) ∧
      trace.IsChain (fun a b => TM2.step baseProgram a=some b) ∧
      trace.getLast?=some final ∧
      final.l=some (if valueDigits digits=0 then 7 else 8) ∧
      final.stk=cells frame (Raw.packet (Raw.outputDigits digits)) [false] [] ∧
      decoded final.var=(Raw.final digits).q ∧ trace.length≤256*scale frame digits := by
  obtain ⟨native,memoryNative,left,tail,nativeFirst,nativeChain,nativeLast,nativeTime,nativeDecoded⟩ :=
    actual_native frame digits
  have nativeBound := trace_slot_bound baseProgram base_pushes native
    (baseState frame 1 default (Raw.packet digits) [false] [])
    (occupied (cells frame (Raw.packet digits) [false] [])) nativeFirst nativeChain
    (point_mass (cells frame (Raw.packet digits) [false] []))
  have nativeMember := List.mem_of_getLast? nativeLast
  have leftBound := nativeBound _ nativeMember 11
  change left.length≤occupied (cells frame (Raw.packet digits) [false] [])+2*native.length at leftBound
  have rightBound := nativeBound _ nativeMember 10
  change (Raw.packet (Raw.outputDigits digits)++tail).length≤
    occupied (cells frame (Raw.packet digits) [false] [])+2*native.length at rightBound
  simp only [List.length_append] at rightBound
  obtain ⟨normalize⟩ := actual_normalize frame memoryNative (Raw.outputDigits digits) tail left
  let nativePath : Path (baseState frame 1 default (Raw.packet digits) [false] [])
      (baseState frame 2 memoryNative (Raw.packet (Raw.outputDigits digits)++tail) left [])
      (32*(digits.length+1)+1) := ⟨native,nativeFirst,nativeChain,nativeLast,nativeTime⟩
  let enter := Path.edge (baseState frame 0 memory (Raw.packet digits) [false] [])
    (baseState frame 1 default (Raw.packet digits) [false] []) (by rfl)
  let whole := (enter.append nativePath).append normalize
  have flag : initialZero memoryNative=decide (valueDigits digits=0) := by
    unfold initialZero
    rw [nativeDecoded]
    rfl
  refine ⟨whole.trace,_,whole.first,whole.chain,whole.last,?_,rfl,?_,?_⟩
  · change some (if initialZero memoryNative then 7 else 8)=some (if valueDigits digits=0 then 7 else 8)
    rw [flag]
    simp only [decide_eq_true_eq]
  · change decoded ((false,false),memoryNative.2)=(Raw.final digits).q
    exact nativeDecoded
  · have count := whole.count
    have width := output_width digits
    have room := width_room frame digits
    dsimp only [scale] at room ⊢
    omega

theorem actual_run {C : Type*} (frame : Stack → List Bool) (memory : Store C) (digits : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry frame memory digits) ∧
      trace.IsChain (fun a b => TM2.step program a=some b) ∧ trace.getLast?=some final ∧
      final.l=some (if valueDigits digits=0 then 7 else 8) ∧ final.var.1=memory.1 ∧
      final.stk=cells frame (Raw.packet (Raw.outputDigits digits)) [false] [] ∧
      decoded final.var.2=(Raw.final digits).q ∧ trace.length≤256*scale frame digits := by
  obtain ⟨trace,final,first,chain,last,port,contents,decodedFinal,time⟩ := actual_base frame memory.2 digits
  obtain ⟨liftedFirst,liftedChain,liftedLast,liftedLength,_projected,_frames⟩ :=
    ContextLift.actual_path baseProgram memory.1 trace _ _ first chain last
  exact ⟨trace.map (ContextLift.configuration memory.1),ContextLift.configuration memory.1 final,
    liftedFirst,liftedChain,liftedLast,port,rfl,contents,decodedFinal,by rw [liftedLength]; exact time⟩

end RootB234.RuntimeCounter.Round
