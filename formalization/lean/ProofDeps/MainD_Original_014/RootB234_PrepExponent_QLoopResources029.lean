module

public import RootB234_PrepExponent_QLoopUniform028

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

noncomputable def pushAllowance (C : Type*) : Nat :=
  1+Finset.univ.sup (fun point : Label => AuxWorkspace.pushes (program (C:=C) .halt point))
noncomputable def actionAllowance (C : Type*) : Nat :=
  1+Finset.univ.sup (fun point : Label => ScannerClock.actions (program (C:=C) .halt point))

theorem pushes_le (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ pushAllowance C := by
  have bound := Finset.le_sup (f:=fun point : Label => AuxWorkspace.pushes (program (C:=C) .halt point)) (Finset.mem_univ point)
  unfold pushAllowance
  omega
theorem actions_le (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ actionAllowance C := by
  have bound := Finset.le_sup (f:=fun point : Label => ScannerClock.actions (program (C:=C) .halt point)) (Finset.mem_univ point)
  unfold actionAllowance
  omega

theorem trace_space (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) (initialBound : Nat)
    (initial : ∀ slot,(before.stk slot).length ≤ initialBound) :
    ∀ current∈trace,∀ slot,(current.stk slot).length ≤ initialBound+pushAllowance C*trace.length := by
  induction trace generalizing before initialBound with
  | nil => intro current member;cases member
  | cons start rest ih =>
    have equal : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member slot
      have equal := List.mem_singleton.mp member
      subst current
      exact (initial slot).trans (Nat.le_add_right _ _)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have middle : ∀ slot,(next.stk slot).length ≤ initialBound+pushAllowance C := by
        cases before with
        | mk position memory contents =>
          cases position with
          | none => cases edge
          | some point =>
            have same : next=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
            subst next
            intro slot
            exact (AuxWorkspace.endpoint_bound _ _ _ initialBound initial slot).trans
              (Nat.add_le_add_left (pushes_le point) initialBound)
      have later := ih next rfl tailChain (initialBound+pushAllowance C) middle
      intro current member slot
      rcases List.mem_cons.mp member with rfl|tail
      · exact (initial slot).trans (Nat.le_add_right _ _)
      · exact (later current tail slot).trans_eq (by simp only [List.length_cons];ring)

noncomputable def spaceCoefficient (C : Type*) : Nat := 8+pushAllowance C*fullCoefficient+pushAllowance C
noncomputable def clockCoefficient (C : Type*) : Nat := 2*actionAllowance C*(spaceCoefficient C+1)
noncomputable def scanCoefficient (C : Type*) : Nat := fullCoefficient*clockCoefficient C
noncomputable def chargeCoefficient (C : Type*) : Nat := fullCoefficient+scanCoefficient C

noncomputable def stateClock (before : State C) : Nat :=
  before.l.elim 0 (fun point => ScannerStatement.clock (program .halt point) before.var before.stk)
noncomputable def clockSum (trace : List (State C)) : Nat := (trace.dropLast.map stateClock).sum

theorem final_mass (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) :
    RatInput.occupied
      (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []) ≤
      512*fullScale background tail budget number := by
  have width := power_field (12 : Rat) number
  rw [twelve_field] at width
  have each : ∀ slot,(bank background
      (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] [] slot).length ≤
      32*fullScale background tail budget number := by
    intro slot
    have b := bank_length background
      (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] [] slot
    rw [RatInput.Encoder.packet_length,RatInput.Encoder.packet_length] at b
    unfold fullScale
    simp only [List.length_nil] at b
    omega
  exact (RatInput.Encoder.occupied_bound _ _ each).trans_eq (by ring)

structure UniformBounds (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat)
    (trace : List (State C)) : Prop where
  count : trace.length ≤ fullCoefficient*(fullScale background tail budget number)^5
  boundaries : ∀ current∈trace,
    (∀ slot,(current.stk slot).length ≤ spaceCoefficient C*(fullScale background tail budget number)^5) ∧
    RatInput.occupied current.stk ≤ 16*spaceCoefficient C*(fullScale background tail budget number)^5
  internal : ∀ current∈trace,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length ≤ spaceCoefficient C*(fullScale background tail budget number)^5) ∧
      RatInput.occupied node.2 ≤ 16*spaceCoefficient C*(fullScale background tail budget number)^5) ∧
    ScannerStatement.clock (program .halt point) current.var current.stk ≤
      clockCoefficient C*(fullScale background tail budget number)^5
  scan : clockSum trace ≤ scanCoefficient C*(fullScale background tail budget number)^10
  charge : trace.length+clockSum trace ≤ chargeCoefficient C*(fullScale background tail budget number)^10

theorem segment_resources (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat) (final : State C)
    (part : Segment .halt
      (state default memory (bank background tail [] (RatInput.Encoder.packet budget []) [])) final)
    (count : part.trace.length ≤ fullCoefficient*(fullScale background tail budget number)^5) :
    UniformBounds background tail budget number part.trace := by
  let S := fullScale background tail budget number
  have positive : 1 ≤ S := fullScale_positive background tail budget number
  have power : S ≤ S^5 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ 5 by decide)
  have one : 1 ≤ S^5 := positive.trans power
  have initial : ∀ slot,(bank background tail [] (RatInput.Encoder.packet budget []) [] slot).length ≤ 8*S := by
    intro slot
    have b := bank_length background tail [] (RatInput.Encoder.packet budget []) [] slot
    rw [RatInput.Encoder.packet_length] at b
    simp only [List.length_nil] at b
    unfold S fullScale
    omega
  have boundary := trace_space part.trace _ part.first part.chain (8*S) initial
  have bCap : ∀ current∈part.trace,∀ slot,(current.stk slot).length ≤
      (8+pushAllowance C*fullCoefficient)*S^5 := by
    intro current member slot
    have b := boundary current member slot
    have length := Nat.mul_le_mul_left (pushAllowance C) count
    nlinarith only [b,length,power]
  have internal : ∀ current∈part.trace,∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
        (∀ slot,(node.2 slot).length ≤ spaceCoefficient C*S^5) ∧
        RatInput.occupied node.2 ≤ 16*spaceCoefficient C*S^5) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ clockCoefficient C*S^5 := by
    intro current member point _active
    have b := bCap current member
    have base : (8+pushAllowance C*fullCoefficient)*S^5+AuxWorkspace.pushes (program (C:=C) .halt point) ≤
        spaceCoefficient C*S^5 := by
      have enlarged : pushAllowance C ≤ pushAllowance C*S^5 := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (pushAllowance C) one
      have pushes := (pushes_le (C:=C) point).trans enlarged
      unfold spaceCoefficient
      nlinarith only [pushes]
    refine ⟨?_,?_⟩
    · intro node present
      have bound : ∀ slot,(node.2 slot).length ≤ spaceCoefficient C*S^5 :=
        fun slot => (AuxWorkspace.node_bound _ _ _ _ b node present slot).trans base
      exact ⟨bound,(RatInput.Encoder.occupied_bound _ _ bound).trans_eq (by ring)⟩
    · have old := ScannerClock.clock_bound (program .halt point) current.var current.stk _ b
      have args : (8+pushAllowance C*fullCoefficient)*S^5+AuxWorkspace.pushes (program (C:=C) .halt point)+1 ≤
          (spaceCoefficient C+1)*S^5 := by nlinarith only [base,one]
      exact old.trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 (actions_le point)) args).trans_eq (by
        unfold clockCoefficient;ring))
  have scan : clockSum part.trace ≤ scanCoefficient C*S^10 := by
    have caps : ∀ current∈part.trace.dropLast,stateClock current ≤ clockCoefficient C*S^5 := by
      intro current member
      cases active : current.l with
      | none => simp only [stateClock,active,Option.elim_none];exact Nat.zero_le _
      | some point => simpa only [stateClock,active,Option.elim_some] using
          (internal current (List.dropLast_subset part.trace member) point active).2
    have bounded := List.sum_le_length_nsmul (part.trace.dropLast.map stateClock) (clockCoefficient C*S^5)
      (by intro value member;obtain ⟨current,inside,rfl⟩ := List.mem_map.mp member;exact caps current inside)
    have listLength : part.trace.dropLast.length ≤ part.trace.length := by rw [List.length_dropLast];omega
    have sumBound : (part.trace.dropLast.map stateClock).sum ≤ part.trace.dropLast.length*(clockCoefficient C*S^5) := by
      simpa only [List.length_map,smul_eq_mul] using bounded
    have product := Nat.mul_le_mul_right (clockCoefficient C*S^5) (listLength.trans count)
    change (part.trace.dropLast.map stateClock).sum ≤ _
    exact sumBound.trans (product.trans_eq (by unfold scanCoefficient;ring))
  refine ⟨count,?_,internal,scan,?_⟩
  · intro current member
    have bound : ∀ slot,(current.stk slot).length ≤ spaceCoefficient C*S^5 := by
      intro slot
      have b := bCap current member slot
      unfold spaceCoefficient
      nlinarith only [b,Nat.zero_le (pushAllowance C*S^5)]
    exact ⟨bound,(RatInput.Encoder.occupied_bound _ _ bound).trans_eq (by ring)⟩
  · have powers : S^5 ≤ S^10 := Nat.pow_le_pow_right positive (by decide : 5 ≤ 10)
    have enlarged := count.trans (Nat.mul_le_mul_left fullCoefficient powers)
    unfold chargeCoefficient
    nlinarith only [enlarged,scan]

end RootB234.PrepExponent.QLoop
