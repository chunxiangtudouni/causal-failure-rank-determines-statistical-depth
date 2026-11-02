module

public import RootB234_PrepExponent_GlobalRun040

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def resourceScale (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat :=
  RatInput.occupied background+tail.length+RatInput.Encoder.fieldSize budget+number+targetExponent budget number+1

theorem resourceScale_positive (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) :
    1≤resourceScale background tail budget number := by unfold resourceScale;omega

noncomputable def pushAllowance (C : Type*) : Nat :=
  1+Finset.univ.sup (fun point : Label => AuxWorkspace.pushes (program (C:=C) .halt point))
noncomputable def actionAllowance (C : Type*) : Nat :=
  1+Finset.univ.sup (fun point : Label => ScannerClock.actions (program (C:=C) .halt point))

theorem pushes_le (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤pushAllowance C := by
  have cap := Finset.le_sup (f:=fun point : Label => AuxWorkspace.pushes (program (C:=C) .halt point)) (Finset.mem_univ point)
  unfold pushAllowance
  omega
theorem actions_le (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤actionAllowance C := by
  have cap := Finset.le_sup (f:=fun point : Label => ScannerClock.actions (program (C:=C) .halt point)) (Finset.mem_univ point)
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

noncomputable def spaceCoefficient (C : Type*) (time : Nat) : Nat := 8+pushAllowance C*time+pushAllowance C
noncomputable def clockCoefficient (C : Type*) (time : Nat) : Nat := 2*actionAllowance C*(spaceCoefficient C time+1)
noncomputable def scanCoefficient (C : Type*) (time : Nat) : Nat := time*clockCoefficient C time
noncomputable def chargeCoefficient (C : Type*) (time : Nat) : Nat := time+scanCoefficient C time

noncomputable def stateClock (before : State C) : Nat :=
  before.l.elim 0 (fun point => ScannerStatement.clock (program .halt point) before.var before.stk)
noncomputable def clockSum (trace : List (State C)) : Nat := (trace.dropLast.map stateClock).sum

structure PolynomialBounds (coefficient degree scale : Nat) (trace : List (State C)) : Prop where
  count : trace.length≤coefficient*scale^degree
  boundaries : ∀ current∈trace,
    (∀ slot,(current.stk slot).length≤spaceCoefficient C coefficient*scale^degree) ∧
    RatInput.occupied current.stk≤16*spaceCoefficient C coefficient*scale^degree
  internal : ∀ current∈trace,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤spaceCoefficient C coefficient*scale^degree) ∧
      RatInput.occupied node.2≤16*spaceCoefficient C coefficient*scale^degree) ∧
    ScannerStatement.clock (program .halt point) current.var current.stk≤clockCoefficient C coefficient*scale^degree
  scan : clockSum trace≤scanCoefficient C coefficient*scale^(2*degree)
  charge : trace.length+clockSum trace≤chargeCoefficient C coefficient*scale^(2*degree)

/-- Attach whole-bank, primitive-internal and scanner certificates to
ANY already-constructed actual path. No second execution witness is chosen. -/
theorem resources_of_cap (before final : State C) (part : Segment .halt before final)
    (coefficient degree scale : Nat) (scalePositive : 1≤scale) (degreePositive : 1≤degree)
    (initial : ∀ slot,(before.stk slot).length≤8*scale)
    (count : part.trace.length≤coefficient*scale^degree) :
    PolynomialBounds coefficient degree scale part.trace := by
  have power : scale≤scale^degree := by
    simpa only [pow_one] using Nat.pow_le_pow_right scalePositive degreePositive
  have one : 1≤scale^degree := scalePositive.trans power
  have boundary := trace_space part.trace before part.first part.chain (8*scale) initial
  have bCap : ∀ current∈part.trace,∀ slot,(current.stk slot).length≤
      (8+pushAllowance C*coefficient)*scale^degree := by
    intro current member slot
    have b := boundary current member slot
    have length := Nat.mul_le_mul_left (pushAllowance C) count
    nlinarith only [b,length,power]
  have internal : ∀ current∈part.trace,∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
        (∀ slot,(node.2 slot).length≤spaceCoefficient C coefficient*scale^degree) ∧
        RatInput.occupied node.2≤16*spaceCoefficient C coefficient*scale^degree) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤clockCoefficient C coefficient*scale^degree := by
    intro current member point _active
    have b := bCap current member
    have base : (8+pushAllowance C*coefficient)*scale^degree+AuxWorkspace.pushes (program (C:=C) .halt point)≤
        spaceCoefficient C coefficient*scale^degree := by
      have enlarged : pushAllowance C≤pushAllowance C*scale^degree := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (pushAllowance C) one
      have pushes := (pushes_le (C:=C) point).trans enlarged
      unfold spaceCoefficient
      nlinarith only [pushes]
    refine ⟨?_,?_⟩
    · intro node present
      have bound : ∀ slot,(node.2 slot).length≤spaceCoefficient C coefficient*scale^degree :=
        fun slot => (AuxWorkspace.node_bound _ _ _ _ b node present slot).trans base
      exact ⟨bound,(RatInput.Encoder.occupied_bound _ _ bound).trans_eq (by ring)⟩
    · have old := ScannerClock.clock_bound (program .halt point) current.var current.stk _ b
      have args : (8+pushAllowance C*coefficient)*scale^degree+AuxWorkspace.pushes (program (C:=C) .halt point)+1≤
          (spaceCoefficient C coefficient+1)*scale^degree := by nlinarith only [base,one]
      exact old.trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 (actions_le point)) args).trans_eq (by
        unfold clockCoefficient;ring))
  have scan : clockSum part.trace≤scanCoefficient C coefficient*scale^(2*degree) := by
    have caps : ∀ current∈part.trace.dropLast,stateClock current≤clockCoefficient C coefficient*scale^degree := by
      intro current member
      cases active : current.l with
      | none => simp only [stateClock,active,Option.elim_none];exact Nat.zero_le _
      | some point => simpa only [stateClock,active,Option.elim_some] using
          (internal current (List.dropLast_subset part.trace member) point active).2
    have bounded := List.sum_le_length_nsmul (part.trace.dropLast.map stateClock) (clockCoefficient C coefficient*scale^degree)
      (by intro value member;obtain ⟨current,inside,rfl⟩ := List.mem_map.mp member;exact caps current inside)
    have listLength : part.trace.dropLast.length≤part.trace.length := by rw [List.length_dropLast];omega
    have sumBound : (part.trace.dropLast.map stateClock).sum≤part.trace.dropLast.length*(clockCoefficient C coefficient*scale^degree) := by
      simpa only [List.length_map,smul_eq_mul] using bounded
    have product := Nat.mul_le_mul_right (clockCoefficient C coefficient*scale^degree) (listLength.trans count)
    have square : scale^degree*scale^degree=scale^(2*degree) := by rw [←pow_add];congr 1;omega
    have equal : coefficient*scale^degree*(clockCoefficient C coefficient*scale^degree)=
        scanCoefficient C coefficient*scale^(2*degree) := by
      calc
        _=(coefficient*clockCoefficient C coefficient)*(scale^degree*scale^degree) := by ring
        _=_ := by rw [square];rfl
    exact sumBound.trans (product.trans_eq equal)
  refine ⟨count,?_,internal,scan,?_⟩
  · intro current member
    have bound : ∀ slot,(current.stk slot).length≤spaceCoefficient C coefficient*scale^degree := by
      intro slot
      have b := bCap current member slot
      unfold spaceCoefficient
      nlinarith only [b,Nat.zero_le (pushAllowance C*scale^degree)]
    exact ⟨bound,(RatInput.Encoder.occupied_bound _ _ bound).trans_eq (by ring)⟩
  · have powers : scale^degree≤scale^(2*degree) := Nat.pow_le_pow_right scalePositive (by omega : degree≤2*degree)
    have enlarged := count.trans (Nat.mul_le_mul_left coefficient powers)
    unfold chargeCoefficient
    nlinarith only [enlarged,scan]

theorem original_entry_cap (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) :
    ∀ slot,(QLoop.bank background tail [] (RatInput.Encoder.packet budget []) [] slot).length≤
      8*resourceScale background tail budget number := by
  intro slot
  have b := QLoop.bank_length background tail [] (RatInput.Encoder.packet budget []) [] slot
  rw [RatInput.Encoder.packet_length] at b
  simp only [List.length_nil] at b
  unfold resourceScale
  omega

theorem original_resources_of_cap (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat) (final : State C)
    (part : Segment .halt (state default memory (QLoop.bank background tail [] (RatInput.Encoder.packet budget []) [])) final)
    (coefficient degree : Nat) (degreePositive : 1≤degree)
    (count : part.trace.length≤coefficient*(resourceScale background tail budget number)^degree) :
    PolynomialBounds coefficient degree (resourceScale background tail budget number) part.trace :=
  resources_of_cap _ _ part coefficient degree _ (resourceScale_positive background tail budget number) degreePositive
    (original_entry_cap background tail budget number) count

end RootB234.PrepExponent.Global
