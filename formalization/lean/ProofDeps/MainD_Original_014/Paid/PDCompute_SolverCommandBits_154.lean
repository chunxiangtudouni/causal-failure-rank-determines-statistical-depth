module

public import Paid.PDCompute_SolverRatPrefix_153
public import Paid.PDCompute_SolverHeaderCommand_026

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)
open PDROC.CalibrationRow.Operand

theorem constantSlot_prefix_safe (input : List Cell) (before : State) (base target budget : ℕ) (value : Cell)
    (inside : target<headerWords) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (valueBits : value.bits≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+4)≤budget) : PrefixSafe input (constantSlot target value) before budget := by
  let middle:=({before with pc:=before.pc+1}).set .total value
  have firstSafe:=PrefixSafe.constant input before budget .total value safe valueBits
    ((natBits_mono (by omega : before.pc+1≤before.pc+4)).trans pcBits)
  have firstRun : linearExecute input [.constant .total value] before=some middle := rfl
  have middleSafe:=firstSafe.final firstRun
  have middleFresh : middle.register .fresh=.natural base := by simpa [middle,State.set] using fresh
  have storeSafe:=PrefixSafe.storeSlot input middle base target budget .total middleSafe middleFresh (by decide)
    ((Nat.add_le_add_left (natBits_mono (by omega : base+target≤base+headerWords)) 1).trans addressBits)
    (by simpa only [middle,State.set,Nat.add_assoc] using pcBits)
  exact PrefixSafe.append input _ _ before middle budget firstRun firstSafe storeSafe

theorem copySlot_prefix_safe (input : List Cell) (before : State) (base source target budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+6)≤budget) :
    PrefixSafe input (copySlot source target) before budget := by
  let middle:=loadSlotResult before base source .total
  have firstRun:=(header.loadSlot_execute input source .total sourceInside fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base source budget .total safe fresh (header.live source sourceInside)
    ((Nat.add_le_add_left (natBits_mono (by omega : base+source≤base+headerWords)) 1).trans addressBits)
    ((natBits_mono (by omega : before.pc+3≤before.pc+6)).trans pcBits)
  have middleSafe:=firstSafe.final firstRun
  have middleFresh : middle.register .fresh=.natural base := (loadSlotResult_fresh before base source .total (by decide)).trans fresh
  have storeSafe:=PrefixSafe.storeSlot input middle base target budget .total middleSafe middleFresh (by decide)
    ((Nat.add_le_add_left (natBits_mono (by omega : base+target≤base+headerWords)) 1).trans addressBits)
    (by simpa only [middle,loadSlotResult,Nat.add_assoc] using pcBits)
  exact PrefixSafe.append input _ _ before middle budget firstRun firstSafe storeSafe

def HeaderValueBits (values : ℕ → Cell) (budget : ℕ) : Prop := ∀ slot<headerWords,(values slot).bits≤budget

/-- Actual4/6/10-op Header commands preserve SAME caller bits. The
next-value numerical premise is about the literal evaluated scalar map;
concrete DP blocks must discharge it from original entry/cache bounds. -/
theorem HeaderCommand.prefix_safe (command : HeaderCommand) (input : List Cell) (before : State)
    (base budget : ℕ) (values next : ℕ → Cell) (valid : command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (evaluated : command.eval values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (nextBits : HeaderValueBits next budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+command.code.length)≤budget) : PrefixSafe input command.code before budget := by
  cases command with
  | constant target value =>
    have same : Function.update values target value=next := Option.some.inj evaluated
    subst next
    have valueBits : value.bits≤budget := by simpa only [Function.update_self] using nextBits target valid
    exact constantSlot_prefix_safe input before base target budget value valid fresh safe valueBits addressBits pcBits
  | copy source target =>
    exact copySlot_prefix_safe input before base source target budget values header valid.1 valid.2 fresh safe addressBits pcBits
  | rational operation left right target =>
    cases hx : values left with
    | natural x => simp [HeaderCommand.eval,hx,Cell.rat?] at evaluated
    | rational x =>
      cases hy : values right with
      | natural y => simp [HeaderCommand.eval,hx,hy,Cell.rat?] at evaluated
      | rational y =>
        have bound : ((operation.eval x y).bind fun result=>some (Function.update values target (.rational result)))=some next := by
          simpa [HeaderCommand.eval,hx,hy,Cell.rat?] using evaluated
        obtain ⟨result,computed,same⟩:=Option.bind_eq_some_iff.mp bound
        have equal : Function.update values target (.rational result)=next := Option.some.inj same
        subst next
        have resultBits : (.rational result : Cell).bits≤budget := by simpa only [Function.update_self] using nextBits target valid.2.2
        exact ratBinarySlots_prefix_safe input before base budget left right target operation x y result values header fresh valid.1 valid.2.1 valid.2.2
          hx hy computed safe resultBits addressBits pcBits

end PDCompute.Solver
