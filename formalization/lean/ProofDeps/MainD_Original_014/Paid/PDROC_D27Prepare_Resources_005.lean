module

public import Paid.PDROC_D27Prepare_Resources_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDROC.D27Prepare.Program
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

theorem StateBounds.output {H B : ℕ} {state : State} (h : StateBounds H B state)
    (source : Register) : StateBounds H B {state with output := state.output ++ [state.register source]} := by
  refine ⟨h.live, h.registers, h.heapValues, ?_⟩
  intro cell member
  rcases List.mem_append.mp member with old | added
  · exact h.outputs cell old
  · have same := List.mem_singleton.mp added
    subst cell
    exact h.registers source

theorem output_prefix_bounds (input : List Cell) (before : State) (source : Register)
    (H B : ℕ) (hbefore : StateBounds H B before) :
    LinearPrefixBounds input [.output source] before H B := by
  apply single_prefix_bounds input _ before _ H B hbefore
    ((hbefore.output source).with_pc (before.pc + 1))
  rfl

/-- Exact ceil core: numeratorAbs, denominator, quotient and remainder
are all bounded by the original rational encoding. This includes q=0. -/
theorem ceilCore_prefix_bounds (input : List Cell) (before : State)
    (source target H B : ℕ) (q : ℚ) (hbefore : StateBounds H B before)
    (fresh : before.register .fresh = .natural 0) (live : source ∈ before.live)
    (hvalue : before.heap source = .rational q) (sourceInside : source < H) (targetInside : target < H)
    (addressBits : 1 + natBits H ≤ B) (qbits : ratEncodingBits q + 1 ≤ B) :
    LinearPrefixBounds input (ceilCore source target) before H B := by
  let loaded := loadSlotResult before 0 source .total
  let numerator := ({loaded with pc := loaded.pc + 1}).set .old (.natural q.num.natAbs)
  let denominator := ({numerator with pc := numerator.pc + 1}).set .value (.natural q.den)
  let quotient := ({denominator with pc := denominator.pc + 1}).set .total (.natural (q.num.natAbs / q.den))
  let stored := storeSlotResult quotient 0 target .total
  let final := ({stored with pc := stored.pc + 1}).set .flag (.natural (q.num.natAbs % q.den))
  have numeratorBits : (Cell.natural q.num.natAbs).bits ≤ B := (numeratorAbs_cell_bits q).trans qbits
  have denominatorBits : (Cell.natural q.den).bits ≤ B := (denominator_cell_bits q).trans qbits
  have quotientBits : (Cell.natural (q.num.natAbs / q.den)).bits ≤ B :=
    (Nat.add_le_add_left (natBits_mono (Nat.div_le_self q.num.natAbs q.den)) 1).trans numeratorBits
  have remainderBits : (Cell.natural (q.num.natAbs % q.den)).bits ≤ B :=
    (Nat.add_le_add_left (natBits_mono (Nat.mod_le q.num.natAbs q.den)) 1).trans numeratorBits
  have loadExecute : linearExecute input (loadSlot source .total) before = some loaded :=
    loadSlot_execute input before 0 source .total fresh (by simpa only [Nat.zero_add] using live)
  have loadBounds := loadSlot_prefix_bounds input before source .total H B hbefore fresh live
    (address_cell_bits source H B sourceInside addressBits)
  have hl := loadBounds.final loadExecute
  have hn : StateBounds H B numerator := (hl.with_pc _).set _ _ numeratorBits
  have hd : StateBounds H B denominator := (hn.with_pc _).set _ _ denominatorBits
  have hq : StateBounds H B quotient := (hd.with_pc _).set _ _ quotientBits
  have numExecute : (Instruction.numeratorAbs .old .total).execute input loaded = some numerator := by
    simp [Instruction.execute, loaded, numerator, loadSlotResult, hvalue, State.set, Cell.rat?]
  have denExecute : (Instruction.denominator .value .total).execute input numerator = some denominator := by
    simp [Instruction.execute, loaded, numerator, denominator, loadSlotResult, hvalue, State.set, Cell.rat?]
  have quotientExecute : (Instruction.natOp .divide .total .old .value).execute input denominator = some quotient := by
    apply PDMenu.ComputeFrame.execute_natOp .divide .total .old .value input denominator q.num.natAbs q.den (q.num.natAbs / q.den)
    · simp [denominator, numerator, State.set]
    · simp [denominator, State.set]
    · simp only [NatOp.eval, q.den_nz, ↓reduceIte]
  have calculations : LinearPrefixBounds input
      [.numeratorAbs .old .total, .denominator .value .total, .natOp .divide .total .old .value] loaded H B :=
    LinearPrefixBounds.cons input _ _ loaded numerator H B hl numExecute
      (LinearPrefixBounds.cons input _ _ numerator denominator H B hn denExecute
        (single_prefix_bounds input _ denominator quotient H B hd hq quotientExecute))
  have calculationsExecute : linearExecute input
      (loadSlot source .total ++ [.numeratorAbs .old .total, .denominator .value .total,
        .natOp .divide .total .old .value]) before = some quotient := by
    rw [linearExecute_append, loadExecute, Option.bind_some]
    simp only [linearExecute, numExecute, denExecute, quotientExecute, Option.bind_some]
  have firstBounds := LinearPrefixBounds.append input _ _ before loaded H B loadExecute loadBounds calculations
  have quotientFresh : quotient.register .fresh = .natural 0 := by
    simpa [quotient, denominator, numerator, loaded, State.set, loadSlotResult] using fresh
  have storeExecute : linearExecute input (storeSlot target .total) quotient = some stored :=
    storeSlot_execute input quotient 0 target .total quotientFresh (by decide)
  have storeBounds := storeSlot_prefix_bounds input quotient target .total H B hq quotientFresh
    targetInside (by decide) (address_cell_bits target H B targetInside addressBits)
  have hs := storeBounds.final storeExecute
  have hf : StateBounds H B final := (hs.with_pc _).set _ _ remainderBits
  have modExecute : (Instruction.natOp .modulo .flag .old .value).execute input stored = some final := by
    apply PDMenu.ComputeFrame.execute_natOp .modulo .flag .old .value input stored q.num.natAbs q.den (q.num.natAbs % q.den)
    · simp [stored, quotient, denominator, numerator, storeSlotResult, State.set]
    · simp [stored, quotient, denominator, storeSlotResult, State.set]
    · simp only [NatOp.eval, q.den_nz, ↓reduceIte]
  have modBounds := single_prefix_bounds input _ stored final H B hs hf modExecute
  have beforeModExecute : linearExecute input
      (loadSlot source .total ++ [.numeratorAbs .old .total, .denominator .value .total,
        .natOp .divide .total .old .value] ++ storeSlot target .total) before = some stored := by
    rw [linearExecute_append, calculationsExecute, Option.bind_some, storeExecute]
  have beforeModBounds := LinearPrefixBounds.append input _ _ before quotient H B calculationsExecute firstBounds storeBounds
  exact LinearPrefixBounds.append input _ _ before stored H B beforeModExecute beforeModBounds modBounds

end PDROC.D27Prepare.Resources
