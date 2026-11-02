module

public import Structure.PSTR_HD_HeadsReadBranchSafe_100
public import Structure.PSTR_HD_HeadsUniformDispatch_080

/-! The SAME actual q0/positive dispatch witness now includes every proper
clock's true fetch/decode/access and whole-heap identity. Input access is
only original raw dimension slot1, never metadata or a new ROM field. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem containing_uniform_dispatch_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (origin q heapWords : Nat)
    (hbound : origin + (uniformDispatch origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (uniformDispatch origin).length), whole[origin + i]'(by omega) = (uniformDispatch origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hq : Fits bits q) (hraw : (rom.words .input).getD 1 0 = q)
    (hsize : 2 ≤ (rom.words .input).length) :
    ∃ steps ≤ 8,
    let after := packingRun rom whole steps state
    after.pc = (if q = 0 then BitVec.ofNat bits (5 * (origin + 39)) else BitVec.ofNat bits (5 * (origin + 8))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .value = state.register .value ∧
    after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
    after.register .index = state.register .index ∧ after.register .address = BitVec.ofNat bits 46 ∧
    (∀ clock < steps, AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
      (packingRun rom whole clock state).heap = state.heap) := by
  have lead_code : ∀ i (hi : i < (dispatchLead origin).length), whole[origin + i]'(by rw [uniformDispatch_length, dispatchLead_length] at *; omega) = (dispatchLead origin)[i] := by
    intro i hi
    have hc := hcode i (by rw [uniformDispatch_length, dispatchLead_length] at *; omega)
    change i < 4 at hi
    interval_cases i <;> exact hc
  have branch_code : whole[origin + (dispatchLead origin).length]'(by rw [uniformDispatch_length, dispatchLead_length] at *; omega) = .jumpIfZero .flag .total :=
    hcode 4 (by change 4 < 8; decide)
  have hlead := execute_dispatchLead rom origin q state hb hraw
  have h5 := fetched_conditional rom whole (dispatchLead origin) origin (origin + 39) q .flag
    (by rw [uniformDispatch_length] at hbound; rw [dispatchLead_length]; omega)
    lead_code branch_code (dispatchLead_straight origin) hwords hpcfit state hp ha hlead.1 hlead.2.1 hq
  rw [dispatchLead_length] at h5
  have safe5 (clock : Nat) (hc : clock < 5) :
      AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
        (packingRun rom whole clock state).heap = state.heap := by
    have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
    have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
    have hinput : 1 < (rom.words .input).length := by omega
    apply readonly_branch_prefix_safe rom whole (dispatchLead origin) heapWords origin .flag .total
      (by rw [uniformDispatch_length] at hbound; rw [dispatchLead_length]; omega)
      lead_code branch_code (dispatchLead_straight origin) (by simp [dispatchLead, ReadOnly])
      hwords hpcfit state hp ha ?_ clock (by rw [dispatchLead_length]; omega)
    intro count hcount
    change count < 4 at hcount
    interval_cases count <;>
      simp_all +decide [dispatchLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
        packingAccessFits, AccessFits]
  by_cases hz : q = 0
  · refine ⟨5, by omega, ?_⟩
    dsimp only
    rw [h5]
    exact ⟨by simp only [hz, ↓reduceIte], ha, rfl, rfl, rfl, rfl, rfl, rfl, safe5⟩
  · let after5 := packingRun rom whole 5 state
    have pc5 : after5.pc = BitVec.ofNat bits (5 * (origin + 5)) := by dsimp only [after5]; rw [h5]; exact ite_eq_right hz
    have halt5 : after5.halted = false := by dsimp only [after5]; rw [h5]; exact ha
    have heap5 : after5.heap = state.heap := by dsimp only [after5]; rw [h5]; rfl
    have value5 : after5.register .value = state.register .value := by dsimp only [after5]; rw [h5]; rfl
    have old5 : after5.register .old = state.register .old := by dsimp only [after5]; rw [h5]; rfl
    have fresh5 : after5.register .fresh = state.register .fresh := by dsimp only [after5]; rw [h5]; rfl
    have index5 : after5.register .index = state.register .index := by dsimp only [after5]; rw [h5]; rfl
    have addr5 : after5.register .address = BitVec.ofNat bits 46 := by dsimp only [after5]; rw [h5]; rfl
    have padding_code : ∀ i (hi : i < dispatchPadding.length), whole[(origin + 5) + i]'(by rw [uniformDispatch_length, dispatchPadding_length] at *; omega) = dispatchPadding[i] := by
      intro i hi
      have hc := hcode (5 + i) (by rw [uniformDispatch_length, dispatchPadding_length] at *; omega)
      change i < 3 at hi
      interval_cases i <;> exact hc
    have run3 := straight_segment rom whole dispatchPadding (origin + 5)
      (by rw [uniformDispatch_length] at hbound; rw [dispatchPadding_length]; omega)
      padding_code dispatchPadding_straight hwords hpcfit after5 pc5 halt5
    rw [dispatchPadding_length] at run3
    have safe8 (clock : Nat) (hc : clock < 8) :
        AtSafe rom whole heapWords (packingRun rom whole clock state) ∧
          (packingRun rom whole clock state).heap = state.heap := by
      by_cases hfirst : clock < 5
      · exact safe5 clock hfirst
      · have hclock : clock = 5 + (clock - 5) := by omega
        rw [hclock, run_add]
        have hs : PrefixOK rom heapWords (fun _ => True) dispatchPadding after5 :=
          readOnly_prefixOK rom heapWords (fun _ => True) dispatchPadding after5
            (by simp [dispatchPadding, ReadOnly]) (by
              intro count hcount
              change count < 3 at hcount
              interval_cases count <;> trivial)
        have h := straight_prefix_safe rom whole dispatchPadding heapWords (origin + 5) (fun _ => True)
          (by rw [uniformDispatch_length] at hbound; rw [dispatchPadding_length]; omega)
          padding_code dispatchPadding_straight hwords hpcfit after5 pc5 halt5 hs (clock - 5)
          (by rw [dispatchPadding_length]; omega)
        refine ⟨h.1, ?_⟩
        rw [fetched_prefix rom whole dispatchPadding (origin + 5)
          (by rw [uniformDispatch_length] at hbound; rw [dispatchPadding_length]; omega)
          padding_code dispatchPadding_straight hwords hpcfit after5 pc5 halt5 (clock - 5)
          (by rw [dispatchPadding_length]; omega)]
        exact (readOnly_prefix_heap rom dispatchPadding after5 (by simp [dispatchPadding, ReadOnly]) _).trans heap5
    refine ⟨8, le_refl _, ?_⟩
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, safe8⟩
    all_goals rw [show 8 = 5 + 3 from rfl, run_add, run3]
    · rw [ite_eq_right hz, executeOps_pc rom dispatchPadding after5 dispatchPadding_straight, pc5, BitVec.ofNat_add_ofNat]
      congr 1
    · exact halt5
    · exact heap5
    · exact value5
    · exact old5
    · exact fresh5
    · exact index5
    · exact addr5

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
