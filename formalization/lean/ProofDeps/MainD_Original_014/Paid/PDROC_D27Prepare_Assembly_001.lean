module

public import Paid.PDROC_D27Prepare_Search_004
public import Paid.PDROC_D27Prepare_Resources_016
public import Paid.PDROC_D27Prepare_Prefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

theorem raw_of_slots (P : Parameters) (fee : ℚ) (before after : State)
    (raw : Search.RawConstants P fee before)
    (fresh : after.register .fresh = before.register .fresh)
    (carry : ∀ address, address < 6 ∨ (13 ≤ address ∧ address ≤ 21) → ∀ value,
      Search.SlotHas before address value → Search.SlotHas after address value) : Search.RawConstants P fee after :=
  ⟨fresh.trans raw.fresh,
    carry 0 (by decide) _ raw.stages, carry 1 (by decide) _ raw.tools,
    carry 2 (by decide) _ raw.gamma, carry 3 (by decide) _ raw.risk,
    carry 4 (by decide) _ raw.reviewFee, carry 5 (by decide) _ raw.feeValue,
    carry 13 (by decide) _ raw.natZero, carry 14 (by decide) _ raw.natOne,
    carry 15 (by decide) _ raw.natTwo, carry 16 (by decide) _ raw.ratZero,
    carry 17 (by decide) _ raw.ratOne, carry 18 (by decide) _ raw.ratTwo,
    carry 19 (by decide) _ raw.ratThree, carry 20 (by decide) _ raw.ratFour,
    carry 21 (by decide) _ raw.ratHalf⟩

/-- Actual heap cells, not an already-emitted prepared13 input vector. -/
def PreparedMemory (P : Parameters) (fee : ℚ) (state : State) : Prop :=
  ∀ address value, (preparedInput P fee)[address]? = some value → Search.SlotHas state address value

structure PreFinalState (P : Parameters) (fee : ℚ) (state : State) : Prop where
  location : state.pc = pc 45
  output : state.output = []
  fresh : state.register .fresh = .natural 0
  cells : PreparedMemory P fee state
  bounded : StateBounds 64 (operandBudget P fee) state

theorem preparedMemory_of_fields (P : Parameters) (fee : ℚ) (state : State)
    (raw : Search.RawConstants P fee state)
    (t0 : Search.SlotHas state 6 (.natural P.certificate.t0))
    (M : Search.SlotHas state 7 (.natural P.certificate.M))
    (E : Search.SlotHas state 8 (.natural P.certificate.E))
    (Q : Search.SlotHas state 9 (.natural P.certificate.Q))
    (J : Search.SlotHas state 10 (.natural (P.bisectionBudget fee)))
    (lambda : Search.SlotHas state 11 (.rational P.Lambda))
    (zeta : Search.SlotHas state 12 (.rational (P.zeroChargeRisk fee))) : PreparedMemory P fee state := by
  intro address value fetched
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp fetched
  have length : (preparedInput P fee).length = 13 := rfl
  have bound : address < 13 := by simpa only [length] using inside
  interval_cases address <;> simp [preparedInput, rawInput] at fetched <;> subst value
  · exact raw.stages
  · exact raw.tools
  · exact raw.gamma
  · exact raw.risk
  · exact raw.reviewFee
  · exact raw.feeValue
  · exact t0
  · exact M
  · exact E
  · exact Q
  · exact J
  · exact lambda
  · exact zeta

theorem PreparedMemory.live (P : Parameters) (fee : ℚ) (state : State) (cells : PreparedMemory P fee state)
    (address : ℕ) (inside : address < 13) : address ∈ state.live := by
  have inList : address < (preparedInput P fee).length := by simpa only [show (preparedInput P fee).length = 13 from rfl] using inside
  exact (cells address _ (List.getElem?_eq_getElem inList)).1

theorem PreparedMemory.row (P : Parameters) (fee : ℚ) (state : State) (cells : PreparedMemory P fee state) :
    (List.range 13).map state.heap = preparedInput P fee := by
  have h0 := (cells 0 _ (by rfl)).2
  have h1 := (cells 1 _ (by rfl)).2
  have h2 := (cells 2 _ (by rfl)).2
  have h3 := (cells 3 _ (by rfl)).2
  have h4 := (cells 4 _ (by rfl)).2
  have h5 := (cells 5 _ (by rfl)).2
  have h6 := (cells 6 _ (by rfl)).2
  have h7 := (cells 7 _ (by rfl)).2
  have h8 := (cells 8 _ (by rfl)).2
  have h9 := (cells 9 _ (by rfl)).2
  have h10 := (cells 10 _ (by rfl)).2
  have h11 := (cells 11 _ (by rfl)).2
  have h12 := (cells 12 _ (by rfl)).2
  change [state.heap 0, state.heap 1, state.heap 2, state.heap 3, state.heap 4, state.heap 5,
    state.heap 6, state.heap 7, state.heap 8, state.heap 9, state.heap 10, state.heap 11, state.heap 12] = _
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  rfl

end PDROC.D27Prepare.Assembly
