module

public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Bits

/-- Untouched cells retain their actual caller value. Only actual new
assignments enter the phase catalogue; no parameter bound is assumed on
an arbitrary incoming scratch register or unrelated caller heap cell. -/
structure Sources (before after : State) (New : Cell → Prop) : Prop where
  registers : ∀ target, after.register target = before.register target ∨ New (after.register target)
  heap : ∀ address ∈ after.live,
    (address ∈ before.live ∧ after.heap address = before.heap address) ∨ New (after.heap address)
  live : ∀ address ∈ after.live, address ∈ before.live ∨ New (.natural address)
  output : after.output = before.output

theorem Sources.refl (state : State) (New : Cell → Prop) : Sources state state New :=
  ⟨fun _ => Or.inl rfl, fun _ member => Or.inl ⟨member, rfl⟩,
    fun _ member => Or.inl member, rfl⟩

theorem Sources.trans {before middle after : State} {New : Cell → Prop}
    (first : Sources before middle New) (later : Sources middle after New) : Sources before after New := by
  constructor
  · intro target
    rcases later.registers target with same | assigned
    · rcases first.registers target with old | assigned
      · exact Or.inl (same.trans old)
      · exact Or.inr (same.symm ▸ assigned)
    · exact Or.inr assigned
  · intro address member
    rcases later.heap address member with ⟨live, same⟩ | assigned
    · rcases first.heap address live with ⟨oldLive, old⟩ | assigned
      · exact Or.inl ⟨oldLive, same.trans old⟩
      · exact Or.inr (same.symm ▸ assigned)
    · exact Or.inr assigned
  · intro address member
    rcases later.live address member with live | assigned
    · exact first.live address live
    · exact Or.inr assigned
  · exact later.output.trans first.output

theorem Sources.mono {before after : State} {New Larger : Cell → Prop}
    (sources : Sources before after New) (included : ∀ value, New value → Larger value) :
    Sources before after Larger := by
  refine ⟨?_, ?_, ?_, sources.output⟩
  · intro target
    exact (sources.registers target).imp_right (included _)
  · intro address member
    exact (sources.heap address member).imp_right (included _)
  · intro address member
    exact (sources.live address member).imp_right (included _)

theorem Sources.withPC {before after : State} {New : Cell → Prop}
    (sources : Sources before after New) (position : ℕ) :
    Sources before {after with pc := position} New :=
  ⟨sources.registers, sources.heap, sources.live, sources.output⟩

theorem Sources.set (before : State) (New : Cell → Prop) (target : Register) (value : Cell)
    (assigned : New value) : Sources before (before.set target value) New := by
  refine ⟨?_, fun _ member => Or.inl ⟨member, rfl⟩, fun _ member => Or.inl member, rfl⟩
  intro register
  by_cases same : register = target
  · subst register
    exact Or.inr (by simpa only [State.set, Function.update_self] using assigned)
  · exact Or.inl (by simp only [State.set, Function.update_of_ne same])

theorem Sources.store (before : State) (New : Cell → Prop) (address : ℕ) (value : Cell)
    (assigned : New value) (addressSource : New (.natural address)) :
    Sources before
      {before with
        heap := Function.update before.heap address value
        live := insert address before.live} New := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, rfl⟩
  · intro location member
    by_cases same : location = address
    · subst location
      exact Or.inr (by simpa only [Function.update_self] using assigned)
    · exact Or.inl ⟨(Finset.mem_insert.mp member).resolve_left same,
        by simp only [Function.update_of_ne same]⟩
  · intro location member
    rcases Finset.mem_insert.mp member with same | old
    · subst location
      exact Or.inr addressSource
    · exact Or.inl old

/-- This is a transport of provenance through the frozen complete
stateCellBits constructor, not a parameter-only callee-entry premise. -/
theorem Sources.safe {before after : State} {New : Cell → Prop} {budget : ℕ}
    (sources : Sources before after New) (caller : SafeBits before budget)
    (assigned : ∀ value, New value → value.bits ≤ budget)
    (pc : natBits after.pc ≤ budget) : SafeBits after budget := by
  apply SafeBits.of_fields
  · intro target
    rcases sources.registers target with same | source
    · rw [same]
      exact caller.register target
    · exact assigned _ source
  · intro address member
    rcases sources.live address member with old | source
    · exact caller.address address old
    · have h := assigned _ source
      change 1 + natBits address ≤ budget at h
      omega
  · intro address member
    rcases sources.heap address member with ⟨live, same⟩ | source
    · rw [same]
      exact caller.heap address live
    · exact assigned _ source
  · intro value member
    rw [sources.output] at member
    exact caller.output value member
  · exact pc

end PDROC.CalibrationRow.ScatterOperands
