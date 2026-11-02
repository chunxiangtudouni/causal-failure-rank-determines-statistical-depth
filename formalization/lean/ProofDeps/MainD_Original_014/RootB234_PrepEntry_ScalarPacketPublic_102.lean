module

public import RootB234_PrepEntry_ScalarPacketResources_101

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.ScalarPacket
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep
variable {C : Type*}

private theorem source_mass (point : Label) (background : RatInput.Stack→List Bool)
    (context : C) (memory : RatOutput.Store) (source : List Bool) :
    source.length ≤ inputMass (state point context memory background source) := by
  simpa only [inputMass,state,bank,Function.update_self] using
    RatInput.Encoder.point_mass (bank background source) 15

theorem natural_with_bounds (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (tail : List Bool) :
    ∃ part : Path .halt (state .natural context memory background (NatField.packet number tail))
      (state .done context (true,false) background tail) ((PSTRTMNatValue017.rawPayload number).length+4),
      Bounds (state .natural context memory background (NatField.packet number tail)) part.trace := by
  obtain ⟨part,_⟩:=natural_actual .halt background context memory number tail
  refine ⟨part,certify part rfl ?_⟩
  have mass:=source_mass .natural background context memory (NatField.packet number tail)
  rw [RootB234.ECost.natural_packet_length] at mass
  have count:=part.count
  unfold inputScale
  change 2*(PSTRTMNatValue017.rawPayload number).length+2+tail.length≤_ at mass
  omega

theorem rational_with_bounds (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (value : Rat) (tail : List Bool) :
    ∃ part : Path .halt (state .rational context memory background (RatInput.Encoder.packet value tail))
      (state .done context (true,false) background tail) (RatInput.Encoder.fieldSize value+6),
      Bounds (state .rational context memory background (RatInput.Encoder.packet value tail)) part.trace := by
  obtain ⟨part,_⟩:=rational_actual .halt background context memory value tail
  refine ⟨part,certify part rfl ?_⟩
  have mass:=source_mass .rational background context memory (RatInput.Encoder.packet value tail)
  rw [RatInput.Encoder.packet_length] at mass
  have count:=part.count
  unfold inputScale
  omega

theorem sign_with_bounds (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (value : Rat) (tail : List Bool) :
    ∃ part : Path .halt (state .sign context memory background (RatInput.Encoder.packet value tail))
      (state .done context (true,PA17TMRatArithmeticParse002.sign value) background
        (RatInput.Encoder.packet value tail)) 2,
      Bounds (state .sign context memory background (RatInput.Encoder.packet value tail)) part.trace := by
  obtain ⟨part,_⟩:=sign_actual .halt background context memory value tail
  refine ⟨part,certify part rfl ?_⟩
  have count:=part.count
  unfold inputScale
  omega

theorem actual_path_on {Λ : Type*} (mapping : Label→Λ)
    (code : Λ→TM2.Stmt RatInput.Alphabet Λ (Store C))
    {before final : State C} {bound : Nat} (part : Path .halt before final bound)
    (facts : Bounds before part.trace)
    (same : ∀ point,point≠.done→code (mapping point)=LabelMap.statement mapping (program .halt point)) :
    (part.trace.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping before) ∧
    (part.trace.map (LabelMap.configuration mapping)).IsChain (fun a b=>TM2.step code a=some b) ∧
    (part.trace.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) := by
  have result:=LabelMap.actual_path_on mapping (program .halt) code part.trace before final
    part.first part.chain part.last (by
      intro current member point selected
      apply same point
      intro equal
      subst point
      exact facts.proper current member selected)
  exact ⟨result.1,result.2.1,result.2.2.1⟩

end RootB234.PrepEntry.ScalarPacket
