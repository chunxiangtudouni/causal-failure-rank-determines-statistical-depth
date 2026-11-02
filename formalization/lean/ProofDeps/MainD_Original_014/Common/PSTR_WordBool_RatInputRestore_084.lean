module

public import Common.PSTR_WordBool_RatInputFields_083

/-! Reuse087's actual owned-sentinel return, through frozen094 labels and
static1/15 code roles. Original archive1 stays the fixed target field of
that restore-only source, and is untouched throughout this actual path. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput

open Turing PSTRWordVM RationalControllerComputation PSTRSymbolicNaturalExport

variable {C : Type*}

def restoreBackground (background : Stack → List Bool) (numerator denominator raw : List Bool) : Stack → List Bool :=
  StackIso.slots restoreRoles.symm (cells background [] [] numerator denominator raw)

theorem restore_configuration (background : Stack → List Bool) (context : C) (memory : Store) (point : Label)
    (source scratch numerator denominator raw : List Bool) :
    StackIso.configuration restoreRoles
      (PSTRSymbolicNaturalExport.state (some point) (context,memory) source scratch (background 1)
        (restoreBackground background numerator denominator raw)) =
      state background point context memory source scratch numerator denominator raw := by
  change (⟨some point,(context,memory),_⟩ : State C) = _
  congr 1
  funext other
  fin_cases other <;> rfl

def restoreTrace (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) : List (State C) :=
  (PSTRSymbolicRatExport.restoreTrace context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw)).map (StackIso.configuration restoreRoles)

theorem restore_head (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    (restoreTrace background context bit flag mode copied source scratch numerator denominator raw).head? =
      some (state background 3 context (bit,flag,mode) source (backups copied ++ true::scratch) numerator denominator raw) := by
  rw [restoreTrace,List.head?_map,PSTRSymbolicRatExport.restore_head,Option.map_some,restore_configuration]

theorem restore_last (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    (restoreTrace background context bit flag mode copied source scratch numerator denominator raw).getLast? =
      some (state background 4 context (finalBit copied bit,true,mode) (copied.reverse++source) scratch numerator denominator raw) := by
  rw [restoreTrace,List.getLast?_map,PSTRSymbolicRatExport.restore_last,Option.map_some,restore_configuration]

theorem restore_length (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    (restoreTrace background context bit flag mode copied source scratch numerator denominator raw).length = copied.length+2 := by
  rw [restoreTrace,List.length_map,PSTRSymbolicRatExport.restore_length]

theorem restore_chain (caller : Statement C) (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    (restoreTrace background context bit flag mode copied source scratch numerator denominator raw).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  let old := PSTRSymbolicRatExport.restoreTrace context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw)
  have chain := PSTRSymbolicRatExport.restore_chain context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw)
  have last := PSTRSymbolicRatExport.restore_last context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw)
  have proper := NativeMulLink.no_early_halt_port PSTRSymbolicRatExport.ratProgram 4 rfl old _ chain last rfl
  apply StackIso.chain_configuration_on restoreRoles PSTRSymbolicRatExport.ratProgram (program caller) old chain
  intro current member point selected
  have currentMember : current ∈ old := List.mem_of_mem_dropLast member
  obtain ⟨small,smallMember,rfl⟩ := List.mem_map.mp currentMember
  have labels := PSTRSymbolicRatExport.old_restore_labels context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw) small smallMember
  have different : point ≠ 4 := by intro same; subst point; exact proper _ member selected
  rcases labels with inside | done
  · have position : point = 3 := by
      change small.l.map PSTRSymbolicRatExport.restoreLabel = some point at selected
      rw [inside] at selected
      exact (Option.some.inj selected).symm
    subst point
    rfl
  · have position : point = 4 := by
      change small.l.map PSTRSymbolicRatExport.restoreLabel = some point at selected
      rw [done] at selected
      cases mode <;> exact (Option.some.inj selected).symm
    exact False.elim (different position)

theorem restore_mass_identity (background : Stack → List Bool) (numerator denominator raw : List Bool) :
    PSTRSymbolicNaturalExport.outside (restoreBackground background numerator denominator raw)+(background 1).length =
      baseMass background+numerator.length+denominator.length+raw.length := by
  simp [PSTRSymbolicNaturalExport.outside,PSTRSymbolicNaturalExport.slots,restoreBackground,StackIso.slots,
    restoreRoles,Equiv.swap_apply_def,cells,baseMass,VirtualReturn.occupiedSlots,Fin.sum_univ_succ,Nat.add_assoc]
  omega

private theorem original_restore_target (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch target : List Bool) :
    ∀ current ∈ PSTRSymbolicNaturalExport.restoreTrace context bit flag mode copied source scratch target background,
      current.stk 15 = target := by
  induction copied generalizing bit flag source with
  | nil =>
    intro current member
    simp only [PSTRSymbolicNaturalExport.restoreTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  | cons cell later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      rfl
    · exact ih cell false (cell::source) current remaining

theorem restore_frames (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ restoreTrace background context bit flag mode copied source scratch numerator denominator raw,
      current.var.1 = context ∧ ∀ slot, slot ≠ 7 → slot ≠ 15 →
        current.stk slot = cells background [] [] numerator denominator raw slot := by
  intro current member
  obtain ⟨mapped,mappedMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨small,smallMember,rfl⟩ := List.mem_map.mp mappedMember
  have bound := PSTRSymbolicNaturalExport.restore_resources context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw) small smallMember
  refine ⟨bound.1,?_⟩
  intro slot notS notT
  change small.stk (restoreRoles.symm slot) = _
  by_cases atOne : slot = 1
  · subst slot
    exact original_restore_target _ context bit flag mode copied source scratch (background 1) small smallMember
  · have fixed : restoreRoles.symm slot = slot := by
      change Equiv.swap 1 15 slot = slot
      exact Equiv.swap_apply_of_ne_of_ne atOne notT
    rw [fixed]
    have same := bound.2.1 slot atOne notS notT
    apply same.trans
    change cells background [] [] numerator denominator raw (restoreRoles slot) = _
    change cells background [] [] numerator denominator raw (Equiv.swap 1 15 slot) = _
    rw [Equiv.swap_apply_of_ne_of_ne atOne notT]

theorem restore_mass (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ restoreTrace background context bit flag mode copied source scratch numerator denominator raw,
      occupied current.stk ≤ baseMass background+source.length+2*copied.length+scratch.length+
        numerator.length+denominator.length+raw.length+1 := by
  intro current member
  obtain ⟨mapped,mappedMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨small,smallMember,rfl⟩ := List.mem_map.mp mappedMember
  have bound := PSTRSymbolicNaturalExport.restore_resources context bit flag mode copied source scratch (background 1)
    (restoreBackground background numerator denominator raw) small smallMember
  change occupied (StackIso.slots restoreRoles small.stk) ≤ _
  rw [occupied,StackIso.occupied_sum,← occupied]
  have mass : occupied small.stk ≤ PSTRSymbolicNaturalExport.outside (restoreBackground background numerator denominator raw)+
      (source.length+2*copied.length+scratch.length+(background 1).length+1) := by
    exact (IsolatedRat.occupied_eq small.stk).le.trans bound.2.2
  have identity := restore_mass_identity background numerator denominator raw
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatInput
