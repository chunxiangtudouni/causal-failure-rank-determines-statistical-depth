module

public import Paid.PDROC_BitVM_Codec_NatWriter_Global_005
public import Paid.PDROC_BitVM_Kernel_NatMarshal_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.RatMarshal

open Turing PDROC.BitVM.Native

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 18
abbrev Store := Option Bool × Bool
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store
abbrev Register := PaperProofs.Paid.Computation.Register

def tempSlot (temp : Fin 7) : Stack := ⟨25 + temp.val, by omega⟩

theorem tempSlot_bounds (temp : Fin 7) : 25 ≤ (tempSlot temp).val := by
  change 25 ≤ 25 + temp.val
  omega

theorem tempSlot_injective : Function.Injective tempSlot := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  change 25 + left.val = 25 + right.val at values
  omega

theorem temp_not_right (temp : Fin 7) : tempSlot temp ≠ 0 := by
  intro same
  have value := congrArg Fin.val same
  have bound := tempSlot_bounds temp
  change (tempSlot temp).val = 0 at value
  omega

theorem temp_not_left (temp : Fin 7) : tempSlot temp ≠ 24 := by
  intro same
  have value := congrArg Fin.val same
  have bound := tempSlot_bounds temp
  change (tempSlot temp).val = 24 at value
  omega

def headerEmbedding (temp : Fin 7) : PDROC.BitVM.Log.Header.Stack ↪ Stack :=
  NatWriter.headerRoles.trans
    (NatWriter.Global.embedding (tempSlot temp) (temp_not_right temp) (temp_not_left temp))

/-- The unused role0 of the numerator drain is the already-cleared
denominator destination. Native-right still contains the real denominator
and is outside this call; no extra empty temporary is needed. -/
def numeratorDrainEmbedding (num den : Fin 7) (different : num ≠ den) : NatWriter.Stack ↪ Stack where
  toFun := fun role => if role = 0 then tempSlot den else if role = 1 then 24 else tempSlot num
  inj' := by
    intro left right equal
    have unequal : tempSlot num ≠ tempSlot den :=
      fun same => different (tempSlot_injective same)
    have numNotLeft := temp_not_left num
    have denNotLeft := temp_not_left den
    fin_cases left <;> fin_cases right <;> simp_all

def denominatorDrainEmbedding (den : Fin 7) : NatWriter.Stack ↪ Stack :=
  NatWriter.Global.embedding (tempSlot den) (temp_not_right den) (temp_not_left den)

def copyLabels (label : PDROC.BitVM.Log.TwoStack.Label) : Label := ⟨1 + label.val, by omega⟩
def numeratorLabels (label : PDROC.BitVM.Log.Header.Label) : Label := ⟨7 + label.val, by omega⟩
def denominatorLabels (label : PDROC.BitVM.Log.Header.Label) : Label := ⟨12 + label.val, by omega⟩

/-- TRUE tag and sign are actual Option Bool reads. Missing sign is not
silently treated as FALSE. Only the read sign survives as finite control. -/
def tagCode : Statement :=
  .pop 0 (fun saved symbol => (symbol, saved.2))
    (.branch (fun saved => saved.1 == some true)
      (.pop 0 (fun saved symbol => (symbol, saved.2))
        (.branch (fun saved => saved.1.isSome)
          (.load (fun saved => (none, saved.1.getD false)) (.goto (fun _ => 7))) .halt)) .halt)

/-- One fixed Bool machine: copy the complete source Cell, then clear
both old destinations, read real tag/sign, scan numerator and denominator,
and really write both natural tags. No Rat, Nat value or width is control. -/
def program (source : Register) (num den : Fin 7) (different : num ≠ den)
    (label : Label) : Statement :=
  if label = 0 then .load (fun _ => (none, false)) (.goto (fun _ => 1))
  else if small : label.val < 4 then
    Inline.statement copyLabels 4 (Lift.statement (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source)
      (Copy.program ⟨label.val - 1, by omega⟩))
  else if label = 4 then Inline.statement (fun _ : Unit => 4) 5
    (PDROC.BitVM.Kernel.Clear.program (tempSlot num) ())
  else if label = 5 then Inline.statement (fun _ : Unit => 5) 6
    (PDROC.BitVM.Kernel.Clear.program (tempSlot den) ())
  else if label = 6 then tagCode
  else if small : label.val < 11 then
    Inline.statement numeratorLabels 11 (Lift.statement (headerEmbedding num)
      (PDROC.BitVM.Log.Header.program ⟨label.val - 7, by omega⟩))
  else if label = 11 then Inline.statement (fun _ : Unit => 11) 12
    (Lift.statement (numeratorDrainEmbedding num den different) (NatWriter.drainProgram ()))
  else if small : label.val < 16 then
    Inline.statement denominatorLabels 16 (Lift.statement (headerEmbedding den)
      (PDROC.BitVM.Log.Header.program ⟨label.val - 12, by omega⟩))
  else if label = 16 then Inline.statement (fun _ : Unit => 16) 17
    (Lift.statement (denominatorDrainEmbedding den) (NatWriter.drainProgram ()))
  else .halt

theorem copy_agrees (source : Register) (num den : Fin 7) (different : num ≠ den)
    (label : PDROC.BitVM.Log.TwoStack.Label) : program source num den different (copyLabels label) =
      Inline.statement copyLabels 4
        (Lift.machine (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source) Copy.program label) := by
  fin_cases label <;> rfl

theorem clear_num_agrees (source : Register) (num den : Fin 7) (different : num ≠ den) (label : Unit) :
    program source num den different 4 = Inline.statement (fun _ : Unit => 4) 5
      (PDROC.BitVM.Kernel.Clear.program (tempSlot num) label) := by
  cases label
  rfl

theorem clear_den_agrees (source : Register) (num den : Fin 7) (different : num ≠ den) (label : Unit) :
    program source num den different 5 = Inline.statement (fun _ : Unit => 5) 6
      (PDROC.BitVM.Kernel.Clear.program (tempSlot den) label) := by
  cases label
  rfl

theorem numerator_agrees (source : Register) (num den : Fin 7) (different : num ≠ den)
    (label : PDROC.BitVM.Log.Header.Label) : program source num den different (numeratorLabels label) =
      Inline.statement numeratorLabels 11
        (Lift.machine (headerEmbedding num) PDROC.BitVM.Log.Header.program label) := by
  fin_cases label <;> rfl

theorem drain_num_agrees (source : Register) (num den : Fin 7) (different : num ≠ den) (label : Unit) :
    program source num den different 11 = Inline.statement (fun _ : Unit => 11) 12
      (Lift.machine (numeratorDrainEmbedding num den different) NatWriter.drainProgram label) := by
  cases label
  rfl

theorem denominator_agrees (source : Register) (num den : Fin 7) (different : num ≠ den)
    (label : PDROC.BitVM.Log.Header.Label) : program source num den different (denominatorLabels label) =
      Inline.statement denominatorLabels 16
        (Lift.machine (headerEmbedding den) PDROC.BitVM.Log.Header.program label) := by
  fin_cases label <;> rfl

theorem drain_den_agrees (source : Register) (num den : Fin 7) (different : num ≠ den) (label : Unit) :
    program source num den different 16 = Inline.statement (fun _ : Unit => 16) 17
      (Lift.machine (denominatorDrainEmbedding den) NatWriter.drainProgram label) := by
  cases label
  rfl

theorem supports (source : Register) (num den : Fin 7) (different : num ≠ den) :
    TM2.Supports (program source num den different) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program source num den different label)⟩

end PDROC.BitVM.Codec.RatMarshal
