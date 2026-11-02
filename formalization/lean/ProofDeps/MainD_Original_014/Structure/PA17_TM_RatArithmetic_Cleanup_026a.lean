module
public import Structure.PA17_TM_RatArithmetic_Parse_002g

/-! Erase actual data/TRUE-flag pairs and their END cell. The second OWN
FALSE is genuinely read at label2 and left untouched. No width or EOF answer
is supplied to this fixed four-label program. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCleanup026

open Turing

def fieldEraseMachine : Machine 3 := fun q symbol =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | 2 => if symbol then some (3,.write false) else none
  | _ => some (0,.move .right)

def fieldState (q : Fin 4) (left right : List Bool) : MachineState 3 :=
  ⟨q,Tape.mk₂ left right⟩

def fieldTrace (archive : List Bool) : List Bool → List Bool → List (MachineState 3)
  | [],suffix =>
    [fieldState 0 archive (false::false::suffix),
     fieldState 1 archive (false::false::suffix),
     fieldState 2 (false::archive) (false::suffix)]
  | bit::later,suffix =>
    let tail := PSTRTMIncrement009.blocks later++false::false::suffix
    [fieldState 0 archive (bit::true::tail),
     fieldState 1 archive (false::true::tail),
     fieldState 2 (false::archive) (true::tail),
     fieldState 3 (false::archive) (false::tail)] ++
      fieldTrace (false::false::archive) later suffix

def fieldFinal (archive digits suffix : List Bool) : MachineState 3 :=
  fieldState 2 (List.replicate (2*digits.length+1) false++archive) (false::suffix)

theorem fieldTrace_head (archive digits suffix : List Bool) :
    (fieldTrace archive digits suffix).head? =
      some (fieldState 0 archive (PSTRTMIncrement009.blocks digits++false::false::suffix)) := by
  cases digits <;> rfl

private theorem zeros_append_two (k : Nat) (archive : List Bool) :
    List.replicate k false++false::false::archive = List.replicate (k+2) false++archive := by
  rw [List.replicate_add]
  simp [List.replicate_succ,List.append_assoc]

theorem fieldTrace_last (archive digits suffix : List Bool) :
    (fieldTrace archive digits suffix).getLast? = some (fieldFinal archive digits suffix) := by
  induction digits generalizing archive with
  | nil => rfl
  | cons bit later ih =>
    rw [fieldTrace,List.getLast?_append,ih,Option.some_or]
    simp only [fieldFinal]
    have hn : (2*later.length+1)+2 = 2*(bit::later).length+1 := by
      simp only [List.length_cons]
      omega
    rw [zeros_append_two,hn]

theorem fieldTrace_chain (archive digits suffix : List Bool) :
    (fieldTrace archive digits suffix).IsChain
      (fun before after => TM0.step fieldEraseMachine before = some after) := by
  induction digits generalizing archive with
  | nil =>
    simp [fieldTrace,List.isChain_cons_cons,TM0.step,fieldEraseMachine,fieldState,Tape.mk₂]
  | cons bit later ih =>
    let tail := PSTRTMIncrement009.blocks later++false::false::suffix
    let front := [fieldState 0 archive (bit::true::tail),
      fieldState 1 archive (false::true::tail),
      fieldState 2 (false::archive) (true::tail),
      fieldState 3 (false::archive) (false::tail)]
    have hf : front.IsChain (fun before after => TM0.step fieldEraseMachine before = some after) := by
      simp [front,List.isChain_cons_cons,TM0.step,fieldEraseMachine,fieldState,Tape.mk₂]
    change (front++fieldTrace (false::false::archive) later suffix).IsChain _
    apply hf.append (ih (false::false::archive))
    intro before hb after ha
    have hl : front.getLast? = some (fieldState 3 (false::archive) (false::tail)) := rfl
    rw [hl] at hb
    rw [fieldTrace_head] at ha
    simp only [Option.mem_some_iff] at hb ha
    subst before
    subst after
    simp [tail,TM0.step,fieldEraseMachine,fieldState,Tape.mk₂]

theorem fieldFinal_halt (archive digits suffix : List Bool) :
    TM0.step fieldEraseMachine (fieldFinal archive digits suffix) = none := by
  simp [TM0.step,fieldEraseMachine,fieldFinal,fieldState,Tape.mk₂]

/-- Includes internal empty fields. A canonical Nat0 has one actual FALSE
payload bit; it is not represented by the empty-field case. -/
theorem field_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom fieldEraseMachine
      (fieldState 0 archive (PSTRTMIncrement009.blocks digits++false::false::suffix))
      (fieldTrace archive digits suffix) (fieldFinal archive digits suffix) :=
  ⟨fieldTrace_head archive digits suffix,fieldTrace_chain archive digits suffix,
    fieldTrace_last archive digits suffix,fieldFinal_halt archive digits suffix⟩

theorem field_final_tape (archive digits suffix : List Bool) :
    (fieldFinal archive digits suffix).Tape =
      Tape.mk₂ (List.replicate (2*digits.length+1) false++archive) (false::suffix) := rfl

theorem fieldTrace_length (archive digits suffix : List Bool) :
    (fieldTrace archive digits suffix).length = 4*digits.length+3 := by
  induction digits generalizing archive with
  | nil => rfl
  | cons bit later ih =>
    rw [fieldTrace,List.length_append,ih]
    change 4+(4*later.length+3) = 4*(bit::later).length+3
    simp only [List.length_cons]
    omega

theorem field_prefix_space (archive digits suffix : List Bool) (prefixLength chargedLength : Nat) :
    visitedSpace fieldEraseMachine chargedLength ((fieldTrace archive digits suffix).take prefixLength) ≤
      chargedLength+8*digits.length+7 := by
  have hs := PSTRTMTrace002.visitedSpace_le fieldEraseMachine chargedLength
    ((fieldTrace archive digits suffix).take prefixLength)
  have ht := fieldTrace_length archive digits suffix
  have hp : ((fieldTrace archive digits suffix).take prefixLength).length ≤
      (fieldTrace archive digits suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCleanup026
