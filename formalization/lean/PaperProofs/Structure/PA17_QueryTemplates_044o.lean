module
public import PaperProofs.Structure.PA17_QueryTemplates_044n
public import PaperProofs.Structure.PA17_UniformGenerator_035ae

/-! Every literal of the actual complete finite generator: logarithm
prelude, measured streams, patch instructions, and hardware final copy. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044o
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035g PA17UniformGenerator035i
  PA17UniformGenerator035k PA17UniformGenerator035o PA17UniformGenerator035y PA17UniformGenerator035ac
  PA17UniformGenerator035ae PA17QueryTemplates044n

@[instance_reducible] def constantDec (B : Nat) : (op : PackingOp) → Decidable (ConstantLE B op)
  | .base (.base (.constant _ value)) => by change Decidable (value ≤ B); infer_instance
  | .base (.base (.add _ _ _)) | .base (.base (.minimum _ _ _)) | .base (.base (.select _ _ _ _))
  | .base (.base (.loadROM _ _ _)) | .base (.base (.loadHeap _ _)) | .base (.base (.storeHeap _ _))
  | .base (.subtract _ _ _) | .arithmetic _ _ _ _ | .jumpIfZero _ _ => isTrue True.intro

@[instance_reducible] def constantsDec (B : Nat) (program : List PackingOp) : Decidable (ConstantsLE B program) := by
  letI : DecidablePred (ConstantLE B) := constantDec B
  unfold ConstantsLE
  infer_instance

theorem constants_mono (small large : Nat) (program : List PackingOp) (hle : small ≤ large)
    (hs : ConstantsLE small program) : ConstantsLE large program := by
  intro op hm
  have hc := hs op hm
  cases op with
  | base operation =>
    cases operation with
    | base instruction => cases instruction <;> first | exact hc.trans hle | trivial
    | subtract target left right => trivial
  | arithmetic primitive target left right => trivial
  | jumpIfZero condition target => trivial

theorem prelude_constants : ConstantsLE 1024 (dimensionPrelude 0) := by
  let _ := constantsDec 1024 (dimensionPrelude 0)
  decide

theorem cursorInit_constants (B : Nat) : ConstantsLE B cursorInit := by
  intro op hm
  simp only [cursorInit, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · trivial

theorem snapshot_constants (B cursor saved : Nat) (hc : cursor ≤ B) (hs : saved ≤ B) :
    ConstantsLE B (snapshot cursor saved) := by
  intro op hm
  simp only [snapshot, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact hs
  · trivial

theorem patch_constants (B cursor saved outputBase : Nat) (h1 : 1 ≤ B)
    (hc : cursor ≤ B) (hs : saved ≤ B) (ho : outputBase ≤ B) : ConstantsLE B (patch cursor saved outputBase) := by
  intro op hm
  simp only [patch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact hs
  · trivial
  · exact h1
  · trivial
  · trivial
  · exact ho
  · trivial
  · trivial

theorem measuredHead_constants (rom : PhysicalROM) (environment : Nat → Nat) (B heapWords : Nat) (hB : 1024 ≤ B) :
    ConstantsLE B (wrapperHead 64 0 3 1024) :=
  ConstantsLE.append B _ _ (snapshot_constants B 0 3 (by omega) (by omega))
    (emitWord_constants (.constant 0) rom environment B heapWords 64 0 1024
      (by omega) (by change 65 ≤ B; omega) (by omega) hB (Nat.zero_le _))

theorem measuredBlock_constants (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords start : Nat) (hB : 1024 ≤ B) (hb : template.Below 64) (hs : template.StackFits 64 1024)
    (hc : TemplateChecked rom B heapWords environment template)
    (he : 5 * (start + template.codeLength 64 + 23) ≤ B) :
    ConstantsLE B (block template 64 0 3 1024 start) := by
  have ht := template_constants template rom environment B heapWords 64 0 1024 (start + 13)
    (by omega) (by omega) hB hb hs hc (by omega)
  exact ConstantsLE.append B _ _
    (ConstantsLE.append B _ _ (measuredHead_constants rom environment B heapWords hB) ht)
    (patch_constants B 0 3 1024 (by omega) (by omega) (by omega) hB)

theorem streams_constants (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords count start : Nat) (hB : 1024 ≤ B)
    (hb : ∀ template ∈ templates, template.Below 64) (hs : ∀ template ∈ templates, template.StackFits 64 1024)
    (hc : StreamsChecked rom B heapWords environment 3 count templates)
    (he : 5 * (start + streamLength 64 templates) ≤ B) :
    ConstantsLE B (streams 64 0 3 1024 start templates) := by
  induction templates generalizing count start with
  | nil => intro op hm; cases hm
  | cons first later ih =>
    let firstCode := block first 64 0 3 1024 start
    have hl : firstCode.length = first.codeLength 64 + 23 := block_length first 64 0 3 1024 start
    have heFirst : 5 * (start + first.codeLength 64 + 23) ≤ B := by
      change 5 * (start + (first.codeLength 64 + 23 + streamLength 64 later)) ≤ B at he
      omega
    have heLater : 5 * ((start + firstCode.length) + streamLength 64 later) ≤ B := by
      change 5 * (start + (first.codeLength 64 + 23 + streamLength 64 later)) ≤ B at he
      omega
    have hf : ConstantsLE B firstCode := measuredBlock_constants first rom (Function.update environment 3 count)
      B heapWords start hB (hb first List.mem_cons_self) (hs first List.mem_cons_self) hc.1 heFirst
    have hr := ih
      (count + (first.denote rom (Function.update environment 3 count)).length + 1) (start + firstCode.length)
      (fun template ht => hb template (List.mem_cons_of_mem _ ht))
      (fun template ht => hs template (List.mem_cons_of_mem _ ht)) hc.2 heLater
    exact ConstantsLE.append B _ _ hf hr

theorem copyInit_constants (B cursor source : Nat) (h1 : 1 ≤ B) (hc : cursor ≤ B) (hs : source ≤ B) :
    ConstantsLE B (copyInit cursor source) := by
  intro op hm
  simp only [copyInit, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact Nat.zero_le _
  · exact hs
  · exact h1
  · exact Nat.zero_le _

theorem copyHead_constants (B exit : Nat) (he : exit ≤ B) : ConstantsLE B (copyHead exit) := by
  intro op hm
  simp only [copyHead, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact he
  · trivial

theorem copyTail_constants (B entry : Nat) (he : entry ≤ B) : ConstantsLE B (copyTail entry) := by
  intro op hm
  simp only [copyTail, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact he
  · trivial

theorem copyBlock_constants (B cursor source start : Nat) (h1 : 1 ≤ B) (hc : cursor ≤ B) (hs : source ≤ B)
    (he : 5 * (start + 15) ≤ B) : ConstantsLE B (copyBlock cursor source start) :=
  ConstantsLE.append B _ _
    (ConstantsLE.append B _ _ (copyInit_constants B cursor source h1 hc hs) (copyHead_constants B _ he))
    (copyTail_constants B _ (by omega))

theorem generator_constants (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords : Nat) (hB : 1024 ≤ B)
    (hb : ∀ template ∈ templates, template.Below 64) (hs : ∀ template ∈ templates, template.StackFits 64 1024)
    (hc : StreamsChecked rom B heapWords environment 3 0 templates)
    (he : 5 * (generator templates).length ≤ B) : ConstantsLE B (generator templates) := by
  have hlen := generator_length templates
  have hstream : 5 * (48 + streamLength 64 templates) ≤ B := by omega
  have hcopy : 5 * ((48 + streamLength 64 templates) + 15) ≤ B := by omega
  exact ConstantsLE.append B _ _
    (ConstantsLE.append B _ _
      (ConstantsLE.append B _ _ (constants_mono 1024 B _ hB prelude_constants) (cursorInit_constants B))
      (streams_constants templates rom environment B heapWords 0 48 hB hb hs hc hstream))
    (copyBlock_constants B 0 1024 _ (by omega) (by omega) hB hcopy)

theorem generator_packingCode_fits (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B bits heapWords : Nat) (hB : 1024 ≤ B) (hf : Fits bits B)
    (hb : ∀ template ∈ templates, template.Below 64) (hs : ∀ template ∈ templates, template.StackFits 64 1024)
    (hc : StreamsChecked rom B heapWords environment 3 0 templates)
    (he : 5 * (generator templates).length ≤ B) : WordsFit bits (packingCode (generator templates)) :=
  packingCode_fit B bits (by omega) hf _ (generator_constants templates rom environment B heapWords hB hb hs hc he)

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044o
