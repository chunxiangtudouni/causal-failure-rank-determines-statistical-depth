module
public import PaperProofs.Structure.PA17_UniformGenerator_035y

/-! Literal and genuine jump-PC bounds of the actual template compiler.
All code is checked, including loop bodies whose runtime bound is zero. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044n
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035o PA17UniformGenerator035y

theorem spill_constants (B target : Nat) (ht : target ≤ B) : ConstantsLE B (spill target) := by
  intro op hm
  simp only [spill, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ht
  · trivial

theorem emitTail_constants (B cursor outputBase : Nat) (h1 : 1 ≤ B) (hc : cursor ≤ B) (ho : outputBase ≤ B) :
    ConstantsLE B (emitTail cursor outputBase) := by
  intro op hm
  simp only [emitTail, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact ho
  · trivial
  · trivial
  · exact h1
  · trivial
  · trivial

theorem bind_constants (expression : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords stack target : Nat) (hstack : stack + expression.size ≤ B) (ht : target ≤ B)
    (hc : PA17UniformGenerator035j.ExprChecked rom environment B heapWords expression) :
    ConstantsLE B (bind expression stack target) :=
  ConstantsLE.append B _ _ (expression_constants expression rom environment B heapWords stack hstack hc)
    (spill_constants B target ht)

theorem emitWord_constants (expression : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords stack cursor outputBase : Nat) (h1 : 1 ≤ B) (hstack : stack + expression.size ≤ B)
    (hcursor : cursor ≤ B) (houtput : outputBase ≤ B)
    (hc : PA17UniformGenerator035j.ExprChecked rom environment B heapWords expression) :
    ConstantsLE B (emitWord expression stack cursor outputBase) :=
  ConstantsLE.append B _ _ (expression_constants expression rom environment B heapWords stack hstack hc)
    (emitTail_constants B cursor outputBase h1 hcursor houtput)

theorem loopHead_constants (B counter exit : Nat) (hc : counter ≤ B) (he : exit ≤ B) :
    ConstantsLE B (loopHead counter exit) := by
  intro op hm
  simp only [loopHead, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact he
  · trivial

theorem loopTail_constants (B counter entry : Nat) (h1 : 1 ≤ B) (hc : counter ≤ B) (he : entry ≤ B) :
    ConstantsLE B (loopTail counter entry) := by
  intro op hm
  simp only [loopTail, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc
  · trivial
  · exact h1
  · trivial
  · trivial
  · exact Nat.zero_le _
  · exact he
  · trivial

theorem loopBlock_constants (B counter start : Nat) (body : List PackingOp) (h1 : 1 ≤ B)
    (hc : counter ≤ B) (hs : 5 * start ≤ B) (he : 5 * (start + body.length + 12) ≤ B)
    (hb : ConstantsLE B body) : ConstantsLE B (loopBlock counter start body) :=
  ConstantsLE.append B _ _ (ConstantsLE.append B _ _ (loopHead_constants B counter _ hc he) hb)
    (loopTail_constants B counter _ h1 hc hs)

theorem template_constants (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords stack cursor outputBase start : Nat) (h1 : 1 ≤ B) (hcursor : cursor ≤ B) (houtput : outputBase ≤ B)
    (hbelow : template.Below stack) (hstack : template.StackFits stack outputBase)
    (hchecked : TemplateChecked rom B heapWords environment template)
    (hend : 5 * (start + template.codeLength stack) ≤ B) :
    ConstantsLE B (template.compile stack cursor outputBase start) := by
  induction template generalizing environment start with
  | empty => intro op hm; cases hm
  | word expression =>
    exact emitWord_constants expression rom environment B heapWords stack cursor outputBase h1
      (hstack.trans houtput) hcursor houtput hchecked
  | append left right ihl ihr =>
    have hl : 5 * (start + left.codeLength stack) ≤ B := by
      change 5 * (start + (left.codeLength stack + right.codeLength stack)) ≤ B at hend
      omega
    have hr : 5 * ((start + left.codeLength stack) + right.codeLength stack) ≤ B := by
      change 5 * (start + (left.codeLength stack + right.codeLength stack)) ≤ B at hend
      omega
    exact ConstantsLE.append B _ _
      (ihl environment start hbelow.1 hstack.1 hchecked.1 hl)
      (ihr environment (start + left.codeLength stack) hbelow.2 hstack.2 hchecked.2 hr)
  | «repeat» counter count body ih =>
    let pre := bind count stack counter
    let bodyCode := body.compile stack cursor outputBase (start + pre.length + 4)
    have hc : counter ≤ B := by have hs := hstack.1; have hb := hbelow.1; omega
    have hp : pre.length = (count.compile stack).length + 2 := bind_length count stack counter
    have hb : bodyCode.length = body.codeLength stack := body.compile_length stack cursor outputBase _
    have he : 5 * (start + pre.length + bodyCode.length + 12) ≤ B := by
      change 5 * (start + ((count.compile stack).length + 2 + body.codeLength stack + 12)) ≤ B at hend
      omega
    have hbodyEnd : 5 * ((start + pre.length + 4) + body.codeLength stack) ≤ B := by omega
    have hbodyChecked := hchecked.2 0 (Nat.zero_le _)
    have hbody : ConstantsLE B bodyCode :=
      ih (Function.update environment counter 0) (start + pre.length + 4)
        hbelow.2.2 hstack.2 hbodyChecked hbodyEnd
    have hpre : ConstantsLE B pre :=
      bind_constants count rom environment B heapWords stack counter (hstack.1.trans houtput) hc hchecked.1
    change ConstantsLE B (pre ++ loopBlock counter (start + pre.length) bodyCode)
    exact ConstantsLE.append B _ _ hpre
      (loopBlock_constants B counter (start + pre.length) bodyCode h1 hc (by omega) (by omega) hbody)

theorem template_constants_embedded (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords stack cursor outputBase : Nat) (left right : List PackingOp)
    (h1 : 1 ≤ B) (hcursor : cursor ≤ B) (houtput : outputBase ≤ B)
    (hbelow : template.Below stack) (hstack : template.StackFits stack outputBase)
    (hchecked : TemplateChecked rom B heapWords environment template)
    (hwhole : 5 * (left ++ template.compile stack cursor outputBase left.length ++ right).length ≤ B) :
    ConstantsLE B (template.compile stack cursor outputBase left.length) := by
  apply template_constants template rom environment B heapWords stack cursor outputBase left.length
    h1 hcursor houtput hbelow hstack hchecked
  simp only [List.length_append, template.compile_length] at hwhole
  omega

theorem template_packingCode_fits (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (B bits heapWords stack cursor outputBase : Nat) (hB : 15 ≤ B) (hfit : Fits bits B)
    (hcursor : cursor ≤ B) (houtput : outputBase ≤ B)
    (hbelow : template.Below stack) (hstack : template.StackFits stack outputBase)
    (hchecked : TemplateChecked rom B heapWords environment template)
    (hend : 5 * template.codeLength stack ≤ B) :
    WordsFit bits (packingCode (template.compile stack cursor outputBase 0)) := by
  apply packingCode_fit B bits hB hfit
  exact template_constants template rom environment B heapWords stack cursor outputBase 0
    (by omega) hcursor houtput hbelow hstack hchecked (by simpa only [Nat.zero_add] using hend)

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044n
