module

public import PaperProofs.Structure.PA17_UniformGenerator_035ae
public import PaperProofs.Structure.PA17_UniformGenerator_035z
public import PaperProofs.Structure.PA17_UniformGenerator_035ab
public import PaperProofs.Structure.PA17_UniformGenerator_035ad

/-! Complete actual natural execution of the fixed finite source: original
dimension ROM, real width/bits prelude, measured streams, forward copy.
All instruction-prefix safety follows from local compiler contracts. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035af

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d
  PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035g PA17UniformGenerator035i
  PA17UniformGenerator035j PA17UniformGenerator035l PA17UniformGenerator035m PA17UniformGenerator035o
  PA17UniformGenerator035ab PA17UniformGenerator035ac PA17UniformGenerator035ad PA17UniformGenerator035ae PA17UniformGenerator035z

theorem cursorInit_numeric (rom : PhysicalROM) (B heapWords : Nat) (hH : 0 < heapWords)
    (state : NatState) (hr : RegistersLE B state) : NumericSafe B heapWords rom cursorInit state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 3 at hn
    interval_cases count <;> cases register <;>
      simp [cursorInit, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 3 at hn
    interval_cases count <;>
      simp [cursorInit, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hH]

theorem generator_run (templates : List Template) (N q t B heapWords : Nat)
    (hscope : ∀ template ∈ templates, template.WellScoped (insert 3 {1,2}))
    (hbelow : ∀ template ∈ templates, template.Below 64)
    (hfits : ∀ template ∈ templates, template.StackFits 64 1024)
    (havoid : ∀ template ∈ templates, CountersAvoid 0 template)
    (hchecked : StreamsChecked (PA17Generator.dimensionROM N q t) B heapWords (preparedEnv N q) 3 0 templates)
    (hinput : N + q + 1 ≤ B) (hbits : indexWidth 32 N q ≤ B)
    (hpcB : 5 * (generator templates).length ≤ B)
    (houtputB : 1024 + (streamWords (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates).length + 1 ≤ B)
    (houtputH : 1024 + (streamWords (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates).length + 1 ≤ heapWords) :
    let rom := PA17Generator.dimensionROM N q t
    let words := streamWords rom (preparedEnv N q) 3 0 templates
    let fresh := natRun rom (generator templates) (stepsBeforeHalt templates N q t) start
    fresh.pc = 5 * (generator templates).length ∧ fresh.halted = false ∧
      (∀ position (hp : position < words.length), fresh.heap position = words[position]) ∧
      RunSafe B heapWords rom (generator templates) (stepsBeforeHalt templates N q t) start := by
  intro rom words fresh
  change 1024 + words.length + 1 ≤ B at houtputB
  change 1024 + words.length + 1 ≤ heapWords at houtputH
  let environment := preparedEnv N q
  let head := dimensionPrelude 0
  let source := streams 64 0 3 1024 48 templates
  let beforeCopy := head ++ cursorInit ++ source
  let tail := PA17UniformGenerator035g.copyBlock 0 1024 (48 + streamLength 64 templates)
  let allCode := generator templates
  have hSourceCode : allCode = head ++ cursorInit ++ source ++ tail := rfl
  have hHeadLen : head.length = 45 := rfl
  have hCursorLen : cursorInit.length = 3 := rfl
  have hLeadLen : (head ++ cursorInit).length = 48 := by rw [List.length_append, hHeadLen, hCursorLen]
  have hBeforeLen : beforeCopy.length = 48 + streamLength 64 templates := by
    rw [List.length_append, hLeadLen, streams_length]
  have hCopyCode : beforeCopy ++ PA17UniformGenerator035g.copyBlock 0 1024 beforeCopy.length ++ [] = allCode := by
    rw [List.append_nil, hBeforeLen]
    rfl
  have hsStart : RegistersLE B start := fun _ => Nat.zero_le _
  have hsHead := dimensionPrelude_safe N q t B heapWords [] (cursorInit ++ source ++ tail) start
    (by omega) (by omega) hinput hbits rfl rfl hsStart
    (by simpa only [allCode, generator, source, tail, List.nil_append, List.length_nil, List.append_assoc] using hpcB)
  have hsHead' : RunSafe B heapWords rom allCode (dimensionClock N q) start := by
    simpa only [rom, allCode, generator, source, tail, List.nil_append, List.length_nil, List.append_assoc] using hsHead
  let pre := natRun rom allCode (dimensionClock N q) start
  have hpre := dimensionPrelude_run N q t [] (cursorInit ++ source ++ tail) start rfl rfl
  have hpre' : pre.pc = 225 ∧ pre.halted = false ∧ pre.heap 1 = CapacityBits.width q ∧ pre.heap 2 = indexWidth 32 N q := by
    exact ⟨by simpa only [pre, rom, allCode, generator, source, tail, List.nil_append, List.length_nil, Nat.zero_add, List.append_assoc] using hpre.1,
      by simpa only [pre, rom, allCode, generator, source, tail, List.nil_append, List.length_nil, List.append_assoc] using hpre.2.1,
      by simpa only [pre, rom, allCode, generator, source, tail, List.nil_append, List.length_nil, List.append_assoc] using hpre.2.2.1,
      by simpa only [pre, rom, allCode, generator, source, tail, List.nil_append, List.length_nil, List.append_assoc] using hpre.2.2.2.1⟩
  let initialized := runOps rom cursorInit pre
  have hinitHeap : initialized.heap = Function.update pre.heap 0 0 := rfl
  have hinitPC : initialized.pc = 240 := by
    rw [runOps_pc rom cursorInit pre (by simp [cursorInit, NoJump]), hpre'.1, hCursorLen]
  have hsCursor : RunSafe B heapWords rom allCode 3 pre := by
    have hh := straight_segment_safe rom B heapWords head cursorInit (source ++ tail)
      (by simp [cursorInit, NoJump]) pre (by rw [hHeadLen]; exact hpre'.1) hpre'.2.1
      (cursorInit_numeric rom B heapWords (by omega) pre (hsHead'.final _ _ _ _ _).1)
    simpa only [hSourceCode, hCursorLen, List.append_assoc] using hh
  have hcursorRun : natRun rom allCode 3 pre = initialized := by
    have hh := natRun_of_straight_segment rom (head ++ cursorInit ++ (source ++ tail)) cursorInit head.length
      (by simp only [List.length_append]; omega)
      (segment_index head cursorInit (source ++ tail)) (by simp [cursorInit, NoJump])
      pre (by rw [hHeadLen]; exact hpre'.1) hpre'.2.1
    simpa only [hSourceCode, hCursorLen, List.append_assoc] using hh
  have hregInit : RegistersLE B initialized := by
    have hh := (hsCursor.final _ _ _ _ _).1
    rw [hcursorRun] at hh
    exact hh
  have henv : EnvRep {1,2} environment initialized.heap := by
    intro address hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · simpa only [hinitHeap, Function.update_of_ne (by decide : 1 ≠ 0), environment, preparedEnv, ite_true] using hpre'.2.2.1
    · simpa only [hinitHeap, Function.update_of_ne (by decide : 2 ≠ 0), environment, preparedEnv,
        show (2 : Nat) ≠ 1 by decide, ite_false, ite_true] using hpre'.2.2.2
  have hempty : StreamRep 0 1024 [] initialized.heap := by
    constructor
    · rw [hinitHeap, Function.update_self]; rfl
    · intro position hp; simp only [List.length_nil] at hp; omega
  have hscopeBelow : ScopeBelow 64 {1,2} := by
    intro address hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> decide
  have hStreamsCode : (head ++ cursorInit) ++ streams 64 0 3 1024 (head ++ cursorInit).length templates ++ tail = allCode := by
    rw [hLeadLen]
    rfl
  have hstreams := streams_semantics_safe templates rom B heapWords 64 0 3 1024 {1,2} environment
    hscope hbelow hfits havoid hscopeBelow (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (head ++ cursorInit) tail initialized [] (by rw [hLeadLen]; exact hinitPC)
    ((runOps_halted rom cursorInit pre).trans hpre'.2.1) hregInit henv hempty hchecked
    (by rw [hStreamsCode]; exact hpcB)
    (by simpa only [environment, rom, List.length_nil, Nat.add_zero] using houtputB)
    (by simpa only [environment, rom, List.length_nil, Nat.add_zero] using houtputH)
  rw [hStreamsCode] at hstreams
  let emitted := natRun rom allCode (streamClock rom environment 64 3 0 templates) initialized
  have hstreamResult : Result {1,2} environment 0 1024 words (5 * (48 + streamLength 64 templates)) emitted := by
    simpa only [emitted, hLeadLen, List.length_nil, List.nil_append, words, environment, Nat.zero_add] using hstreams.1
  have hstreamSafe : RunSafe B heapWords rom allCode (streamClock rom environment 64 3 0 templates) initialized := by
    simpa only [List.length_nil] using hstreams.2
  have hwordBound := stream_words_le templates rom B heapWords environment 3 0 hchecked
    (by change 0 + words.length ≤ B; omega)
  have hcursor : emitted.heap 0 = words.length := hstreamResult.2.2.2.1
  have hsCopy := copy_safe rom B heapWords beforeCopy [] 0 1024 emitted
    (by rw [hBeforeLen]; exact hstreamResult.1) hstreamResult.2.1 (hstreamSafe.final _ _ _ _ _).1
    (Nat.zero_le _) (by omega) (by omega)
    (by rw [hcursor]; exact by omega) (by rw [hcursor]; exact by omega)
    (by
      intro position hp
      rw [hcursor] at hp
      rw [hstreamResult.2.2.2.2 position hp]
      exact hwordBound _ (List.getElem_mem hp))
    (by rw [hCopyCode]; exact hpcB)
  rw [hCopyCode, hcursor] at hsCopy
  have hcopy := copy_run rom beforeCopy [] 0 1024 emitted (by rw [hBeforeLen]; exact hstreamResult.1) hstreamResult.2.1
  rw [hCopyCode, hcursor] at hcopy
  have hfirstRun : natRun rom allCode (dimensionClock N q + 3) start = initialized := by
    rw [natRun_add]
    exact hcursorRun
  have hsecondRun : natRun rom allCode (dimensionClock N q + 3 + streamClock rom environment 64 3 0 templates) start = emitted := by
    rw [natRun_add, hfirstRun]
  have hsFirst := RunSafe.add _ _ _ _ _ _ start hsHead' hsCursor
  have hsSecond := RunSafe.add _ _ _ _ _ _ start hsFirst (by rw [hfirstRun]; exact hstreamSafe)
  have hsAll := RunSafe.add _ _ _ _ _ _ start hsSecond (by rw [hsecondRun]; exact hsCopy)
  have htime : stepsBeforeHalt templates N q t =
      (dimensionClock N q + 3 + streamClock rom environment 64 3 0 templates) + (9 * words.length + 8) := rfl
  have hrun : fresh = natRun rom allCode (9 * words.length + 8) emitted := by
    change natRun rom allCode (stepsBeforeHalt templates N q t) start = _
    rw [htime, natRun_add, hsecondRun]
  rw [hrun]
  refine ⟨?_, hcopy.2.2, ?_, ?_⟩
  · have hlength : allCode.length = beforeCopy.length + 15 := by
      rw [← hCopyCode, List.length_append, List.length_append, PA17UniformGenerator035g.copyBlock_length, List.length_nil, Nat.add_zero]
    rw [hlength]
    exact hcopy.2.1
  · intro position hp
    have hh := copy_stream rom beforeCopy [] 0 1024 emitted (by rw [hBeforeLen]; exact hstreamResult.1)
      hstreamResult.2.1 words hstreamResult.2.2.2 position hp
    rw [hCopyCode] at hh
    exact hh
  · simpa only [htime] using hsAll

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035af
