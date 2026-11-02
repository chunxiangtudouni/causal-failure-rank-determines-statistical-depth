module

public import PaperProofs.Structure.PA17_UniformGenerator_035af
public import PaperProofs.Structure.PA17_UniformGenerator_035x

/-! Complete physical execution fields for the fixed generator source,
derived from the whole actual driver and existing finite-word semantics. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ah

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035e
  PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035o PA17UniformGenerator035x
  PA17UniformGenerator035ac PA17UniformGenerator035ad PA17UniformGenerator035ae PA17UniformGenerator035af

theorem generator_word (templates : List Template) (N q t B heapWords bits : Nat)
    (hscope : ∀ template ∈ templates, template.WellScoped (insert 3 {1,2}))
    (hbelow : ∀ template ∈ templates, template.Below 64)
    (hfits : ∀ template ∈ templates, template.StackFits 64 1024)
    (havoid : ∀ template ∈ templates, CountersAvoid 0 template)
    (hchecked : StreamsChecked (PA17Generator.dimensionROM N q t) B heapWords (preparedEnv N q) 3 0 templates)
    (hinput : N + q + 1 ≤ B) (hbits : indexWidth 32 N q ≤ B)
    (hpcB : 5 * (generator templates).length ≤ B)
    (houtputB : 1024 + (streamWords (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates).length + 1 ≤ B)
    (houtputH : 1024 + (streamWords (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates).length + 1 ≤ heapWords)
    (hBfit : Fits bits B) (hcode : WordsFit bits (packingCode (generator templates))) :
    let rom := PA17Generator.dimensionROM N q t
    let words := streamWords rom (preparedEnv N q) 3 0 templates
    let steps := stepsBeforeHalt templates N q t + 1
    let fresh := packingRun rom (generator templates) steps (packingInitial (fun _ => BitVec.ofNat bits 0))
    fresh.halted = true ∧
      (∀ position (hp : position < words.length), (fresh.heap (BitVec.ofNat bits position)).toNat = words[position]) ∧
      (∀ count < steps,
        let state := packingRun rom (generator templates) count (packingInitial (fun _ => BitVec.ofNat bits 0))
        state.halted = false ∧ state.pc.toNat + 4 < (packingCode (generator templates)).length ∧
          let fetched := physicalFetch bits (packingCode (generator templates)) state.pc.toNat
          match PackingOp.decode fetched with
          | none => fetched = haltWords
          | some op => packingAccessFits rom heapWords state op) := by
  intro rom words steps fresh
  have hn := generator_run templates N q t B heapWords hscope hbelow hfits havoid hchecked hinput hbits hpcB houtputB houtputH
  have hs : RunSafe B heapWords rom (generator templates) (stepsBeforeHalt templates N q t) start := hn.2.2.2
  have hend : (natRun rom (generator templates) (stepsBeforeHalt templates N q t) start).pc = 5 * (generator templates).length := hn.1
  have hpcfit : Fits bits (5 * (generator templates).length) := lt_of_le_of_lt hpcB hBfit
  have hw := stream_words_le templates rom B heapWords (preparedEnv N q) 3 0 hchecked
    (by change 0 + words.length ≤ B; change 1024 + words.length + 1 ≤ B at houtputB; omega)
  have hhalt := actual_halt rom B heapWords bits (generator templates) (stepsBeforeHalt templates N q t) start hs hBfit hcode hpcfit hend
  rw [start_toWord] at hhalt
  refine ⟨?_, ?_, ?_⟩
  · change (packingRun rom (generator templates) (stepsBeforeHalt templates N q t + 1) _).halted = true
    rw [hhalt]
  · intro position hp
    have ha : Fits bits position := lt_of_le_of_lt (by change 1024 + words.length + 1 ≤ B at houtputB; omega) hBfit
    have hv : Fits bits words[position] := lt_of_le_of_lt (hw _ (List.getElem_mem hp)) hBfit
    have hh := actual_halting_output rom B heapWords bits (generator templates) (stepsBeforeHalt templates N q t) start
      hs hBfit hcode hpcfit hend position words[position] ha hv (hn.2.2.1 position hp)
    rw [start_toWord] at hh
    exact hh.2
  · have hh := actual_allprefix rom B heapWords bits (generator templates) (stepsBeforeHalt templates N q t) start hs hBfit hcode hpcfit hend
    rw [start_toWord] at hh
    exact hh

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ah
