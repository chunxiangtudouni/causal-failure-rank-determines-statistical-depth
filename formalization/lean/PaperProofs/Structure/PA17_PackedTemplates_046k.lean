module
public import PaperProofs.Structure.PA17_PackedTemplates_046f
public import PaperProofs.Structure.PA17_PackedPhase_045e

/-! One fixed six-template family in the original generatedCode order.
The length prefix is added once by the real measured-length controller. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041

def templates : List Template :=
  [wrappedFull.haltingTemplate, PA17QueryTemplates044f.wrappedQuery.haltingTemplate,
    wrappedRolling.haltingTemplate, full, query, rolling]

theorem templates_length : templates.length = 6 := rfl

theorem templates_denote (N q t : Nat) (hq : 0 < q) (environment : Nat → Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = indexWidth 32 N q) :
    templates.map (fun template => template.denote (dimensionROM N q t) environment) =
      [haltingWords (PA17WrappedNatRAM038a.implementation.buildProgram N q t),
       haltingWords (PA17WrappedNatRAM038a.implementation.queryProgram N q t),
       haltingWords (PA17WrappedNatRAM038a.implementation.rollingProgram N q t),
       packingCode (PA17PackedPhase045.programs.build N q t),
       packingCode (PA17PackedPhase045.programs.query N q t),
       packingCode (PA17PackedPhase045.programs.rolling N q t)] := by
  simp only [templates, List.map_cons, List.map_nil, Program.haltingTemplate_denote,
    wrappedFull_eval, wrappedRolling_eval, PA17QueryTemplates044f.wrappedQuery_eval,
    full_denote N q t hq environment hw hb, query_denote N q t hq environment hw hb,
    rolling_denote N q t hq environment hw hb]
  rfl

def output (N q t : Nat) (environment : Nat → Nat) : List Nat :=
  (templates.map (fun template => template.denote (dimensionROM N q t) environment)).flatMap
    (fun code => code.length :: code)

theorem output_eq_generatedCode (N q t : Nat) (hq : 0 < q) (environment : Nat → Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = indexWidth 32 N q) :
    output N q t environment = generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q t := by
  rw [output, templates_denote N q t hq environment hw hb]
  rfl

theorem templates_static (template : Template) (ht : template ∈ templates) :
    template.WellScoped (insert 3 {1, 2}) ∧ template.Below 64 ∧ template.StackFits 64 1024 ∧
      template.InputsBelow 3 ∧ PA17UniformGenerator035e.CountersAvoid 0 template := by
  simp only [templates, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨PA17ProgramTemplates041.full_parentScoped.2, PA17ProgramTemplates041.full_below.2,
      PA17ProgramTemplates041.full_stackFits.2, PA17ProgramTemplates041.full_inputsBelow.2,
      PA17ProgramTemplates041.full_countersAvoid.2⟩
  · exact ⟨PA17QueryTemplates044g.wrapped_parentScoped.2, PA17QueryTemplates044g.wrapped_below.2,
      PA17QueryTemplates044g.wrapped_stackFits.2, PA17QueryTemplates044g.wrapped_inputsBelow.2,
      PA17QueryTemplates044g.wrapped_countersAvoid.2⟩
  · exact ⟨PA17ProgramTemplates041.rolling_parentScoped.2, PA17ProgramTemplates041.rolling_below.2,
      PA17ProgramTemplates041.rolling_stackFits.2, PA17ProgramTemplates041.rolling_inputsBelow.2,
      PA17ProgramTemplates041.rolling_countersAvoid.2⟩
  · exact ⟨full_parentScoped, full_below, full_stackFits, full_inputsBelow, full_countersAvoid⟩
  · exact ⟨query_parentScoped, query_below, query_stackFits, query_inputsBelow, query_countersAvoid⟩
  · exact ⟨rolling_parentScoped, rolling_below, rolling_stackFits, rolling_inputsBelow, rolling_countersAvoid⟩

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
