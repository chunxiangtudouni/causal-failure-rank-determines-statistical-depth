module
public import PaperProofs.Common.PSTR_TM_PackCode_036

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackLift037
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

theorem align_command (q next : Fin 135) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMAlignCode030.alignMachine q symbol = some (next, statement)) :
    packMachine (embedAlign q) symbol = some (embedAlign next, statement) := by
  have hn : q.val ≠ 134 := by
    intro he
    simp [PSTRTMAlignCode030.alignMachine, he] at old
  have hlo : ¬q.val + 10 < 10 := by omega
  have hhi : q.val + 10 < 145 := by omega
  have halt : q.val + 10 ≠ 144 := by omega
  have eof : ¬(q.val = 8 ∧ symbol = false) := by
    rintro ⟨hq, hs⟩
    simp [PSTRTMAlignCode030.alignMachine, hq, hs] at old
  simp [packMachine, embedAlign, hlo, hhi, halt, eof, old]

theorem pad_command (q next : Fin 41) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMPadInsert034.padMachine q symbol = some (next, statement)) :
    packMachine (embedPad q) symbol = some (embedPad next, statement) := by
  have hn : q.val ≠ 40 := by
    intro he
    simp [PSTRTMPadInsert034.padMachine, he] at old
  have hlo : ¬q.val + 145 < 10 := by omega
  have hmid : ¬q.val + 145 < 145 := by omega
  have hhi : q.val + 145 < 186 := by omega
  have halt : q.val + 145 ≠ 185 := by omega
  simp [packMachine, embedPad, hlo, hmid, hhi, halt, old]

/-- Every nonhalting030 transition is retained verbatim by the actual
194-label program. Its EOF extension only changes previously halting cases. -/
theorem align_step (before after : MachineState 134)
    (old : Turing.TM0.step PSTRTMAlignCode030.alignMachine before = some after) :
    Turing.TM0.step packMachine (liftAlign before) = some (liftAlign after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMAlignCode030.alignMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next, statement⟩ := command
      simp only [hc, Option.map_some, Option.some.injEq] at old
      subst after
      have hm := align_command q next tape.head statement hc
      simp only [Turing.TM0.step, liftAlign, hm, Option.map_some]

theorem pad_step (before after : MachineState 40)
    (old : Turing.TM0.step PSTRTMPadInsert034.padMachine before = some after) :
    Turing.TM0.step packMachine (liftPad before) = some (liftPad after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMPadInsert034.padMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next, statement⟩ := command
      simp only [hc, Option.map_some, Option.some.injEq] at old
      subst after
      have hm := pad_command q next tape.head statement hc
      simp only [Turing.TM0.step, liftPad, hm, Option.map_some]

theorem align_chain (trace : List (MachineState 134))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMAlignCode030.alignMachine a = some b)) :
    (trace.map liftAlign).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  apply (List.isChain_map _).mpr
  exact old.imp align_step

theorem pad_chain (trace : List (MachineState 40))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMPadInsert034.padMachine a = some b)) :
    (trace.map liftPad).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  apply (List.isChain_map _).mpr
  exact old.imp pad_step

theorem align_transfer (left right : List Bool) :
    Turing.TM0.step packMachine (liftAlign (PSTRTMAlignCode030.state 134 left right)) =
      some (state 0 left right) := by
  simp [Turing.TM0.step, packMachine, liftAlign, embedAlign, PSTRTMAlignCode030.state,
    state, Turing.Tape.write_self]

theorem pad_transfer (left right : List Bool) :
    Turing.TM0.step packMachine (liftPad (PSTRTMPadInsert034.state 40 left right)) =
      some (state 0 left right) := by
  simp [Turing.TM0.step, packMachine, liftPad, embedPad, PSTRTMPadInsert034.state,
    state, Turing.Tape.write_self]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackLift037
