module
public import Common.PSTR_TM_ThresholdCopyInit_128

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRoundLift129
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126

/-- `bit` reflects the actual saved data bit in finite control40..119.
It is a proof index for the SAME fixed code126, not an input/oracle field. -/
def phaseLabel (bit : Bool) (q : Fin 40) : Fin 131 :=
  ⟨(if bit then 80 else 40)+q.val,by cases bit <;> dsimp <;> have hq := q.isLt <;> omega⟩

def cursorLabel (bit : Bool) (entry : Fin 3) (q : Fin 3) : Fin 131 :=
  let offset := match entry.val with | 0 => 1 | 1 => 5 | _ => 7
  phaseLabel bit ⟨offset+q.val,by
    have hq := q.isLt
    fin_cases entry <;> norm_num [offset] <;> omega⟩

def rewindLabel (bit : Bool) (entry : Fin 3) (q : Fin 4) : Fin 131 :=
  phaseLabel bit (match entry.val,q.val with
    | 0,0 => 17 | 0,1 => 18 | 0,2 => 19 | 0,_ => 20
    | 1,0 => 24 | 1,1 => 25 | 1,2 => 26 | 1,_ => 27
    | _,0 => 29 | _,1 => 30 | _,2 => 31 | _,_ => 32)

def liftCursor (bit : Bool) (entry : Fin 3) (old : MachineState 2) : MachineState 130 :=
  ⟨cursorLabel bit entry old.q,old.Tape⟩

def liftRewind (bit : Bool) (entry : Fin 3) (old : MachineState 3) : MachineState 130 :=
  ⟨rewindLabel bit entry old.q,old.Tape⟩

theorem cursor_command (bit : Bool) (entry : Fin 3) (q next : Fin 3) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMThresholdCursor115.cursorMachine q symbol=some (next,statement)) :
    copyMachine (cursorLabel bit entry q) symbol=some (cursorLabel bit entry next,statement) := by
  cases bit <;> fin_cases entry <;> fin_cases q <;> cases symbol <;>
    simp [PSTRTMThresholdCursor115.cursorMachine] at old <;>
    rcases old with ⟨rfl,rfl⟩ <;> rfl

theorem rewind_command (bit : Bool) (entry : Fin 3) (q next : Fin 4) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMMulRewind085.rewindMachine q symbol=some (next,statement)) :
    copyMachine (rewindLabel bit entry q) symbol=some (rewindLabel bit entry next,statement) := by
  cases bit <;> fin_cases entry <;> fin_cases q <;> cases symbol <;>
    simp [PSTRTMMulRewind085.rewindMachine] at old <;>
    rcases old with ⟨rfl,rfl⟩ <;> rfl

private theorem retained_step {a : Nat} (oldMachine : Machine a)
    (labelMap : Fin (a+1) → Fin 131)
    (commands : ∀ q next symbol statement, oldMachine q symbol=some (next,statement) →
      copyMachine (labelMap q) symbol=some (labelMap next,statement))
    (before after : MachineState a) (old : Turing.TM0.step oldMachine before=some after) :
    Turing.TM0.step copyMachine ⟨labelMap before.q,before.Tape⟩=some ⟨labelMap after.q,after.Tape⟩ := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : oldMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next,statement⟩ := command
      simp only [hc,Option.map_some,Option.some.injEq] at old
      subst after
      have hm := commands q next tape.head statement hc
      simp only [Turing.TM0.step,hm,Option.map_some]

theorem cursor_chain (bit : Bool) (entry : Fin 3) (trace : List (MachineState 2))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdCursor115.cursorMachine before=some after)) :
    (trace.map (liftCursor bit entry)).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact h.imp (fun before after old => retained_step _ _ (cursor_command bit entry) before after old)

theorem rewind_chain (bit : Bool) (entry : Fin 3) (trace : List (MachineState 3))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMMulRewind085.rewindMachine before=some after)) :
    (trace.map (liftRewind bit entry)).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact h.imp (fun before after old => retained_step _ _ (rewind_command bit entry) before after old)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyRoundLift129
