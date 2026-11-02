module
public import Common.PSTR_TM_PaddingTrace_014

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMFullRawPadding015
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrace002 PSTRTMPaddedNat012 PSTRTMPaddingTrace014

/-- Same actual tape; only the finite raw-prefix control label is embedded. -/
def liftRaw (old : MachineState 16) : MachineState 106 := ⟨embedRaw old.q, old.Tape⟩

def EntrySafe (old : MachineState 16) : Prop := old.q.val ≠ 0 ∨ old.Tape.head = true

theorem raw_lookup (q : Fin 17) (symbol : Bool) (h : q.val ≠ 0 ∨ symbol = true) :
    paddedNatMachine (embedRaw q) symbol =
      (PSTRTMRawNat010.rawNatMachine q symbol).map (fun (next, statement) => (embedRaw next, statement)) := by
  have hover : ¬(q.val = 0 ∧ symbol = false) := by
    rcases h with hn | hs
    · exact fun hh => hn hh.1
    · intro hh
      rw [hs] at hh
      cases hh.2
  simp only [paddedNatMachine, embedRaw, dite_eq_left q.isLt, Fin.eta]
  exact ite_eq_right hover

theorem raw_step (old : MachineState 16) (h : EntrySafe old) :
    Turing.TM0.step paddedNatMachine (liftRaw old) =
      (Turing.TM0.step PSTRTMRawNat010.rawNatMachine old).map liftRaw := by
  cases old with
  | mk q tape =>
    simp only [liftRaw, Turing.TM0.step]
    rw [raw_lookup q tape.head h]
    cases hm : PSTRTMRawNat010.rawNatMachine q tape.head with
    | none => rfl
    | some value =>
      obtain ⟨next, statement⟩ := value
      cases statement <;> rfl

theorem scanRight_control (n : Nat) (left tail : List Bool) :
    ∀ old ∈ PSTRTMRawNat010.scanRight n left tail, old.q.val = 2 := by
  induction n generalizing left with
  | zero => simp [PSTRTMRawNat010.scanRight, PSTRTMRawNat010.state]
  | succ n ih =>
    simp only [PSTRTMRawNat010.scanRight, List.forall_mem_cons]
    exact ⟨rfl, ih _⟩

theorem scanLeft_control (bit : Bool) (n : Nat) (left tail : List Bool) :
    ∀ old ∈ PSTRTMRawNat010.scanLeft bit n left tail, old.q = PSTRTMRawNat010.leftMode bit := by
  induction n generalizing tail with
  | zero => simp [PSTRTMRawNat010.scanLeft, PSTRTMRawNat010.state]
  | succ n ih =>
    simp only [PSTRTMRawNat010.scanLeft, List.forall_mem_cons]
    exact ⟨rfl, ih _⟩

/-- The raw prefix overrides ONLY state0 on false at the field end. Every
actual rotation has state0 on true, so the frozen raw unit trace is reused
with genuine step equality rather than an assumed performance interface. -/
theorem unit_entry_safe (bit : Bool) (previous later suffix : List Bool) :
    ∀ old ∈ PSTRTMRawNat010.unitTrace bit previous later suffix, EntrySafe old := by
  have hr (old : MachineState 16)
      (h : old ∈ PSTRTMRawNat010.scanRight later.length (false :: PSTRTMRawNat010.leftBlocks previous)
        (bit :: (later ++ suffix))) : EntrySafe old := by
    left
    have hc := scanRight_control _ _ _ old h
    omega
  have hl (old : MachineState 16)
      (h : old ∈ PSTRTMRawNat010.scanLeft bit later.length (PSTRTMRawNat010.leftBlocks previous)
        (true :: false :: (later ++ suffix))) : EntrySafe old := by
    left
    have hc := scanLeft_control bit _ _ _ old h
    cases bit <;> simp [PSTRTMRawNat010.leftMode] at hc <;> omega
  simp only [PSTRTMRawNat010.unitTrace, List.forall_mem_append, List.forall_mem_cons]
  simp only [EntrySafe] at hr hl
  cases bit <;> simp_all [EntrySafe, PSTRTMRawNat010.state, PSTRTMRawNat010.payloadMode,
    PSTRTMRawNat010.markerMode, PSTRTMRawNat010.leftStartMode, Turing.Tape.mk₂,
    List.replicate_succ]

def liftedUnit (bit : Bool) (previous later suffix : List Bool) : List (MachineState 106) :=
  (PSTRTMRawNat010.unitTrace bit previous later suffix).map liftRaw

theorem liftedUnit_head (bit : Bool) (previous later suffix : List Bool) :
    (liftedUnit bit previous later suffix).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous)
        (List.replicate (later.length + 1) true ++ false :: bit :: (later ++ suffix))) := by
  simp only [liftedUnit, List.head?_map, PSTRTMRawNat010.unit_head, Option.map_some]
  rfl

theorem liftedUnit_last (bit : Bool) (previous later suffix : List Bool) :
    (liftedUnit bit previous later suffix).getLast? = some
      (state 15 (bit :: PSTRTMRawNat010.leftBlocks previous)
        (List.replicate (later.length + 1) true ++ false :: (later ++ suffix))) := by
  simp only [liftedUnit, List.getLast?_map, PSTRTMRawNat010.unit_last, Option.map_some]
  rfl

theorem liftedUnit_length (bit : Bool) (previous later suffix : List Bool) :
    (liftedUnit bit previous later suffix).length = 2 * later.length + 10 := by
  simpa [liftedUnit] using PSTRTMRawNat010.unit_length bit previous later suffix

theorem liftedUnit_chain (bit : Bool) (previous later suffix : List Bool) :
    (liftedUnit bit previous later suffix).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  apply (List.isChain_map liftRaw).mpr
  apply (PSTRTMRawNat010.unit_chain bit previous later suffix).imp_of_mem_imp
  intro before after hb _ hs
  rw [raw_step before (unit_entry_safe bit previous later suffix before hb), hs]
  rfl

/-- Exclude the copy-entry configuration so the next stage supplies it
once. Its final flag-read transition is still charged and proved. -/
def oldPrefix (saved : Bool) : List Bool → List Bool → List (MachineState 106)
  | [], right => [state (post saved 4) [] (false :: right)]
  | bit :: previous, right =>
    state (post saved 4) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: right) ::
    state (post saved 5) (PSTRTMRawNat010.leftBlocks previous) (bit :: true :: right) ::
      oldPrefix saved previous (bit :: true :: right)

theorem oldPrefix_head (saved : Bool) (previous right : List Bool) :
    (oldPrefix saved previous right).head? = some (rewindOldInitial saved previous right) := by
  cases previous <;> rfl

theorem oldPrefix_length (saved : Bool) (previous right : List Bool) :
    (oldPrefix saved previous right).length = 2 * previous.length + 1 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have h := ih (bit :: true :: right)
    change (oldPrefix saved previous (bit :: true :: right)).length + 1 + 1 = 2 * (previous.length + 1) + 1
    omega

theorem oldPrefix_last (saved : Bool) (previous right : List Bool) :
    (oldPrefix saved previous right).getLast? = some
      (state (post saved 4) [] (false :: (PSTRTMIncrement009.blocks previous.reverse ++ right))) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : oldPrefix saved previous (bit :: true :: right) ≠ [] := by
      have hlen := oldPrefix_length saved previous (bit :: true :: right)
      intro h
      simp [h] at hlen
    simp only [oldPrefix, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem oldPrefix_chain (saved : Bool) (previous right : List Bool) :
    (oldPrefix saved previous right).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  induction previous generalizing right with
  | nil => exact .singleton _
  | cons bit previous ih =>
    rw [oldPrefix]
    apply List.isChain_cons_cons.mpr
    constructor
    · cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [oldPrefix_head, Option.mem_some_iff] at ha
      subst after
      cases previous <;> cases saved <;>
        simp [rewindOldInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
          paddedNatMachine, post, state, Turing.Tape.mk₂]
    · exact ih _

private theorem tripleBlank (q : Fin 107) (right : List Bool) :
    state q [false] right = state q [false, false, false] right := by
  have hb : Turing.ListBlank.mk [false, false, false] = Turing.ListBlank.mk [false] := by
    exact (PSTRTMRawNat010.blank_append_false [false, false]).trans
      (PSTRTMRawNat010.blank_append_false [false])
  simp only [state, Turing.Tape.mk₂]
  rw [hb]

private theorem append_link (xs ys : List (MachineState 106)) (last first : MachineState 106)
    (hx : xs.IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step paddedNatMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step paddedNatMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def footerTrace (previous : List Bool) : List Bool → List (MachineState 106)
  | [] => markSuffix false (PSTRTMRawNat010.leftBlocks previous) [] ++
    oldPrefix false previous [true, false] ++
      copyLoop false [] previous.reverse false false false []
  | first :: rest => markSuffix first (PSTRTMRawNat010.leftBlocks previous) rest ++
    oldPrefix first previous (true :: false :: rest) ++
      copyLoop first [] previous.reverse false false false rest

theorem footer_length (previous suffix : List Bool) :
    (footerTrace previous suffix).length = 16 * previous.length + 27 := by
  cases suffix <;>
    simp only [footerTrace, List.length_append, markSuffix_length, oldPrefix_length,
      copyLoop_length, List.length_reverse, List.length_nil] <;> omega

theorem footer_chain (previous suffix : List Bool) :
    (footerTrace previous suffix).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  have build (saved : Bool) (rest : List Bool) :
      (markSuffix saved (PSTRTMRawNat010.leftBlocks previous) rest ++
        (oldPrefix saved previous (true :: false :: rest) ++
          copyLoop saved [] previous.reverse false false false rest)).IsChain
        (fun before after => Turing.TM0.step paddedNatMachine before = some after) := by
    have hc := copyLoop_chain saved [] previous.reverse false false false rest
    have ho := oldPrefix_chain saved previous (true :: false :: rest)
    have hop := append_link (oldPrefix saved previous (true :: false :: rest))
      (copyLoop saved [] previous.reverse false false false rest) _ _ ho hc
      (oldPrefix_last saved previous _) (copyLoop_head saved [] previous.reverse false false false rest)
      (by
        have hstep : Turing.TM0.step paddedNatMachine
            (state (post saved 4) [] (false :: (PSTRTMIncrement009.blocks previous.reverse ++ true :: false :: rest))) =
            some (state (post saved 6) [false] (PSTRTMIncrement009.blocks previous.reverse ++ true :: false :: rest)) := by
          cases saved <;> simp [Turing.TM0.step, paddedNatMachine, post, state, Turing.Tape.mk₂]
        simpa only [PSTRTMRawNat010.leftBlocks,
          List.flatMap_nil, List.nil_append, tripleBlank] using hstep)
    have hhead : (oldPrefix saved previous (true :: false :: rest) ++
        copyLoop saved [] previous.reverse false false false rest).head? =
        some (rewindOldInitial saved previous (true :: false :: rest)) := by
      simp [List.head?_append, oldPrefix_head]
    apply append_link _ _ _ _ (markSuffix_chain saved _ rest) hop (by rfl) hhead
    cases previous <;> cases saved <;>
      simp [rewindOldInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
        paddedNatMachine, post, state, Turing.Tape.mk₂]
  cases suffix with
  | nil => simpa only [footerTrace, List.append_assoc] using build false []
  | cons first rest => simpa only [footerTrace, List.append_assoc] using build first rest

theorem footer_head (previous suffix : List Bool) :
    (footerTrace previous suffix).head? =
      some (state 0 (PSTRTMRawNat010.leftBlocks previous) (false :: suffix)) := by
  cases suffix with
  | nil =>
    simp only [footerTrace, List.head?_append, markSuffix, List.head?_cons,
      Option.some_or]
    congr 1
    simp only [state, Turing.Tape.mk₂]
    rw [show Turing.ListBlank.mk [false, false] = Turing.ListBlank.mk [false] from
      PSTRTMRawNat010.blank_append_false [false]]
  | cons first rest => rfl

theorem footer_last (previous suffix : List Bool) :
    (footerTrace previous suffix).getLast? = some
      (state (post suffix.headI 44) [false]
        (PSTRTMIncrement009.blocks previous.reverse ++ false :: false :: true :: false :: suffix)) := by
  cases suffix with
  | nil =>
    simp only [footerTrace, List.getLast?_append, copyLoop_last,
      List.reverse_nil, List.nil_append]
    simp only [state, Turing.Tape.mk₂]
    rw [show PSTRTMIncrement009.blocks previous.reverse ++ [false, false, true, false, false] =
      (PSTRTMIncrement009.blocks previous.reverse ++ [false, false, true, false]) ++ [false] by
      simp only [List.append_assoc]; rfl]
    rw [PSTRTMRawNat010.blank_append_false]
    rfl
  | cons first rest =>
    simp [footerTrace, List.getLast?_append, copyLoop_last]

/-- Actual raw-prefix rotations followed by footer creation and copy-back.
The proof invariant previous is tape content, never extra runtime input. -/
def paddedTrace (previous : List Bool) : List Bool → List Bool → List (MachineState 106)
  | [], suffix => footerTrace previous suffix
  | bit :: later, suffix => liftedUnit bit previous later suffix ++ paddedTrace (bit :: previous) later suffix

theorem padded_head (previous digits suffix : List Bool) :
    (paddedTrace previous digits suffix).head? = some
      (state 0 (PSTRTMRawNat010.leftBlocks previous)
        (List.replicate digits.length true ++ false :: (digits ++ suffix))) := by
  cases digits with
  | nil => simpa only [paddedTrace, List.length_nil, List.replicate_zero, List.nil_append] using footer_head previous suffix
  | cons bit later => simp [paddedTrace, List.head?_append, liftedUnit_head]

theorem padded_length (previous digits suffix : List Bool) :
    (paddedTrace previous digits suffix).length =
      digits.length ^ 2 + 25 * digits.length + 16 * previous.length + 27 := by
  induction digits generalizing previous with
  | nil => simpa [paddedTrace] using footer_length previous suffix
  | cons bit later ih =>
    simp only [paddedTrace, List.length_append, liftedUnit_length, ih, List.length_cons]
    ring

theorem padded_last (previous digits suffix : List Bool) :
    (paddedTrace previous digits suffix).getLast? = some
      (state (post suffix.headI 44) [false]
        (PSTRTMIncrement009.blocks (previous.reverse ++ digits) ++ false :: false :: true :: false :: suffix)) := by
  induction digits generalizing previous with
  | nil => simpa [paddedTrace] using footer_last previous suffix
  | cons bit later ih =>
    simp [paddedTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem padded_chain (previous digits suffix : List Bool) :
    (paddedTrace previous digits suffix).IsChain (fun before after =>
      Turing.TM0.step paddedNatMachine before = some after) := by
  induction digits generalizing previous with
  | nil => exact footer_chain previous suffix
  | cons bit later ih =>
    rw [paddedTrace]
    apply append_link _ _ _ _ (liftedUnit_chain bit previous later suffix) (ih (bit :: previous))
      (liftedUnit_last bit previous later suffix) (padded_head (bit :: previous) later suffix)
    simp [Turing.TM0.step, paddedNatMachine, embedRaw, PSTRTMRawNat010.rawNatMachine,
      state, Turing.Tape.mk₂, PSTRTMRawNat010.leftBlocks, List.replicate_succ]

/-- The original unexpanded unary length and raw Bool payload are consumed
by this single fixed107-label program, with every suffix bit retained. -/
theorem padded_runs (digits suffix : List Bool) :
    Runs paddedNatMachine (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (paddedTrace [] digits suffix)
      (state (post suffix.headI 44) [false]
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, state, PSTRTMRawNat010.leftBlocks] using padded_head [] digits suffix
  · exact padded_chain [] digits suffix
  · simpa using padded_last [] digits suffix
  · exact padded_halt _ _ _

theorem paddedNat_computes_frame (digits suffix : List Bool) :
    computes paddedNatMachine (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)
      (512 * (digits.length + 1) ^ 2) (512 * (digits.length + 1) ^ 2 + suffix.length) := by
  refine ⟨paddedTrace [] digits suffix,
    state (post suffix.headI 44) [false]
      (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix),
    padded_runs digits suffix, ?_, ?_, ?_⟩
  · simp [state, Turing.Tape.mk₂]
  · rw [padded_length]
    simp only [List.length_nil]
    nlinarith
  · have hspace := visitedSpace_le paddedNatMachine
      (List.replicate digits.length true ++ false :: (digits ++ suffix)).length (paddedTrace [] digits suffix)
    have htime := padded_length [] digits suffix
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hspace htime ⊢
    nlinarith

theorem padded_final_tape (digits suffix : List Bool) :
    (state (post suffix.headI 44) [false]
      (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix) := by
  simp only [state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMFullRawPadding015

