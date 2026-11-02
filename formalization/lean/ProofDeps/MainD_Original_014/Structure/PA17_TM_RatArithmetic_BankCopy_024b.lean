module
public import Structure.PA17_TM_RatArithmetic_BankCopy_024a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
open PA17TMRatArithmeticCopy006 (pairScan backScan writeTrace workspaceRound sourceReturn
  workData workFlag writeData)

theorem lookup_core (q : Fin 43) (symbol : Bool)
    (hq : q.val ∉ [0,5,18,19,38,42]) :
    copyMachine (oldLabel q) symbol =
      (PA17TMRatArithmeticCopy006.copyMachine q symbol).map (fun p => (oldLabel p.1,p.2)) := by
  rcases q with ⟨q,hbound⟩
  interval_cases q <;> simp_all [copyMachine,oldLabel,PSTRTMSeq005.leftLabel]

theorem step_old (s : MachineState 42)
    (hlookup : copyMachine (oldLabel s.q) s.Tape.head =
      (PA17TMRatArithmeticCopy006.copyMachine s.q s.Tape.head).map (fun p => (oldLabel p.1,p.2))) :
    Turing.TM0.step copyMachine (oldCfg s) =
      (Turing.TM0.step PA17TMRatArithmeticCopy006.copyMachine s).map oldCfg := by
  cases s with
  | mk q tape =>
    unfold Turing.TM0.step oldCfg PSTRTMSeq005.leftCfg
    change (copyMachine (oldLabel q) tape.head).map _ = _
    rw [hlookup]
    cases hm : PA17TMRatArithmeticCopy006.copyMachine q tape.head with
    | none => simp [hm]
    | some value =>
      obtain ⟨q',statement⟩ := value
      cases statement <;> simp [hm,oldLabel,PSTRTMSeq005.leftLabel]

theorem old_chain (trace : List (MachineState 42))
    (hchain : trace.IsChain (fun a b => Turing.TM0.step PA17TMRatArithmeticCopy006.copyMachine a = some b))
    (hlookup : ∀ s ∈ trace, copyMachine (oldLabel s.q) s.Tape.head =
      (PA17TMRatArithmeticCopy006.copyMachine s.q s.Tape.head).map (fun p => (oldLabel p.1,p.2))) :
    (trace.map oldCfg).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  rw [List.isChain_map]
  apply List.IsChain.imp_of_mem_imp _ hchain
  intro a b ha _ hab
  simpa only [hab,Option.map_some] using step_old a (hlookup a ha)

theorem pairScan_labels (dataQ flagQ : Fin 43) (left suffix digits : List Bool)
    (s : MachineState 42) (hs : s ∈ pairScan dataQ flagQ left suffix digits) :
    s.q = dataQ ∨ s.q = flagQ := by
  induction digits generalizing left with
  | nil =>
    simp only [pairScan,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | cons bit later ih =>
    simp only [pairScan,List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ih _ hs

theorem backScan_labels (flagQ dataQ : Fin 43) (left tail previous : List Bool)
    (s : MachineState 42) (hs : s ∈ backScan flagQ dataQ left tail previous) :
    s.q = flagQ ∨ s.q = dataQ := by
  induction previous generalizing tail with
  | nil =>
    simp only [backScan,List.mem_singleton] at hs
    subst s
    exact Or.inl rfl
  | cons bit previous ih =>
    simp only [backScan,List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ih _ hs

theorem writeTrace_labels (bit : Bool) (left : List Bool) (s : MachineState 42)
    (hs : s ∈ writeTrace bit left) : 24 ≤ s.q.val ∧ s.q.val ≤ 35 := by
  simp only [writeTrace,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases bit <;> norm_num [PA17TMRatArithmeticCopy006.state,PA17TMRatArithmeticCopy006.writeData]

theorem workspaceRound_labels (bit : Bool) (left copied : List Bool) (s : MachineState 42)
    (hs : s ∈ workspaceRound bit left copied) : 20 ≤ s.q.val ∧ s.q.val ≤ 37 := by
  simp only [workspaceRound,List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · have hc := pairScan_labels (workData bit) (workFlag bit) (false::left) [] copied s hs
    rcases hc with h | h <;> rw [h] <;> cases bit <;> decide
  · have hc := writeTrace_labels bit
      (PSTRTMRawNat010.leftBlocks copied.reverse ++ false::left) s hs
    omega
  · have hc := backScan_labels 36 37 left [bit,true,false,false] copied.reverse s hs
    rcases hc with h | h <;> rw [h] <;> decide

def workspaceTrace (bit : Bool) (left copied : List Bool) : List (MachineState 58) :=
  (workspaceRound bit left copied).map oldCfg

theorem workspaceTrace_chain (bit : Bool) (left copied : List Bool) :
    (workspaceTrace bit left copied).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  apply old_chain _ (PA17TMRatArithmeticCopy006.workspaceRound_chain bit left copied)
  intro s hs
  apply lookup_core
  have hc := workspaceRound_labels bit left copied s hs
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  omega

def sourceTrace (bit : Bool) (left later tail : List Bool) : List (MachineState 58) :=
  (sourceReturn bit left later tail).map oldCfg

theorem sourceTrace_chain (bit : Bool) (left later tail : List Bool) :
    (sourceTrace bit left later tail).IsChain (fun a b => Turing.TM0.step copyMachine a = some b) := by
  apply old_chain _ (PA17TMRatArithmeticCopy006.sourceReturn_chain bit left later tail)
  intro s hs
  simp only [sourceReturn,List.mem_append,List.mem_singleton] at hs
  rcases hs with (rfl | hs) | rfl
  · rfl
  · apply lookup_core
    have hc := backScan_labels 39 40 (bit::left) (false::false::tail) later.reverse s hs
    rcases hc with h | h <;> rw [h] <;> decide
  · rfl

theorem workspaceTrace_length (bit : Bool) (left copied : List Bool) :
    (workspaceTrace bit left copied).length = 4*copied.length+14 := by
  simp only [workspaceTrace,List.length_map,PA17TMRatArithmeticCopy006.workspaceRound_length]

theorem sourceTrace_length (bit : Bool) (left later tail : List Bool) :
    (sourceTrace bit left later tail).length = 2*later.length+3 := by
  simp only [sourceTrace,List.length_map,PA17TMRatArithmeticCopy006.sourceReturn_length]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankCopy024
