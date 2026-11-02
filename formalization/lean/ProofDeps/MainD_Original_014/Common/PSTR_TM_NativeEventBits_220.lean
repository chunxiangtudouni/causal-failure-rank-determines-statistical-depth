module
public import Common.PSTR_TM_NativeFieldBits_219

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeEventBits220
open PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMLength004 PSTRTMNativeFieldBits219
variable {I : Instance}

/-! Actual ORIGINAL event serialization costs. Width facts here are
derived from original Prefix below; no runtime certificate is introduced. -/

def eventBits (event : VisibleEvent I) : Nat := ((encodeEvent event).map datumBits).sum

theorem boolDatum_bits (bit : Bool) : datumBits (boolDatum bit) = 4 := by
  cases bit <;> decide

theorem event_arity_le (event : VisibleEvent I) : (encodeEvent event).length ≤ 4 := by
  cases event <;> simp [encodeEvent,encodeHandle]

theorem eventBits_le (event : VisibleEvent I) (observationWidth serialWidth : Nat)
    (serial : natBits (PSTRTMNativeEventSerial212.eventSerial event) ≤ serialWidth)
    (observed : ∀ i symbol, event = .observation i symbol → natBits symbol ≤ observationWidth) :
    eventBits event ≤ 8*(observationWidth+natBits I.stageCount+natBits I.toolCount+serialWidth+4) := by
  cases event with
  | observation i symbol =>
    have hi := stage_bits_le i
    have ho := observed i symbol rfl
    have htag : natBits 0 = 1 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,datumBits,htag]
    omega
  | wrote i bit stamp =>
    have hi := stage_bits_le i
    change natBits stamp ≤ serialWidth at serial
    have htag : natBits 1 = 1 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [boolDatum_bits]
    simp only [datumBits,htag]
    omega
  | report i bit stamp =>
    have hi := stage_bits_le i
    change natBits stamp ≤ serialWidth at serial
    have htag : natBits 2 = 2 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [boolDatum_bits]
    simp only [datumBits,htag]
    omega
  | committed handle tool =>
    have hi := stage_bits_le handle.stage
    have ht := tool_bits_le tool
    change natBits handle.writeSerial ≤ serialWidth at serial
    have htag : natBits 3 = 2 := by decide
    simp only [eventBits,encodeEvent,encodeHandle,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,datumBits,htag]
    omega
  | executed handle tool =>
    have hi := stage_bits_le handle.stage
    have ht := tool_bits_le tool
    change natBits handle.writeSerial ≤ serialWidth at serial
    have htag : natBits 4 = 3 := by decide
    simp only [eventBits,encodeEvent,encodeHandle,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,datumBits,htag]
    omega
  | advanced i =>
    have hi := stage_bits_le i
    have htag : natBits 5 = 3 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,datumBits,htag]
    omega
  | stopped =>
    have htag : natBits 6 = 3 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,datumBits,htag]
    omega
  | abandoned =>
    have htag : natBits 7 = 3 := by decide
    simp only [eventBits,encodeEvent,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,datumBits,htag]
    omega

theorem prefix_eventBits_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (budget : Rat) (event : VisibleEvent I) (hm : event ∈ s.history) :
    eventBits event ≤ 8*((preparationInput input C budget).length+
      natBits I.stageCount+natBits I.toolCount+natBits s.clock+4) := by
  apply eventBits_le event _ _
    (prefix_eventSerial_bits_le input C mode accounting policy seed truth tapes hp event hm)
  intro i symbol he
  have ho : .observation i symbol ∈ s.history := he ▸ hm
  exact prefix_observation_bits_le input C mode accounting policy seed truth tapes hp budget i symbol ho

theorem history_event_arity_le (history : List (VisibleEvent I)) :
    (history.flatMap encodeEvent).length ≤ 4*history.length := by
  induction history with
  | nil => simp
  | cons event later ih =>
    have he := event_arity_le event
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    omega

theorem history_eventBits_le (history : List (VisibleEvent I)) (bound : Nat)
    (hb : ∀ event ∈ history, eventBits event ≤ bound) :
    ((history.flatMap encodeEvent).map datumBits).sum ≤ history.length*bound := by
  induction history with
  | nil => simp
  | cons event later ih =>
    have he := hb event List.mem_cons_self
    have hl := ih (fun e hm => hb e (List.mem_cons_of_mem _ hm))
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.length_cons]
    change eventBits event + ((later.flatMap encodeEvent).map datumBits).sum ≤ (later.length+1)*bound
    calc
      _ ≤ bound+later.length*bound := Nat.add_le_add he hl
      _ = _ := by ring

theorem prefix_history_eventBits_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (budget : Rat) :
    ((s.history.flatMap encodeEvent).map datumBits).sum ≤
      s.history.length*(8*((preparationInput input C budget).length+
        natBits I.stageCount+natBits I.toolCount+natBits s.clock+4)) :=
  history_eventBits_le s.history _ (fun e hm =>
    prefix_eventBits_le input C mode accounting policy seed truth tapes hp budget e hm)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeEventBits220
