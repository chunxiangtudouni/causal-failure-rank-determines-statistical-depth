module
public import Structure.PA17_TM_RatArithmetic_CopyLoop_042a

/-! The frozen031 induction, now parameterized by two actual fixed
excursions. The loop terminates at the real SOURCE local footer. Final
navigation, canonical source restoration, and DEST output belong to callers. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopyLoop042
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

variable {s : Nat}

theorem loop_bounded (h : 8≤s) (excursions : Bool → Machine s) (last : Fin (s+1))
    (context : List Bool) (work : List Bool → List Bool) (fee : List Bool → List Bool → Nat)
    (correct : ExcursionCorrect excursions last context work fee)
    (end_false : ∀ copied, (context++work copied).head?=some false)
    (digits left copied : List Bool) (first_false : (copied++digits).headD false=false) :
    BoundedRun (loopMachine h excursions last)
      (Tape.mk₂ left (sourceWord context work digits copied)) (haltLabel h)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft left digits)
        (context++work (copied++digits))) (loopFee fee copied digits) := by
  induction digits generalizing left copied with
  | nil =>
    have hc := suffix_false (context++work copied) (end_false copied)
    have hr := reader_eof_bounded h left ((context++work copied).tail)
    rw [← hc] at hr
    obtain ⟨trace,hr,hl⟩ := hr
    have hb := block_runsFrom (rows h excursions) (ports last) 0 _ _ trace hr
      (by simp [ports,eofPort,padLabel])
    refine ⟨trace.map (blockCfg (p:=2) (s:=s) (0 : Fin 3)),?_,?_⟩
    · simpa only [blockCfg_zero,block_eof,loopMachine,sourceWord,PSTRTMIncrement009.blocks,List.flatMap_nil,
        List.nil_append,List.append_nil,PA17TMRatArithmeticFarLoad031.passedLeft] using hb
    · change (trace.map (blockCfg (p:=2) (s:=s) (0 : Fin 3))).length≤3
      simpa only [List.length_map] using hl
  | cons bit later ih =>
    let suffix := sourceWord context work later copied
    obtain ⟨tr,hr,hlr⟩ := reader_data_bounded h left bit suffix
    have hre : PSTRTMSeq005.RunsFrom (rows h excursions 0)
        ⟨0,Tape.mk₂ left (bit::true::suffix)⟩ tr
        ⟨readerPort h bit,Tape.mk₂ (false::bit::left) suffix⟩ := hr
    obtain ⟨te,he,hle⟩ := correct left later copied bit (prefix_false copied bit later first_false)
    have hee : PSTRTMSeq005.RunsFrom (rows h excursions (PA17TMRatArithmeticBookmark014.readPort bit))
        ⟨0,Tape.mk₂ (false::bit::left) suffix⟩ te
        ⟨last,Tape.mk₂ (true::bit::left) (sourceWord context work later (copied++[bit]))⟩ := by
      cases bit <;> exact he
    have ht : ((copied++[bit])++later).headD false=false := by
      simpa only [List.append_assoc,List.singleton_append] using first_false
    obtain ⟨ti,hi,hli⟩ := ih (true::bit::left) (copied++[bit]) ht
    have hs := segment_append (loopMachine h excursions last) _ _ _ _ _ _
      (block_segment (rows h excursions) (ports last) 0 _ _ tr hre)
      (block_segment (rows h excursions) (ports last) (PA17TMRatArithmeticBookmark014.readPort bit) _ _ te hee)
      (block_transfer (rows h excursions) (ports last) 0 _
        (PA17TMRatArithmeticBookmark014.readPort bit,0) hre.2.2.2 (by cases bit <;> rfl))
    have back := block_transfer (rows h excursions) (ports last)
      (PA17TMRatArithmeticBookmark014.readPort bit) _ (0,0) hee.2.2.2
      (by cases bit <;> simp [ports,PA17TMRatArithmeticBookmark014.readPort])
    have back' : TM0.step (loopMachine h excursions last)
        (blockCfg (PA17TMRatArithmeticBookmark014.readPort bit)
          (⟨last,Tape.mk₂ (true::bit::left) (sourceWord context work later (copied++[bit]))⟩ : MachineState s))=
        some (⟨0,Tape.mk₂ (true::bit::left) (sourceWord context work later (copied++[bit]))⟩ : MachineState (totalStates 2 s)) := by
      simpa only [loopMachine,blockCfg_zero] using back
    have hs' := segment_append (loopMachine h excursions last) _ _ _ _ _ _ hs
      ⟨hi.1,hi.2.1,hi.2.2.1⟩ back'
    refine ⟨(tr.map (blockCfg (p:=2) (s:=s) (0 : Fin 3))++
      te.map (blockCfg (p:=2) (s:=s) (PA17TMRatArithmeticBookmark014.readPort bit)))++ti,?_,?_⟩
    · have hr := segment_runsFrom _ _ _ _ hs' hi.2.2.2
      simpa only [blockCfg_zero,suffix,sourceWord,PSTRTMIncrement009.blocks,List.flatMap_cons,
        List.cons_append,List.nil_append,List.append_assoc,List.singleton_append,
        PA17TMRatArithmeticFarLoad031.passedLeft] using hr
    · simp only [List.length_append,List.length_map,loopFee]
      omega

theorem loopFee_affine (fee : List Bool → List Bool → Nat) (alpha delta : Nat)
    (bound : ∀ later copied, fee later copied≤alpha*(later.length+copied.length)+delta)
    (copied digits : List Bool) :
    loopFee fee copied digits≤digits.length*(alpha*(digits.length+copied.length)+delta+5)+3 := by
  induction digits generalizing copied with
  | nil => simp [loopFee]
  | cons bit later ih =>
    have hi := ih (copied++[bit])
    have hf := bound later copied
    simp only [List.length_append,List.length_singleton] at hi
    simp only [loopFee,List.length_cons]
    nlinarith

theorem loop_contract (h : 8≤s) (excursions : Bool → Machine s) (last : Fin (s+1))
    (context : List Bool) (work : List Bool → List Bool) (fee : List Bool → List Bool → Nat)
    (correct : ExcursionCorrect excursions last context work fee)
    (end_false : ∀ copied, (context++work copied).head?=some false)
    (digits left copied : List Bool) (first_false : (copied++digits).headD false=false)
    (inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (loopMachine h excursions last)
      ⟨0,Tape.mk₂ left (sourceWord context work digits copied)⟩ trace
      ⟨haltLabel h,Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft left digits)
        (context++work (copied++digits))⟩ ∧ trace.length≤loopFee fee copied digits ∧
      ∀ k, visitedSpace (loopMachine h excursions last) inputLength (trace.take k) ≤
        inputLength+2*loopFee fee copied digits+1 := by
  obtain ⟨trace,hr,hl⟩ := loop_bounded h excursions last context work fee correct end_false digits left copied first_false
  refine ⟨trace,hr,hl,?_⟩
  intro k
  have hs := PSTRTMTrace002.visitedSpace_le (loopMachine h excursions last) inputLength (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCopyLoop042
