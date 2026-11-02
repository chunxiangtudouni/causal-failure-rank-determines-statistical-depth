module
public import Common.PSTR_TM_ThresholdDoubleCode_197
public import Common.PSTR_TM_DoubleCode_061

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDoubleTrace198
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDoubleCode197

def writtenLeft (archive written : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks written.reverse ++ false::archive

theorem writtenLeft_snoc (archive written : List Bool) (bit : Bool) :
    writtenLeft archive (written ++ [bit]) = true::bit::writtenLeft archive written := by
  simp [writtenLeft,PSTRTMRawNat010.leftBlocks,List.reverse_append]

def scanTrace (carry : Bool) (archive written : List Bool) : List Bool → List (MachineState 19)
  | [] => endTrace carry (writtenLeft archive written)
  | bit::later => unitTrace carry bit (writtenLeft archive written)
      (PSTRTMIncrement009.blocks later ++ [false,false]) ++
    scanTrace bit archive (written ++ [carry]) later

theorem scan_head (carry : Bool) (archive written digits : List Bool) :
    (scanTrace carry archive written digits).head? = some
      (state (readLabel carry) (writtenLeft archive written)
        (PSTRTMIncrement009.blocks digits ++ [false,false])) := by
  cases digits with
  | nil => rfl
  | cons bit later => simp [scanTrace,List.head?_append,unit_head,PSTRTMIncrement009.blocks]

theorem scan_last (carry : Bool) (archive written digits : List Bool) :
    (scanTrace carry archive written digits).getLast? = some
      (state 19 (writtenLeft archive (written ++ carry::digits)) []) := by
  induction digits generalizing carry written with
  | nil =>
    rw [scanTrace,end_last,writtenLeft_snoc]
  | cons bit later ih =>
    rw [scanTrace,List.getLast?_append,ih]
    simp only [Option.some_or,List.append_assoc,List.singleton_append]

theorem scan_length (carry : Bool) (archive written digits : List Bool) :
    (scanTrace carry archive written digits).length = 5*digits.length + 7 := by
  induction digits generalizing carry written with
  | nil => rfl
  | cons bit later ih =>
    simp only [scanTrace,List.length_append,unitTrace,List.length_cons,List.length_nil,ih]
    omega

theorem scan_chain (carry : Bool) (archive written digits : List Bool) :
    (scanTrace carry archive written digits).IsChain
      (fun a b => Turing.TM0.step scanMachine a = some b) := by
  induction digits generalizing carry written with
  | nil => exact end_chain _ _
  | cons bit later ih =>
    rw [scanTrace]
    apply (unit_chain _ _ _ _).append (ih bit (written ++ [carry]))
    intro before hb after ha
    rw [unit_last] at hb
    rw [scan_head] at ha
    have eb := Option.mem_some_iff.mp hb
    have ea := Option.mem_some_iff.mp ha
    subst before
    subst after
    rw [writtenLeft_snoc]
    exact unit_advance _ _ _ _

private theorem blank_two (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false,false]) = Turing.ListBlank.mk bits := by
  calc
    Turing.ListBlank.mk (bits ++ [false,false]) =
        Turing.ListBlank.mk ((bits ++ [false]) ++ [false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits ++ [false]) := PSTRTMRawNat010.blank_append_false _
    _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _

theorem scan_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom scanMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks digits))
      (scanTrace false archive [] digits)
      (state 19 (writtenLeft archive (false::digits)) []) := by
  refine ⟨?_,scan_chain _ _ _ _,?_,scan_halt _ _⟩
  · rw [scan_head]
    simp [state,readLabel,writtenLeft,PSTRTMRawNat010.leftBlocks,Turing.Tape.mk₂,blank_two]
  · simpa only [List.nil_append] using scan_last false archive [] digits

/-- Fixed24-label actual double, including the real return to the first
digit. The entire arbitrary archive behind its false guard is preserved. -/
def doubleMachine : Machine 23 :=
  PSTRTMSeq005.seqMachine scanMachine PSTRTMMulRewind085.rewindMachine

def doubleTrace (archive digits : List Bool) : List (MachineState 23) :=
  (scanTrace false archive [] digits).map (PSTRTMSeq005.leftCfg (b := 3)) ++
    (PSTRTMPairRewind105.fullTrace archive (false::digits).reverse []).map
      (PSTRTMSeq005.rightCfg (a := 19))

def doubleFinal (archive digits : List Bool) : MachineState 23 :=
  PSTRTMSeq005.rightCfg (a := 19) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks (false::digits)))

theorem double_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom doubleMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)⟩
      (doubleTrace archive digits) (doubleFinal archive digits) := by
  apply PSTRTMSeq005.seq_runsFrom scanMachine PSTRTMMulRewind085.rewindMachine
    (state 0 (false::archive) (PSTRTMIncrement009.blocks digits))
    (state 19 (writtenLeft archive (false::digits)) [])
    (PSTRTMMulRewind085.state 3 (false::archive) (PSTRTMIncrement009.blocks (false::digits)))
    (scanTrace false archive [] digits)
    (PSTRTMPairRewind105.fullTrace archive (false::digits).reverse []) (scan_runsFrom _ _)
  simpa only [List.append_nil,writtenLeft,PSTRTMThresholdDoubleCode197.state,
    PSTRTMMulRewind085.state] using
    PSTRTMPairRewind105.rewind_runsFrom archive (false::digits) []

theorem double_final_tape (archive digits : List Bool) :
    (doubleFinal archive digits).Tape =
      Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (false::digits)) := rfl

theorem double_length (archive digits : List Bool) :
    (doubleTrace archive digits).length = 7*digits.length + 12 := by
  simp only [doubleTrace,List.length_append,List.length_map,scan_length,
    PSTRTMPairRewind105.full_length,List.length_reverse,List.length_cons]
  omega

/-- The shift is canonical for every positive natural; the exact finite
code is also proved on arbitrary flagged digits without a fake zero promise. -/
theorem false_cons_rawPayload (value : Nat) (hv : 0 < value) :
    false::PSTRTMNatValue017.rawPayload value = PSTRTMNatValue017.rawPayload (2*value) := by
  have hz : PSTRTMNatValue017.rawPayload value ≠ [false] := by
    intro he
    have hn := PSTRTMNatValue017.valueDigits_rawPayload value
    rw [he] at hn
    change 0 = value at hn
    omega
  have he := PSTRTMDoubleCode061.doubleDigits_rawPayload value
  rw [PSTRTMDoubleCode061.doubleDigits,ite_eq_right hz] at he
  exact he

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDoubleTrace198
