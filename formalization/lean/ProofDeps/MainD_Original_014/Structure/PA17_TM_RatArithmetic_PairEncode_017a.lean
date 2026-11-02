module
public import Structure.PA17_TM_RatArithmetic_Unblock_004d
public import Structure.PA17_TM_RatArithmetic_Parse_002g

/-! Two original natural fields are serialized by real inverse calls.
The first B header is physically clamped and then restored by A's marker
inverse. No arbitrary raw-word shift or free separator deletion is used. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017

def payload (n : Nat) : List Bool := PSTRTMNatValue017.rawPayload n

def natTail (n : Nat) : List Bool :=
  List.replicate (Nat.log2 n) true ++ false::payload n

theorem encodeNat_head (n : Nat) : encodeNat n = true::natTail n := by
  simp [encodeNat,natBits,natTail,payload,PSTRTMNatValue017.rawPayload,
    List.replicate_succ,List.append_assoc]

theorem payload_length (n : Nat) : (payload n).length = natBits n := by
  simp [payload,PSTRTMNatValue017.rawPayload]

def aArchive (archive : List Bool) (a : Nat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (payload a).reverse ++ false::archive

/-- footer is a compile-time choice of code, never extra data on the tape. -/
def inverseMachine (footer : Bool) : Machine 19 :=
  if footer then PA17TMRatArithmeticUnblock004.markerMachine else PSTRTMUnblock018.unblockMachine

def inverseTrace (footer : Bool) (archive digits suffix : List Bool) : List (MachineState 19) :=
  if footer then PA17TMRatArithmeticUnblock004.markerTrace archive digits suffix
  else PA17TMRatArithmeticUnblock004.framedTrace archive digits suffix

theorem inverse_runsFrom (footer : Bool) (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (inverseMachine footer)
      (PSTRTMUnblock018.state 0 (false::archive) (PSTRTMIncrement009.blocks digits ++ false::false::suffix))
      (inverseTrace footer archive digits suffix)
      (PSTRTMUnblock018.state 19 (false::archive) (PSTRTMUnblockTrace019.rawWord digits ++ footer::suffix)) := by
  cases footer with
  | false => exact PA17TMRatArithmeticUnblock004.framed_runsFrom archive digits suffix
  | true => exact PA17TMRatArithmeticUnblock004.marker_runsFrom archive digits suffix

theorem inverseNat_runsFrom (footer : Bool) (archive suffix : List Bool) (n : Nat) :
    PSTRTMSeq005.RunsFrom (inverseMachine footer)
      (PSTRTMUnblock018.state 0 (false::archive) (PSTRTMIncrement009.blocks (payload n) ++ false::false::suffix))
      (inverseTrace footer archive (payload n) suffix)
      (PSTRTMUnblock018.state 19 (false::archive) (encodeNat n ++ footer::suffix)) := by
  rw [← PA17TMRatArithmeticUnblock004.rawWord_payload]
  exact inverse_runsFrom footer archive (payload n) suffix

theorem inverse_length (footer : Bool) (archive digits suffix : List Bool) :
    (inverseTrace footer archive digits suffix).length =
      digits.length^2+11*digits.length+5+(if footer then 1 else 0) := by
  cases footer with
  | false =>
    change (PA17TMRatArithmeticUnblock004.framedTrace archive digits suffix).length =
      digits.length^2+11*digits.length+5+0
    rw [PA17TMRatArithmeticUnblock004.framed_length]
  | true =>
    change (PA17TMRatArithmeticUnblock004.markerTrace archive digits suffix).length =
      digits.length^2+11*digits.length+5+1
    rw [PA17TMRatArithmeticUnblock004.marker_length]

def clampHeaderMachine : Machine 1 := fun q _ =>
  if q.val=0 then some (1,.write false) else none

def clampHeaderTrace (left tail : List Bool) : List (MachineState 1) :=
  [⟨0,Turing.Tape.mk₂ left (true::tail)⟩,⟨1,Turing.Tape.mk₂ left (false::tail)⟩]

theorem clampHeader_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom clampHeaderMachine ⟨0,Turing.Tape.mk₂ left (true::tail)⟩
      (clampHeaderTrace left tail) ⟨1,Turing.Tape.mk₂ left (false::tail)⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clampHeaderTrace,List.isChain_cons_cons,Turing.TM0.step,clampHeaderMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,clampHeaderMachine]

theorem clampHeader_length (left tail : List Bool) : (clampHeaderTrace left tail).length = 2 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017
