module
public import Structure.B23_5_RawInit_Dispatch018
public import Structure.B23_5_RawInit_Small0_003
public import Structure.B23_5_RawInit_SingletonPad026
public import Structure.B23_5_RawInit_Small23_015
public import Structure.B23_5_RawInit_LargeArchive010

/-! One original-input program covers all five real count branches.
The empty branch already emits exact Fin16; nonempty branches emit their
entire physical archives. The singleton callee really pads its work bank
to two digits, retaining the original count bank. This front does not claim that
the pending archive-to-staging producer has been supplied. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.PaddedFront
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicRawLoop
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRTMIncrement009
open RationalControllerComputation.PSTRSymbolicPairedArchive

noncomputable def sizes : Fin 5 → Nat :=
  Fin.cases 476 (Fin.cases 241 (Fin.cases 750
    (Fin.cases 860 (Fin.cases (750+Remaining.support.card+1) Fin.elim0))))

noncomputable def callees : ∀ tag, Machine (sizes tag) :=
  Fin.cases Small0Fixed.machine (Fin.cases SingletonPad.machine (Fin.cases Small23.twoMachine
    (Fin.cases Small23.threeMachine (Fin.cases LargeArchive.machine (fun tag => Fin.elim0 tag)))))

def outcome : List Datum → Tape Bool → Prop
  | [],tape => tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode []))
  | [first],tape => tape=Tape.mk₂ ((pairedDatum first).reverse++SingletonPad.header) [true]
  | [first,second],tape => tape=Tape.mk₂ (countedPairLeft first second []) [true]
  | [first,second,third],tape => tape=Tape.mk₂
      ((pairedDatum third).reverse++countedPairLeft first second [third]) [true]
  | first::second::third::fourth::later,tape =>
      let data:=first::second::third::fourth::later
      let digits:=PSTRTMNatValue017.rawPayload data.length
      ∃ endDigits, tape=archiveTape data (false::HeaderCopy.bank digits) endDigits [] true ∧
        valueDigits endDigits=0 ∧ endDigits.length=digits.length

theorem square_le_cube (size : Nat) : (size+1)^2≤(size+1)^3 := by
  nlinarith only [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem small_time (size coefficient : Nat) (room : coefficient≤31000) :
    coefficient*(size+1)^2≤31000*(size+1)^3 :=
  (Nat.mul_le_mul_right _ room).trans (Nat.mul_le_mul_left _ (square_le_cube size))

theorem selected_actual (data : List Datum) :
    ∃ path final, Runs (callees (countTag data.length)) (encode data) path final ∧
      outcome data final.Tape ∧ path.length≤31000*((encode data).length+1)^3 := by
  rcases data with _ | ⟨first,data⟩
  · change ∃ path final, Runs Small0Fixed.machine (encode []) path final ∧
      outcome [] final.Tape ∧ path.length≤31000*((encode []).length+1)^3
    obtain ⟨path,final,run,_port,tape,time,_space⟩:=Small0Fixed.actual
    refine ⟨path,final,run,tape,?_⟩
    have positive : 0<((encode []).length+1)^3 := by positivity
    rw [time]
    omega
  rcases data with _ | ⟨second,data⟩
  · obtain ⟨path,final,run,tape,time,_space⟩:=SingletonPad.actual first
    exact ⟨path,final,run,tape,time.trans (small_time _ _ (by decide))⟩
  rcases data with _ | ⟨third,data⟩
  · obtain ⟨path,final,run,tape,time,_space⟩:=Small23.actual_two first second
    exact ⟨path,final,run,tape,time.trans (small_time _ _ (by decide))⟩
  rcases data with _ | ⟨fourth,later⟩
  · obtain ⟨path,final,run,tape,time,_space⟩:=Small23.actual_three first second third
    exact ⟨path,final,run,tape,time.trans (small_time _ _ (by decide))⟩
  have tag : countTag (first::second::third::fourth::later).length=4 := by
    simp only [List.length_cons,countTag]
    split <;> omega
  rw [tag]
  obtain ⟨digits,path,final,run,_port,tape,zero,width,time,_space⟩:=
    LargeArchive.actual first second third fourth later
  exact ⟨path,final,run,⟨digits,tape,zero,width⟩,time⟩

def sink : Machine 0 := fun _ _ => none
noncomputable def front : Machine (Dispatch.support sizes).card := Dispatch.machine sizes callees
noncomputable def machine : Machine ((Dispatch.support sizes).card+0+1) :=
  seqMachine (a:=(Dispatch.support sizes).card) (b:=0) front sink
noncomputable def haltPort : Fin (((Dispatch.support sizes).card+0+1)+1) :=
  rightLabel (a:=(Dispatch.support sizes).card) (b:=0) 0

theorem finish {states : Nat} (callee : Machine states) (input : List Bool)
    (path : List (MachineState states)) (final : MachineState states)
    (run : Runs callee input path final) :
    Runs (seqMachine callee sink) input
      (path.map (leftCfg (b:=0))++[rightCfg (a:=states) (b:=0) ⟨0,final.Tape⟩])
      (rightCfg (a:=states) (b:=0) ⟨0,final.Tape⟩) := by
  apply seq_runs callee sink input final ⟨0,final.Tape⟩ path [⟨0,final.Tape⟩] run
  exact ⟨rfl,List.IsChain.singleton _,rfl,rfl⟩

theorem actual (data : List Datum) : ∃ path final,
    Runs machine (encode data) path final ∧ final.q=haltPort ∧ outcome data final.Tape ∧
      path.length≤32000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace machine (encode data).length (path.take clock)≤
          100000*((encode data).length+1)^3 := by
  classical
  obtain ⟨back,backFinal,backRun,output,backTime⟩:=selected_actual data
  obtain ⟨frontPath,frontRun,frontTime⟩:=Dispatch.actual sizes callees data back backFinal backRun
  let mid:=Dispatch.liftCfg sizes (Dispatch.branchCfg sizes (countTag data.length) backFinal)
  let path:=frontPath.map (leftCfg (b:=0))++[rightCfg (a:=(Dispatch.support sizes).card) (b:=0) ⟨0,mid.Tape⟩]
  let final:=rightCfg (a:=(Dispatch.support sizes).card) (b:=0) ⟨0,mid.Tape⟩
  have time : path.length≤32000*((encode data).length+1)^3 := by
    simp only [path,List.length_append,List.length_map,List.length_cons,List.length_nil]
    have positive : 0<((encode data).length+1)^3 := by positivity
    omega
  refine ⟨path,final,finish front (encode data) frontPath mid frontRun,rfl,output,time,?_⟩
  intro clock
  have cells:=PSTRTMTrace002.visitedSpace_le machine (encode data).length (path.take clock)
  have short:=(List.length_take_le' clock path).trans time
  have inputRoom : (encode data).length≤((encode data).length+1)^3 := by
    nlinarith only [Nat.zero_le ((encode data).length^2),Nat.zero_le ((encode data).length^3)]
  have positive : 0<((encode data).length+1)^3 := by positivity
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.PaddedFront
