module
public import Structure.PA17_TM_RatArithmetic_Width_018b

/-! The original two-item header and relocated first sign occupy seven
actual cells. These fixed walks cross all seven; the counter is never
obtained by identifying two differently positioned tapes. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018

def sevenMachine (direction : Turing.Dir) : Machine 7 := fun q _ =>
  if h : q.val<7 then some (⟨q.val+1,by omega⟩,.move direction) else none

def sevenState (q : Fin 8) (left right : List Bool) : MachineState 7 := ⟨q,Turing.Tape.mk₂ left right⟩

def prefixLeft (sx : Bool) (counter : List Bool) : List Bool := [false,sx,true,false,false,true,true]++counter

def prefixRight (sx : Bool) (bank : List Bool) : List Bool := [true,true,false,false,true,sx,false]++bank

def leftSevenTrace (sx : Bool) (counter bank : List Bool) : List (MachineState 7) :=
  [sevenState 0 (prefixLeft sx counter) bank,
   sevenState 1 ([sx,true,false,false,true,true]++counter) (false::bank),
   sevenState 2 ([true,false,false,true,true]++counter) (sx::false::bank),
   sevenState 3 ([false,false,true,true]++counter) (true::sx::false::bank),
   sevenState 4 ([false,true,true]++counter) (false::true::sx::false::bank),
   sevenState 5 ([true,true]++counter) (false::false::true::sx::false::bank),
   sevenState 6 (true::counter) (true::false::false::true::sx::false::bank),
   sevenState 7 counter (prefixRight sx bank)]

theorem leftSeven_runsFrom (sx : Bool) (counter bank : List Bool) :
    PSTRTMSeq005.RunsFrom (sevenMachine .left) (sevenState 0 (prefixLeft sx counter) bank)
      (leftSevenTrace sx counter bank) (sevenState 7 counter (prefixRight sx bank)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [leftSevenTrace,List.isChain_cons_cons,Turing.TM0.step,sevenMachine,sevenState,
      prefixLeft,prefixRight,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,sevenMachine,sevenState]

def rightSevenTrace (sx : Bool) (counter bank : List Bool) : List (MachineState 7) :=
  [sevenState 0 counter (prefixRight sx bank),
   sevenState 1 (true::counter) (true::false::false::true::sx::false::bank),
   sevenState 2 ([true,true]++counter) (false::false::true::sx::false::bank),
   sevenState 3 ([false,true,true]++counter) (false::true::sx::false::bank),
   sevenState 4 ([false,false,true,true]++counter) (true::sx::false::bank),
   sevenState 5 ([true,false,false,true,true]++counter) (sx::false::bank),
   sevenState 6 ([sx,true,false,false,true,true]++counter) (false::bank),
   sevenState 7 (prefixLeft sx counter) bank]

theorem rightSeven_runsFrom (sx : Bool) (counter bank : List Bool) :
    PSTRTMSeq005.RunsFrom (sevenMachine .right) (sevenState 0 counter (prefixRight sx bank))
      (rightSevenTrace sx counter bank) (sevenState 7 (prefixLeft sx counter) bank) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [rightSevenTrace,List.isChain_cons_cons,Turing.TM0.step,sevenMachine,sevenState,
      prefixLeft,prefixRight,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,sevenMachine,sevenState]

def headerRightMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (2,.move .right)
  | _ => none

def headerRightTrace (left : List Bool) (near far : Bool) (right : List Bool) : List (MachineState 2) :=
  [markState 0 left (near::far::right),markState 1 (near::left) (far::right),
   markState 2 (far::near::left) right]

theorem headerRight_runsFrom (left : List Bool) (near far : Bool) (right : List Bool) :
    PSTRTMSeq005.RunsFrom headerRightMachine (markState 0 left (near::far::right))
      (headerRightTrace left near far right) (markState 2 (far::near::left) right) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [headerRightTrace,List.isChain_cons_cons,Turing.TM0.step,headerRightMachine,markState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,headerRightMachine,markState]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
