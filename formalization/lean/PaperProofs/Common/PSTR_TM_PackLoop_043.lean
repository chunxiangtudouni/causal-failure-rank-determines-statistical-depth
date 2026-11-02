module
public import PaperProofs.Common.PSTR_TM_PackFinish_039
public import PaperProofs.Common.PSTR_TM_PackZeroA_041
public import PaperProofs.Common.PSTR_TM_PackZeroB_042
public import PaperProofs.Common.PSTR_TM_AddRun_026

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackLoop043
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036

/-- Identify just the shared actual configuration. No real transition
or finite-control transfer is deleted from either segment. -/
def glue (first second : List (MachineState 193)) : List (MachineState 193) := first ++ second.tail

theorem glue_head (first second : List (MachineState 193)) (initial : MachineState 193)
    (hh : first.head? = some initial) : (glue first second).head? = some initial := by
  simp only [glue, List.head?_append, hh, Option.some_or]

theorem glue_last (first second : List (MachineState 193)) (shared final : MachineState 193)
    (hl : first.getLast? = some shared) (hh : second.head? = some shared)
    (he : second.getLast? = some final) : (glue first second).getLast? = some final := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hh
  cases tail with
  | nil =>
    have hf : shared = final := Option.some.inj he
    simpa only [glue, List.tail_cons, List.append_nil, hf] using hl
  | cons next rest =>
    simp only [glue, List.tail_cons]
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    simpa only [List.getLast?_cons_cons] using he

theorem glue_chain (first second : List (MachineState 193)) (shared : MachineState 193)
    (hf : first.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hs : second.IsChain (fun a b => Turing.TM0.step packMachine a = some b))
    (hl : first.getLast? = some shared) (hh : second.head? = some shared) :
    (glue first second).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hh
  have he : first.dropLast ++ [shared] = first :=
    List.dropLast_append_getLast? shared (by rw [hl]; rfl)
  have hf' : (first.dropLast ++ [shared]).IsChain (fun a b => Turing.TM0.step packMachine a = some b) := by
    rw [he]
    exact hf
  have h := hf'.append_overlap hs (by simp)
  simpa only [he, glue, List.tail_cons] using h

theorem glue_length_le (first second : List (MachineState 193)) :
    (glue first second).length ≤ first.length + second.length := by
  simp only [glue, List.length_append, List.length_tail]
  omega

def pairedDigits (pairs : List (Bool × Bool)) : List Bool := pairs.flatMap (fun pair => [pair.1,pair.2])

theorem pairedDigits_blocks (pairs : List (Bool × Bool)) :
    PSTRTMIncrement009.blocks (pairedDigits pairs) = PSTRTMBinaryAdd024.operandColumns pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change a :: true :: b :: true :: PSTRTMIncrement009.blocks (pairedDigits later) =
      a :: true :: b :: true :: PSTRTMBinaryAdd024.operandColumns later
    rw [ih]

def frontier (previous first second : List Bool) : MachineState 193 :=
  state 0 (PSTRTMRawNat010.leftBlocks previous)
    (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second)

theorem frontier_eq (previous first second : List Bool) :
    frontier previous first second = state 0 (PSTRTMRawNat010.leftBlocks previous)
      (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second) := rfl

theorem state_false_suffix (q : Fin 194) (left right : List Bool) (n : Nat) :
    state q left (right ++ List.replicate n false) = state q left right := by
  simp only [state, Turing.Tape.mk₂]
  rw [PSTRTMPackFinish039.blank_false_suffix]

/-- The recursion is a proof witness for the SINGLE194-label program.
Every recursive call consumes at least one real remaining operand digit.
The runtime has no list/value/width arguments from this definition. -/
def packTrace (previous first second : List Bool) : List (MachineState 193) :=
  match first, second with
  | [], [] => PSTRTMPackFinish039.finishTrace previous
  | a :: later, b :: rest =>
    glue (PSTRTMPackColumns038.columnTrace a b (PSTRTMRawNat010.leftBlocks previous)
      later (PSTRTMIncrement009.blocks rest)) (packTrace (b :: a :: previous) later rest)
  | a :: later, [] =>
    glue (PSTRTMPackZeroB042.zeroBTrace a (PSTRTMRawNat010.leftBlocks previous) later)
      (packTrace (false :: a :: previous) later [])
  | [], b :: rest =>
    glue (PSTRTMPackZeroA041.zeroATrace b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks rest))
      (glue (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks rest))
        (packTrace (b :: false :: previous) [] rest))
termination_by first.length + second.length
decreasing_by
  all_goals simp_wf
  omega

theorem pack_head (previous first second : List Bool) :
    (packTrace previous first second).head? = some (frontier previous first second) := by
  cases first with
  | nil =>
    cases second with
    | nil => simpa [packTrace, frontier, PSTRTMIncrement009.blocks] using PSTRTMPackFinish039.finish_head previous
    | cons b rest =>
      rw [packTrace]
      simpa [frontier, PSTRTMIncrement009.blocks] using
        glue_head (PSTRTMPackZeroA041.zeroATrace b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks rest))
          (glue (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks rest))
            (packTrace (b :: false :: previous) [] rest)) _
          (PSTRTMPackZeroA041.zeroA_head b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks rest))
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have hh := glue_head (PSTRTMPackZeroB042.zeroBTrace a (PSTRTMRawNat010.leftBlocks previous) later)
        (packTrace (false :: a :: previous) later []) _
        (PSTRTMPackZeroB042.zeroB_head a (PSTRTMRawNat010.leftBlocks previous) later)
      have hz : a :: true :: (PSTRTMIncrement009.blocks later ++ [false,false,true,false,false,false]) =
          (a :: true :: (PSTRTMIncrement009.blocks later ++ [false,false,true,false])) ++ List.replicate 2 false := by
        simp [List.append_assoc]
      rw [hz, state_false_suffix] at hh
      simpa [frontier, PSTRTMIncrement009.blocks] using hh
    | cons b rest =>
      rw [packTrace]
      simpa [frontier, PSTRTMIncrement009.blocks, List.append_assoc] using
        glue_head (PSTRTMPackColumns038.columnTrace a b (PSTRTMRawNat010.leftBlocks previous)
          later (PSTRTMIncrement009.blocks rest)) (packTrace (b :: a :: previous) later rest) _
          (PSTRTMPackColumns038.column_head a b (PSTRTMRawNat010.leftBlocks previous) later (PSTRTMIncrement009.blocks rest))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackLoop043
