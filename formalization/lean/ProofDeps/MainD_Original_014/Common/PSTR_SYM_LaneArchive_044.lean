module

public import Common.PSTR_SYM_LaneScan_043

/-! The lane scanner's internal no-early-triple condition is supplied by
the actual paired record format, in both physical directions. These pure
facts do not replace the pending actual cursor/counter/global-EOF loop. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneArchive

open PSTRSymbolicLaneScan PSTRSymbolicPairedArchive

theorem seenAfter_append (seen : Fin 3) (first second : List (Bool × Bool)) :
    seenAfter seen (first ++ second) = seenAfter (seenAfter seen first) second := by
  induction first generalizing seen with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    exact ih _

theorem safeNavigation_append (seen : Fin 3) (first second : List (Bool × Bool)) :
    safeNavigation seen (first ++ second) ↔
      safeNavigation seen first ∧ safeNavigation (seenAfter seen first) second := by
  induction first generalizing seen with
  | nil => simp [safeNavigation, seenAfter]
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    simp only [List.cons_append, safeNavigation, seenAfter, ih, and_assoc]

theorem afterSeen_mono (lower upper : Fin 3) (flag : Bool) (bound : lower.val ≤ upper.val) :
    (afterSeen lower flag).val ≤ (afterSeen upper flag).val := by
  fin_cases lower <;> fin_cases upper <;> cases flag <;> simp_all [afterSeen]

theorem safeNavigation_mono (lower upper : Fin 3) (pairs : List (Bool × Bool))
    (bound : lower.val ≤ upper.val) (safe : safeNavigation upper pairs) :
    safeNavigation lower pairs := by
  induction pairs generalizing lower upper with
  | nil => trivial
  | cons pair later ih =>
    obtain ⟨flag,bit⟩ := pair
    change safeFlag upper flag ∧ safeNavigation (afterSeen upper flag) later at safe
    change safeFlag lower flag ∧ safeNavigation (afterSeen lower flag) later
    refine ⟨?_, ih _ _ (afterSeen_mono lower upper flag bound) safe.2⟩
    rcases safe.1 with zero | small
    · exact Or.inl zero
    · exact Or.inr (Nat.lt_of_le_of_lt bound small)

theorem safeNavigation_prefix (seen : Fin 3) (first second : List (Bool × Bool))
    (safe : safeNavigation seen (first ++ second)) : safeNavigation seen first :=
  ((safeNavigation_append seen first second).mp safe).1

theorem safeNavigation_suffix_zero (seen : Fin 3) (first second : List (Bool × Bool))
    (safe : safeNavigation seen (first ++ second)) : safeNavigation 0 second :=
  safeNavigation_mono 0 (seenAfter seen first) second (Nat.zero_le _)
    ((safeNavigation_append seen first second).mp safe).2

def falsePairs (digits : List Bool) : List (Bool × Bool) := digits.map (fun bit => (false,bit))

theorem falsePairs_safe (seen : Fin 3) (digits : List Bool) : safeNavigation seen (falsePairs digits) := by
  induction digits generalizing seen with
  | nil => trivial
  | cons bit later ih =>
    change safeFlag seen false ∧ safeNavigation 0 (falsePairs later)
    exact ⟨Or.inl rfl, ih 0⟩

theorem falsePairs_seen_zero (digits : List Bool) : seenAfter 0 (falsePairs digits) = 0 := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change seenAfter 0 (falsePairs later) = 0
    exact ih

theorem falsePairs_seen_nonempty (seen : Fin 3) (digits : List Bool) (nonempty : digits ≠ []) :
    seenAfter seen (falsePairs digits) = 0 := by
  cases digits with
  | nil => exact False.elim (nonempty rfl)
  | cons bit later => exact falsePairs_seen_zero later

theorem falsePairs_seen_le (seen : Fin 3) (digits : List Bool) :
    (seenAfter seen (falsePairs digits)).val ≤ seen.val := by
  cases digits with
  | nil => exact Nat.le_refl _
  | cons bit later =>
    change (seenAfter 0 (falsePairs later)).val ≤ seen.val
    rw [falsePairs_seen_zero]
    exact Nat.zero_le _

theorem navigationCells_append (first second : List (Bool × Bool)) :
    navigationCells (first ++ second) = navigationCells first ++ navigationCells second := by
  simp only [navigationCells, List.flatMap_append]

theorem falsePairs_cells (digits : List Bool) : navigationCells (falsePairs digits) = zeroPairs digits := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change false :: bit :: navigationCells (falsePairs later) = false :: bit :: zeroPairs later
    rw [ih]

theorem falsePairs_reverse (digits : List Bool) : (falsePairs digits).reverse = falsePairs digits.reverse := by
  exact (List.map_reverse (f := fun bit : Bool => (false,bit)) (l := digits)).symm

def naturalPairs (digits : List Bool) : List (Bool × Bool) := falsePairs digits ++ [(true,false)]

theorem naturalPairs_cells (digits : List Bool) : navigationCells (naturalPairs digits) = naturalWord digits := by
  rw [naturalPairs, navigationCells_append, falsePairs_cells]
  rfl

theorem naturalPairs_safe (seen : Fin 3) (digits : List Bool) (nonempty : digits ≠ []) :
    safeNavigation seen (naturalPairs digits) := by
  rw [naturalPairs, safeNavigation_append, falsePairs_seen_nonempty seen digits nonempty]
  exact ⟨falsePairs_safe seen digits, Or.inr (by decide), trivial⟩

theorem naturalPairs_reverse (digits : List Bool) :
    (naturalPairs digits).reverse = (true,false) :: falsePairs digits.reverse := by
  simp only [naturalPairs, List.reverse_append, falsePairs_reverse, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]

theorem naturalPairs_reverse_safe (digits : List Bool) :
    safeNavigation 0 (naturalPairs digits).reverse := by
  rw [naturalPairs_reverse]
  change safeFlag 0 true ∧ safeNavigation 1 (falsePairs digits.reverse)
  exact ⟨Or.inr (by decide), falsePairs_safe 1 _⟩

theorem naturalPairs_reverse_zero (digits : List Bool) (nonempty : digits ≠ []) :
    seenAfter 0 (naturalPairs digits).reverse = 0 := by
  rw [naturalPairs_reverse]
  change seenAfter 1 (falsePairs digits.reverse) = 0
  apply falsePairs_seen_nonempty
  intro empty
  have original := congrArg List.reverse empty
  exact nonempty (by simpa using original)

def rationalPairs (negative : Bool) (numerator : List Bool) (firstDen : Bool) (laterDen : List Bool) :
    List (Bool × Bool) :=
  [(false,negative)] ++ falsePairs numerator ++ [(true,firstDen)] ++ falsePairs laterDen ++ [(true,true)]

theorem rationalPairs_cells (negative : Bool) (numerator : List Bool) (firstDen : Bool) (laterDen : List Bool) :
    navigationCells (rationalPairs negative numerator firstDen laterDen) =
      rationalWord negative numerator firstDen laterDen := by
  rw [rationalPairs]
  simp only [navigationCells_append]
  rw [falsePairs_cells, falsePairs_cells]
  simp only [navigationCells, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, rationalWord, List.append_assoc]

theorem rationalPairs_safe (seen : Fin 3) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen : List Bool) :
    safeNavigation seen (rationalPairs negative numerator firstDen laterDen) := by
  simp only [rationalPairs, List.append_assoc, List.singleton_append]
  change safeFlag seen false ∧ safeNavigation 0
    (falsePairs numerator ++ (true,firstDen) :: (falsePairs laterDen ++ [(true,true)]))
  refine ⟨Or.inl rfl, (safeNavigation_append _ _ _).mpr ⟨falsePairs_safe _ _, ?_⟩⟩
  rw [falsePairs_seen_zero]
  change safeFlag 0 true ∧ safeNavigation 1 (falsePairs laterDen ++ [(true,true)])
  refine ⟨Or.inr (by decide), (safeNavigation_append _ _ _).mpr ⟨falsePairs_safe _ _, ?_⟩⟩
  change safeFlag (seenAfter 1 (falsePairs laterDen)) true ∧ True
  exact ⟨Or.inr (Nat.lt_of_le_of_lt (falsePairs_seen_le 1 laterDen) (by decide)), trivial⟩

theorem rationalPairs_reverse (negative : Bool) (numerator : List Bool) (firstDen : Bool) (laterDen : List Bool) :
    (rationalPairs negative numerator firstDen laterDen).reverse =
      [(true,true)] ++ falsePairs laterDen.reverse ++ [(true,firstDen)] ++
        falsePairs numerator.reverse ++ [(false,negative)] := by
  simp only [rationalPairs, List.reverse_append, falsePairs_reverse, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc]

theorem rationalPairs_reverse_safe (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen : List Bool) :
    safeNavigation 0 (rationalPairs negative numerator firstDen laterDen).reverse := by
  rw [rationalPairs_reverse]
  simp only [List.append_assoc, List.singleton_append]
  change safeFlag 0 true ∧ safeNavigation 1
    (falsePairs laterDen.reverse ++ (true,firstDen) :: (falsePairs numerator.reverse ++ [(false,negative)]))
  refine ⟨Or.inr (by decide), (safeNavigation_append _ _ _).mpr ⟨falsePairs_safe _ _, ?_⟩⟩
  change safeFlag (seenAfter 1 (falsePairs laterDen.reverse)) true ∧
    safeNavigation (afterSeen (seenAfter 1 (falsePairs laterDen.reverse)) true)
      (falsePairs numerator.reverse ++ [(false,negative)])
  refine ⟨Or.inr (Nat.lt_of_le_of_lt (falsePairs_seen_le 1 laterDen.reverse) (by decide)), ?_⟩
  apply (safeNavigation_append _ _ _).mpr
  exact ⟨falsePairs_safe _ _, Or.inl rfl, trivial⟩

theorem rationalPairs_reverse_zero (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen : List Bool) :
    seenAfter 0 (rationalPairs negative numerator firstDen laterDen).reverse = 0 := by
  rw [rationalPairs_reverse, seenAfter_append]
  rfl

/-! Original Datum payloads supply the nonempty Natural/denominator
qualification. Both scan directions therefore hold for every true raw
Datum prefix, with no extra original-caller fields. -/

open PA17TMRatArithmeticParse002

theorem rawPayload_nonempty (number : Nat) : PSTRTMNatValue017.rawPayload number ≠ [] := by
  obtain ⟨last, earlier, shape⟩ := PSTRSymbolicZeroTail.count_reverse_cons number
  intro empty
  simp only [empty, List.reverse_nil] at shape
  cases shape

def datumPairs : Datum → List (Bool × Bool)
  | .natural number => naturalPairs (PSTRTMNatValue017.rawPayload number)
  | .rational value =>
      match denominatorDigits value with
      | [] => []
      | first :: later => rationalPairs (sign value) (numeratorDigits value) first later

theorem datumPairs_cells (value : Datum) : navigationCells (datumPairs value) = pairedDatum value := by
  cases value with
  | natural number => exact naturalPairs_cells _
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => simp only [datumPairs, shape, pairedDatum, pairedRationalWord, navigationCells, List.flatMap_nil]
    | cons first later =>
      simpa only [datumPairs, shape, pairedDatum, pairedRationalWord] using
        rationalPairs_cells (sign value) (numeratorDigits value) first later

theorem datumPairs_safe (seen : Fin 3) (value : Datum) : safeNavigation seen (datumPairs value) := by
  cases value with
  | natural number => exact naturalPairs_safe seen _ (rawPayload_nonempty number)
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      simpa only [datumPairs, shape] using rationalPairs_safe seen (sign value) (numeratorDigits value) first later

theorem datumPairs_reverse_safe (value : Datum) : safeNavigation 0 (datumPairs value).reverse := by
  cases value with
  | natural number => exact naturalPairs_reverse_safe _
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      simpa only [datumPairs, shape] using rationalPairs_reverse_safe (sign value) (numeratorDigits value) first later

theorem datumPairs_reverse_zero (value : Datum) : seenAfter 0 (datumPairs value).reverse = 0 := by
  cases value with
  | natural number => exact naturalPairs_reverse_zero _ (rawPayload_nonempty number)
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      simpa only [datumPairs, shape] using rationalPairs_reverse_zero (sign value) (numeratorDigits value) first later

def allDatumPairs (data : List Datum) : List (Bool × Bool) := data.flatMap datumPairs

theorem allDatumPairs_cells (data : List Datum) :
    navigationCells (allDatumPairs data) = data.flatMap pairedDatum := by
  induction data with
  | nil => rfl
  | cons value later ih =>
    change navigationCells (datumPairs value ++ allDatumPairs later) = pairedDatum value ++ later.flatMap pairedDatum
    rw [navigationCells_append, datumPairs_cells, ih]

theorem allDatumPairs_safe (seen : Fin 3) (data : List Datum) :
    safeNavigation seen (allDatumPairs data) := by
  induction data generalizing seen with
  | nil => trivial
  | cons value later ih =>
    apply (safeNavigation_append seen (datumPairs value) (allDatumPairs later)).mpr
    exact ⟨datumPairs_safe seen value, ih _⟩

theorem allDatumPairs_reverse (data : List Datum) :
    safeNavigation 0 (allDatumPairs data).reverse ∧ seenAfter 0 (allDatumPairs data).reverse = 0 := by
  induction data with
  | nil => exact ⟨trivial, rfl⟩
  | cons value later ih =>
    change safeNavigation 0 (datumPairs value ++ allDatumPairs later).reverse ∧
      seenAfter 0 (datumPairs value ++ allDatumPairs later).reverse = 0
    simp only [List.reverse_append, safeNavigation_append, seenAfter_append, ih.2]
    exact ⟨⟨ih.1, datumPairs_reverse_safe value⟩, datumPairs_reverse_zero value⟩

theorem actual_prefix_safe_both (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) :
    safeNavigation 0 earlier ∧ safeNavigation 0 earlier.reverse := by
  have forward := allDatumPairs_safe 0 data
  have backward := (allDatumPairs_reverse data).1
  rw [shape] at forward
  rw [shape, List.reverse_append] at backward
  exact ⟨safeNavigation_prefix 0 earlier later forward,
    safeNavigation_suffix_zero 0 later.reverse earlier.reverse backward⟩

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLaneArchive
