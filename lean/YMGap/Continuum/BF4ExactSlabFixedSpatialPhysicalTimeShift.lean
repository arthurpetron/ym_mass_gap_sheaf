/-
# Physical advances of the intrinsic reflected scalar pairing

Advance increases every natural distance from the fixed reflection plane.
This is not centered chart inclusion, which keeps those distances fixed.
The map preserves all signed coefficients and ordered spatial face words.

Moving one step from the left input to the right input changes the complete
mixed reflected polynomial by one common coordinate lift. The existing
supported padded-congruence and left/right limit-padding laws therefore
prove balance for the SAME time-limit pairing at fixed nome, width and
retained heat stage. Iterating balance gives the sum-of-times identity.

These are genuine scalar laws for physical signed spatial-probe
presentations. No null-quotient operator, completed contraction, positive
one-step transfer, spectral gap, or continuum theory is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection (mirrorSchedule)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Increase each distance from the fixed plane, retaining its ordered face list. -/
def advanceSchedule (n : Nat) (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (e.1+n, e.2))

/-- Physical advance of a signed natural-distance presentation. -/
def advanceSpan (n : Nat) (xs : DistanceSpan) : DistanceSpan :=
  xs.map (fun x => (x.1, advanceSchedule n x.2))

theorem advanceSchedule_zero : (fs : List (Nat × List FaceFactor)) →
    advanceSchedule 0 fs = fs
  | [] => rfl
  | e::es => by
      change e::advanceSchedule 0 es = e::es
      rw [advanceSchedule_zero es]

theorem advanceSpan_zero : (xs : DistanceSpan) → advanceSpan 0 xs = xs
  | [] => rfl
  | x::xs => by
      change (x.1, advanceSchedule 0 x.2)::advanceSpan 0 xs = x::xs
      rw [advanceSchedule_zero, advanceSpan_zero xs]

/-- Successive advances compose by addition, without changing list order. -/
theorem advanceSchedule_add (m n : Nat) : (fs : List (Nat × List FaceFactor)) →
    advanceSchedule (m+n) fs = advanceSchedule n (advanceSchedule m fs)
  | [] => rfl
  | e::es => by
      change (e.1+(m+n), e.2)::advanceSchedule (m+n) es =
        ((e.1+m)+n, e.2)::advanceSchedule n (advanceSchedule m es)
      rw [Nat.add_assoc, advanceSchedule_add m n es]

theorem advanceSpan_add (m n : Nat) : (xs : DistanceSpan) →
    advanceSpan (m+n) xs = advanceSpan n (advanceSpan m xs)
  | [] => rfl
  | x::xs => by
      change (x.1, advanceSchedule (m+n) x.2)::advanceSpan (m+n) xs =
        (x.1, advanceSchedule n (advanceSchedule m x.2))::advanceSpan n (advanceSpan m xs)
      rw [advanceSchedule_add, advanceSpan_add m n xs]

theorem advanceSchedule_succ (n : Nat) (fs : List (Nat × List FaceFactor)) :
    advanceSchedule (n+1) fs = advanceSchedule 1 (advanceSchedule n fs) :=
  advanceSchedule_add n 1 fs

theorem advanceSpan_succ (n : Nat) (xs : DistanceSpan) :
    advanceSpan (n+1) xs = advanceSpan 1 (advanceSpan n xs) :=
  advanceSpan_add n 1 xs

theorem advanceSchedule_append (n : Nat) (fs gs : List (Nat × List FaceFactor)) :
    advanceSchedule n (fs++gs) = advanceSchedule n fs ++ advanceSchedule n gs :=
  List.map_append

theorem advanceSpan_append (n : Nat) (xs ys : DistanceSpan) :
    advanceSpan n (xs++ys) = advanceSpan n xs ++ advanceSpan n ys :=
  List.map_append

theorem advanceSpan_scale (n : Nat) (c : Q') (xs : DistanceSpan) :
    advanceSpan n (scaleSpan c xs) = scaleSpan c (advanceSpan n xs) := by
  simp only [advanceSpan, scaleSpan, List.map_map, Function.comp_def]

/-- Physical advancement does not change the original spatial-face domain. -/
theorem advanceSpan_physical {width : Nat} (n : Nat) (xs : DistanceSpan)
    (hf : Physical width xs) : Physical width (advanceSpan n xs) := by
  intro x hx e he f hmem
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  exact hf y hy g hg f hmem

theorem scheduleRadius_advance_le (n : Nat) : (fs : List (Nat × List FaceFactor)) →
    scheduleRadius (advanceSchedule n fs) ≤ scheduleRadius fs+n
  | [] => Nat.zero_le _
  | e::es => by
      change max (e.1+n) (scheduleRadius (advanceSchedule n es)) ≤
        max e.1 (scheduleRadius es)+n
      exact Nat.max_le.mpr
        ⟨Nat.add_le_add_right (Nat.le_max_left _ _) n,
          Nat.le_trans (scheduleRadius_advance_le n es)
            (Nat.add_le_add_right (Nat.le_max_right _ _) n)⟩

/-- An upper bound, not an equality: empty schedules retain radius zero. -/
theorem radius_advance_le (n : Nat) : (xs : DistanceSpan) →
    radius (advanceSpan n xs) ≤ radius xs+n
  | [] => Nat.zero_le _
  | x::xs => by
      change max (scheduleRadius (advanceSchedule n x.2)) (radius (advanceSpan n xs)) ≤
        max (scheduleRadius x.2) (radius xs)+n
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (scheduleRadius_advance_le n x.2)
            (Nat.add_le_add_right (Nat.le_max_left _ _) n),
          Nat.le_trans (radius_advance_le n xs)
            (Nat.add_le_add_right (Nat.le_max_right _ _) n)⟩

/-- Advance the plane's chart radius and the distance together: the
polynomial offset is unchanged. This differs from centered inclusion. -/
theorem encodeSchedule_advance (h n : Nat) : (fs : List (Nat × List FaceFactor)) →
    encodeSchedule (h+n) (advanceSchedule n fs) = encodeSchedule h fs
  | [] => rfl
  | e::es => by
      change ((h+n)-(e.1+n), e.2)::encodeSchedule (h+n) (advanceSchedule n es) =
        (h-e.1, e.2)::encodeSchedule h es
      rw [Nat.add_sub_add_right, encodeSchedule_advance h n es]

theorem encodeChart_advance (h n : Nat) : (xs : DistanceSpan) →
    encodeChart (h+n) (advanceSpan n xs) = encodeChart h xs
  | [] => rfl
  | x::xs => by
      change (x.1, encodeSchedule (h+n) (advanceSchedule n x.2))::
          encodeChart (h+n) (advanceSpan n xs) =
        (x.1, encodeSchedule h x.2)::encodeChart h xs
      rw [encodeSchedule_advance, encodeChart_advance h n xs]

private theorem mirrorSchedule_advance_one (h : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (hf : ∀ e, e ∈ fs → e.1 ≤ h) →
    mirrorSchedule (h+1) (encodeSchedule (h+1) (advanceSchedule 1 fs)) =
      shiftSchedule (mirrorSchedule (h+1) (encodeSchedule (h+1) fs))
  | [], _ => rfl
  | e::es, hf => by
      have he := hf e List.mem_cons_self
      have htime : 2*(h+1)-((h+1)-(e.1+1)) =
          (2*(h+1)-((h+1)-e.1))+1 := by omega
      change (2*(h+1)-((h+1)-(e.1+1)), e.2)::
          mirrorSchedule (h+1) (encodeSchedule (h+1) (advanceSchedule 1 es)) =
        ((2*(h+1)-((h+1)-e.1))+1, e.2)::
          shiftSchedule (mirrorSchedule (h+1) (encodeSchedule (h+1) es))
      rw [htime, mirrorSchedule_advance_one h es
        (fun f hmem => hf f (List.mem_cons_of_mem e hmem))]

private theorem mirrorSpan_advance_one (h : Nat) :
    (xs : DistanceSpan) → (hx : radius xs ≤ h) →
    mirrorSpan (h+1) (encodeChart (h+1) (advanceSpan 1 xs)) =
      shiftSpan (mirrorSpan (h+1) (encodeChart (h+1) xs))
  | [], _ => rfl
  | x::xs, hx => by
      have hhead : ∀ e, e ∈ x.2 → e.1 ≤ h := fun e he =>
        Nat.le_trans (scheduleRadius_within x.2 e he)
          (Nat.le_trans (Nat.le_max_left _ _) hx)
      have htail : radius xs ≤ h := Nat.le_trans (Nat.le_max_right _ _) hx
      change (x.1, mirrorSchedule (h+1) (encodeSchedule (h+1) (advanceSchedule 1 x.2)))::
          mirrorSpan (h+1) (encodeChart (h+1) (advanceSpan 1 xs)) =
        (x.1, shiftSchedule (mirrorSchedule (h+1) (encodeSchedule (h+1) x.2)))::
          shiftSpan (mirrorSpan (h+1) (encodeChart (h+1) xs))
      rw [mirrorSchedule_advance_one h x.2 hhead, mirrorSpan_advance_one h xs htail]

/-- Advancing the reflected input instead of the unreflected input
translates their WHOLE mixed polynomial by exactly one slice. -/
theorem mixedProduct_time_balance (blocks width h : Nat) (xs ys : DistanceSpan)
    (hx : radius xs ≤ h) (hy : radius ys ≤ h) :
    PaddedPolynomialCoeffEqv blocks
      (mixedProduct width (h+1) (encodeChart (h+1) (advanceSpan 1 xs)) (encodeChart (h+1) ys))
      (liftBoundary (N width)
        (mixedProduct width (h+1) (encodeChart (h+1) xs)
          (encodeChart (h+1) (advanceSpan 1 ys)))) := by
  have hright : encodeChart (h+1) ys = shiftSpan (encodeChart (h+1) (advanceSpan 1 ys)) := by
    rw [encodeChart_advance h 1 ys]
    exact encodeChart_succ h ys hy
  unfold mixedProduct
  rw [mirrorSpan_advance_one h xs hx, hright, lift_product]
  exact (sourceSpan_shift blocks width (mirrorSpan (h+1) (encodeChart (h+1) xs))).mul
    (sourceSpan_shift blocks width (encodeChart (h+1) (advanceSpan 1 ys)))

/-- Actual one-step balance at the fixed reflection plane. The common
coordinate lift is removed only through the already-proved window-limit
padding laws, not by a finite-boundary stationarity assertion. -/
theorem pairing_time_balance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan)
    (_hxf : Physical width xs) (_hyf : Physical width ys) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (advanceSpan 1 xs) ys stage)
      (pairing hw0 hw1 width xs (advanceSpan 1 ys) stage) := by
  let h := max (radius xs) (radius ys)
  let H := h+1
  have hx : radius xs ≤ h := Nat.le_max_left _ _
  have hy : radius ys ≤ h := Nat.le_max_right _ _
  have hxH : radius xs ≤ H := Nat.le_trans hx (Nat.le_succ h)
  have hyH : radius ys ≤ H := Nat.le_trans hy (Nat.le_succ h)
  have hax : radius (advanceSpan 1 xs) ≤ H :=
    Nat.le_trans (radius_advance_le 1 xs) (Nat.add_le_add_right hx 1)
  have hay : radius (advanceSpan 1 ys) ≤ H :=
    Nat.le_trans (radius_advance_le 1 ys) (Nat.add_le_add_right hy 1)
  let p := mixedProduct width H (encodeChart H (advanceSpan 1 xs)) (encodeChart H ys)
  let q := mixedProduct width H (encodeChart H xs) (encodeChart H (advanceSpan 1 ys))
  have hp := mixedProduct_supported width H (encodeChart H (advanceSpan 1 xs))
    (encodeChart H ys) (encodeChart_within H ys hyH)
  have hq := mixedProduct_supported width H (encodeChart H xs)
    (encodeChart H (advanceSpan 1 ys)) (encodeChart_within H (advanceSpan 1 ys) hay)
  have hpin := mixedProduct_time_balance ((2*H+1+1)*(N width)) width h xs ys hx hy
  have hform := Equiv.trans
    (Equiv.symm (windowLimit_pad_right hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) (2*H) p hp))
    (Equiv.trans
      (windowLimit_padded_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        (2*H+1) (windowSupport_right hp) (windowSupport_left hq) hpin)
      (windowLimit_pad_left hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) (2*H) q hq))
  exact Equiv.trans (pairing_chart hw0 hw1 width H (advanceSpan 1 xs) ys hax hyH stage)
    (Equiv.trans hform (Equiv.symm (pairing_chart hw0 hw1 width H xs (advanceSpan 1 ys)
      hxH hay stage)))

/-- Every finite advance on the reflected input may be moved to the
other input. The total physical advance is r+s, at the SAME heat stage. -/
theorem pairing_time_sum {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width r s : Nat) (xs ys : DistanceSpan)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (advanceSpan r xs) (advanceSpan s ys) stage)
      (pairing hw0 hw1 width xs (advanceSpan (r+s) ys) stage) := by
  induction r generalizing s with
  | zero =>
      simpa only [advanceSpan_zero, Nat.zero_add] using
        (Equiv.refl (pairing hw0 hw1 width xs (advanceSpan s ys) stage))
  | succ r ih =>
      rw [advanceSpan_succ r xs]
      have hbalance := pairing_time_balance hw0 hw1 width (advanceSpan r xs) (advanceSpan s ys)
        (advanceSpan_physical r xs hxf) (advanceSpan_physical s ys hyf) stage
      have hrest := ih (s+1)
      rw [advanceSpan_succ s ys] at hrest
      have htime : r+(s+1) = r+1+s := by omega
      rw [htime] at hrest
      exact Equiv.trans hbalance hrest

end YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSchedule_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSchedule_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSchedule_succ
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_succ
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSchedule_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.scheduleRadius_advance_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.radius_advance_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.encodeSchedule_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.encodeChart_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.mixedProduct_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.pairing_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift.pairing_time_sum
