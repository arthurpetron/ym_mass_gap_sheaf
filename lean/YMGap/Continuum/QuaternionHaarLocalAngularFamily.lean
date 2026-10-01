/-
# Local finite-family angular Cauchy certificate

The row bound counts list occurrences, not distinct labels.  Every assertion is
on the original polynomial Haar carrier and remains valid after insertion of
the same arbitrary certified positive weight.  In particular signed source
and observable cross terms are not discarded.
-/

import YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
import YMGap.Continuum.QuaternionHaarWordDifference
import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation

namespace YMGap.Continuum.QuaternionHaarLocalAngularFamily

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr {I : Type} (xs : List I) (f g : I → RatPoly)
    (h : ∀ i, i ∈ xs → RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (polySum (xs.map f)) (polySum (xs.map g)) := by
  revert h
  induction xs with
  | nil => intro _; exact RatPolyCoeffEqv.refl _
  | cons i rest ih =>
      intro h
      exact (h i List.mem_cons_self).add
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem sum_filter_zero {I : Type} (xs : List I) (mask : I → Bool)
    (f : I → RatPoly)
    (h : ∀ i, i ∈ xs → mask i = false → RatPolyCoeffEqv (f i) polyZero) :
    RatPolyCoeffEqv (polySum (xs.map f))
      (polySum ((xs.filter mask).map f)) := by
  revert h
  induction xs with
  | nil => intro _; exact RatPolyCoeffEqv.refl _
  | cons i rest ih =>
      intro h
      by_cases hi : mask i = true
      · simp only [List.filter_cons, hi, if_true,
          List.map_cons, polySum]
        exact (RatPolyCoeffEqv.refl _).add
          (ih (fun j hj hj0 => h j (List.mem_cons_of_mem i hj) hj0))
      · have hfalse : mask i = false := by cases hb : mask i <;> simp_all
        simp only [List.filter_cons, hfalse, Bool.false_eq_true, if_false,
          List.map_cons, polySum]
        exact ((h i List.mem_cons_self hfalse).add
          (ih (fun j hj hj0 => h j (List.mem_cons_of_mem i hj) hj0))).trans
          (RatPolyCoeffEqv.zero_add _)

private theorem sum_replicate_zero (k : Nat) :
    RatPolyCoeffEqv (polySum (List.replicate k polyZero)) polyZero := by
  induction k with
  | zero => exact RatPolyCoeffEqv.refl _
  | succ k ih =>
      change RatPolyCoeffEqv
        (polyAdd polyZero (polySum (List.replicate k polyZero))) polyZero
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (RatPolyCoeffEqv.zero_add _)

private theorem sum_replicate_square_zero (k : Nat) :
    RatPolyCoeffEqv
      (polySum ((List.replicate k polyZero).map fun p => polyMul p p))
      polyZero := by
  induction k with
  | zero => exact RatPolyCoeffEqv.refl _
  | succ k ih =>
      change RatPolyCoeffEqv
        (polyAdd (polyMul polyZero polyZero)
          (polySum ((List.replicate k polyZero).map fun p => polyMul p p)))
        polyZero
      exact ((RatPolyCoeffEqv.mul_zero_left _).add ih).trans
        (RatPolyCoeffEqv.zero_add _)

private theorem sum_append_zero (ps : List RatPoly) (k : Nat) :
    RatPolyCoeffEqv (polySum (ps ++ List.replicate k polyZero))
      (polySum ps) := by
  exact (RatPolyCoeffEqv.polySum_append ps _).symm.trans
    (((RatPolyCoeffEqv.refl _).add (sum_replicate_zero k)).trans
      (RatPolyCoeffEqv.add_zero _))

private theorem supported_zero (n : Nat) :
    SupportedQuaternionBlocks n polyZero := by
  intro t ht
  exact False.elim (List.not_mem_nil ht)

/-- Finite Cauchy after padding precisely the nonzero row to its certified
length.  Padding by zero avoids division and subtraction of rational bounds. -/
def masked_square_certificate {I : Type} (n D : Nat) (xs : List I)
    (mask : I → Bool) (f : I → RatPoly)
    (hf : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (f i))
    (hzero : ∀ i, i ∈ xs → mask i = false → RatPolyCoeffEqv (f i) polyZero)
    (hcount : (xs.filter mask).length ≤ D) :
    Certificate n
      (polyAdd
        (polySmul (Q'.ofNat D)
          (polySum (xs.map fun i => polyMul (f i) (f i))))
        (polyNeg (polyMul (polySum (xs.map f)) (polySum (xs.map f))))) := by
  let kept := xs.filter mask
  let padded := kept.map f ++ List.replicate (D - kept.length) polyZero
  have hlen : padded.length = D := by
    simp only [padded, List.length_append, List.length_map, List.length_replicate]
    have hc : kept.length ≤ D := by simpa only [kept] using hcount
    omega
  have hpad : ∀ p, p ∈ padded → SupportedQuaternionBlocks n p := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      exact hf i (List.mem_filter.mp hi).1
    · have hp0 : p = polyZero := (List.mem_replicate.mp hp).2
      rw [hp0]
      exact supported_zero n
  have hsum : RatPolyCoeffEqv (polySum padded) (polySum (xs.map f)) := by
    exact (sum_append_zero (kept.map f) _).trans
      (sum_filter_zero xs mask f hzero).symm
  have hsq : RatPolyCoeffEqv
      (polySum (padded.map fun p => polyMul p p))
      (polySum (xs.map fun i => polyMul (f i) (f i))) := by
    have hpadzero : RatPolyCoeffEqv
        (polySum ((List.replicate (D - kept.length) polyZero).map
          fun p => polyMul p p)) polyZero :=
      sum_replicate_square_zero _
    have hfirst : RatPolyCoeffEqv
        (polySum (padded.map fun p => polyMul p p))
        (polySum (kept.map fun i => polyMul (f i) (f i))) := by
      simp only [padded, List.map_append, List.map_map, Function.comp_def]
      exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans
        (((RatPolyCoeffEqv.refl _).add hpadzero).trans
          (RatPolyCoeffEqv.add_zero _))
    have hfiltered := sum_filter_zero xs mask (fun i => polyMul (f i) (f i))
      (by
        intro i hi hz
        exact ((hzero i hi hz).mul (hzero i hi hz)).trans
          (RatPolyCoeffEqv.mul_zero_left _))
    exact hfirst.trans hfiltered.symm
  have C := sum_square_certificate padded hpad
  rw [hlen] at C
  exact Certificate.ofCoeff
    (((hsq.symm).smul (Q'.ofNat D)).add
      (RatPolyCoeffEqv.neg ((hsum.symm).mul hsum.symm))) C

private theorem derivative_sum {I : Type} (b u v : Nat)
    (xs : List I) (f : I → RatPoly) :
    RatPolyCoeffEqv
      (blockAngularDerivative b u v (polySum (xs.map f)))
      (polySum (xs.map fun i => blockAngularDerivative b u v (f i))) := by
  induction xs with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons i rest ih =>
      change RatPolyCoeffEqv
        (angularDerivative (4*b+u) (4*b+v)
          (polyAdd (f i) (polySum (rest.map f))))
        (polyAdd (blockAngularDerivative b u v (f i))
          (polySum (rest.map fun j => blockAngularDerivative b u v (f j))))
      exact (angularDerivative_add _ _ _ _).trans
        ((RatPolyCoeffEqv.refl _).add ih)

/-- A single local angular plane has the exact incidence-count square
certificate.  This is a polynomial SOS, before any source is chosen. -/
def local_plane_certificate {I : Type} (n D b u v : Nat)
    (xs : List I) (term : I → RatPoly) (row : Nat → I → Bool)
    (hterm : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (term i))
    (hrow : (xs.filter (row b)).length ≤ D)
    (hzero : ∀ i, i ∈ xs → row b i = false →
      RatPolyCoeffEqv (blockAngularDerivative b u v (term i)) polyZero)
    (hb : b < n) (hu : u < 4) (hv : v < 4) :
    Certificate n
      (polyAdd
        (polySmul (Q'.ofNat D)
          (polySum (xs.map fun i =>
            polyMul (blockAngularDerivative b u v (term i))
              (blockAngularDerivative b u v (term i)))))
        (polyNeg
          (polyMul
            (blockAngularDerivative b u v (polySum (xs.map term)))
            (blockAngularDerivative b u v (polySum (xs.map term)))))) := by
  have hf : ∀ i, i ∈ xs → SupportedQuaternionBlocks n
      (blockAngularDerivative b u v (term i)) := by
    intro i hi
    exact angularDerivative_supported_at (by omega) (by omega) (hterm i hi)
  have C := masked_square_certificate n D xs (row b)
    (fun i => blockAngularDerivative b u v (term i)) hf hzero hrow
  exact Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.neg
        ((derivative_sum b u v xs term).mul
          (derivative_sum b u v xs term)))) C

private theorem sixValue_add_local (a b : Nat → Nat → Q') :
    sixValue (fun u v => a u v + b u v) ≈
      sixValue a + sixValue b := by
  unfold sixValue
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

private theorem sixValue_sum {I : Type} (xs : List I) (f : I → Nat → Nat → Q') :
    sixValue (fun u v => qListSum (xs.map fun i => f i u v)) ≈
      qListSum (xs.map fun i => sixValue (f i)) := by
  induction xs with
  | nil =>
      change (0 : Q') ≈ 0
      exact Q'.eqv_refl _
  | cons i rest ih =>
      change sixValue (fun u v => f i u v +
        qListSum (rest.map fun j => f j u v)) ≈
        sixValue (f i) + qListSum (rest.map fun j => sixValue (f j))
      exact Q'.eqv_trans _ _ _
        (sixValue_add_local (f i)
          (fun u v => qListSum (rest.map fun j => f j u v)))
        (Q'.add_eqv_congr_left _ _ _ ih)

private theorem qListSum_mono {I : Type} (xs : List I) (f g : I → Q')
    (h : ∀ i, i ∈ xs → f i ≤ g i) :
    qListSum (xs.map f) ≤ qListSum (xs.map g) := by
  revert h
  induction xs with
  | nil => intro _; exact Q'.le_of_eqv (Q'.eqv_refl _)
  | cons i rest ih =>
      intro h
      exact Q'.add_le_add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem qListSum_swap {I J : Type} (xs : List I) (ys : List J)
    (f : I → J → Q') :
    qListSum (xs.map fun i => qListSum (ys.map fun j => f i j)) ≈
      qListSum (ys.map fun j => qListSum (xs.map fun i => f i j)) := by
  induction xs with
  | nil =>
      induction ys with
      | nil => exact Q'.eqv_refl _
      | cons j rest ih =>
          change (0 : Q') ≈ 0 + qListSum (rest.map fun _ => (0 : Q'))
          exact Q'.eqv_trans _ _ _ ih
            (Q'.eqv_symm (QPoly.q_zero_add_eqv _))
  | cons i rest ih =>
      change
        qListSum (ys.map fun j => f i j) +
          qListSum (rest.map fun k => qListSum (ys.map fun j => f k j)) ≈
        qListSum (ys.map fun j =>
          f i j + qListSum (rest.map fun k => f k j))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
        (Q'.eqv_symm (qListSum_add ys (fun j => f i j)
          (fun j => qListSum (rest.map fun k => f k j))))

private theorem weighted_plane_bound {I : Type} (n D b u v : Nat)
    (W : RatPoly) (R : Certificate n W) (xs : List I)
    (term : I → RatPoly) (row : Nat → I → Bool)
    (hterm : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (term i))
    (hrow : (xs.filter (row b)).length ≤ D)
    (hzero : ∀ i, i ∈ xs → row b i = false →
      RatPolyCoeffEqv (blockAngularDerivative b u v (term i)) polyZero)
    (hb : b < n) (hu : u < 4) (hv : v < 4) :
    quaternionHaar n (polyMul W
      (polyMul (blockAngularDerivative b u v (polySum (xs.map term)))
        (blockAngularDerivative b u v (polySum (xs.map term))))) ≤
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W
          (polyMul (blockAngularDerivative b u v (term i))
            (blockAngularDerivative b u v (term i))))) := by
  have horder := weighted_order R
    (local_plane_certificate n D b u v xs term row hterm hrow hzero hb hu hv)
  have hpin := Q'.eqv_trans _ _ _
    (weighted_scale n W
      (polySum (xs.map fun i =>
        polyMul (blockAngularDerivative b u v (term i))
          (blockAngularDerivative b u v (term i)))) (Q'.ofNat D))
    (Q'.mul_eqv_congr_left _ _ _
      (haar_weighted_sum_indexed n W
        (fun i => polyMul (blockAngularDerivative b u v (term i))
          (blockAngularDerivative b u v (term i))) xs))
  exact Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hpin)

/-- The full original block carré du champ satisfies a local incidence
estimate under one common, possibly highly nonconstant positive source. -/
theorem weighted_blockGamma_local_family {I : Type} (n D b : Nat)
    (W : RatPoly) (R : Certificate n W) (xs : List I)
    (term : I → RatPoly) (row : Nat → I → Bool)
    (hterm : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (term i))
    (hrow : (xs.filter (row b)).length ≤ D)
    (hzero : ∀ i, i ∈ xs → row b i = false →
      ∀ u v, u < 4 → v < 4 →
        RatPolyCoeffEqv (blockAngularDerivative b u v (term i)) polyZero)
    (hb : b < n) :
    quaternionHaar n (polyMul W
      (blockGamma b (polySum (xs.map term)) (polySum (xs.map term)))) ≤
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W (blockGamma b (term i) (term i)))) := by
  let p := polySum (xs.map term)
  let moment := fun (r : RatPoly) (u v : Nat) =>
    quaternionHaar n (polyMul W
      (polyMul (blockAngularDerivative b u v r)
        (blockAngularDerivative b u v r)))
  have hplane (u v : Nat) (hu : u < 4) (hv : v < 4) :
      moment p u v ≤ Q'.ofNat D *
        qListSum (xs.map fun i => moment (term i) u v) :=
    weighted_plane_bound n D b u v W R xs term row hterm hrow
      (fun i hi hz => hzero i hi hz u v hu hv) hb hu hv
  have hleft : quaternionHaar n (polyMul W (blockGamma b p p)) ≈
      sixValue (moment p) := by
    exact haar_six n W (fun u v =>
      polyMul (blockAngularDerivative b u v p)
        (blockAngularDerivative b u v p))
  have hright :
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W (blockGamma b (term i) (term i)))) ≈
      sixValue (fun u v => Q'.ofNat D *
        qListSum (xs.map fun i => moment (term i) u v)) := by
    have hsum := qListSum_congr xs
      (fun i => quaternionHaar n (polyMul W (blockGamma b (term i) (term i))))
      (fun i => sixValue (moment (term i)))
      (fun i _ => haar_six n W (fun u v =>
        polyMul (blockAngularDerivative b u v (term i))
          (blockAngularDerivative b u v (term i))))
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hsum)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (sixValue_sum xs
          (fun i => moment (term i)))))
        (sixValue_mul_left (Q'.ofNat D)
          (fun u v => qListSum (xs.map fun i => moment (term i) u v))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (sixValue_mono (moment p)
        (fun u v => Q'.ofNat D *
          qListSum (xs.map fun i => moment (term i) u v)) hplane)
      (Q'.ge_of_eqv hright))

/-- Incidence bounded by `D` on each listed original quaternion block
controls the entire signed family under the *same* positive Haar weight.
There is no orthogonality or independence premise.  Repeated labels count as
separate list occurrences in every row bound. -/
theorem weighted_activeGamma_local_family {I : Type} (n D : Nat)
    (W : RatPoly) (R : Certificate n W) (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n)
    (xs : List I) (term : I → RatPoly) (row : Nat → I → Bool)
    (hterm : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (term i))
    (hrow : ∀ b, b ∈ active → (xs.filter (row b)).length ≤ D)
    (hzero : ∀ b, b ∈ active → ∀ i, i ∈ xs → row b i = false →
      ∀ u v, u < 4 → v < 4 →
        RatPolyCoeffEqv (blockAngularDerivative b u v (term i)) polyZero) :
    quaternionHaar n (polyMul W
      (activeGamma active (polySum (xs.map term)) (polySum (xs.map term)))) ≤
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W (activeGamma active (term i) (term i)))) := by
  let p := polySum (xs.map term)
  let F := fun (b : Nat) (r : RatPoly) =>
    quaternionHaar n (polyMul W (blockGamma b r r))
  have hleft : quaternionHaar n (polyMul W (activeGamma active p p)) ≈
      qListSum (active.map fun b => F b p) := by
    exact haar_weighted_sum_indexed n W (fun b => blockGamma b p p) active
  have hrows :
      qListSum (active.map fun b => F b p) ≤
      qListSum (active.map fun b =>
        Q'.ofNat D * qListSum (xs.map fun i => F b (term i))) := by
    apply qListSum_mono
    intro b hb
    exact weighted_blockGamma_local_family n D b W R xs term row hterm
      (hrow b hb) (hzero b hb) (hactive b hb)
  have hright :
      qListSum (xs.map fun i =>
        qListSum (active.map fun b => F b (term i))) ≈
      qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W (activeGamma active (term i) (term i)))) := by
    exact qListSum_congr xs
      (fun i => qListSum (active.map fun b => F b (term i)))
      (fun i => quaternionHaar n
        (polyMul W (activeGamma active (term i) (term i))))
      (fun i _ => (haar_weighted_sum_indexed n W
        (fun b => blockGamma b (term i) (term i)) active).symm)
  have hsum :
      qListSum (active.map fun b =>
        Q'.ofNat D * qListSum (xs.map fun i => F b (term i))) ≈
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W
          (activeGamma active (term i) (term i)))) := by
    exact Q'.eqv_trans _ _ _
      (qListSum_scale active
        (fun b => qListSum (xs.map fun i => F b (term i))) (Q'.ofNat D))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (qListSum_swap active xs (fun b i => F b (term i))))
        (Q'.mul_eqv_congr_left _ _ _ hright))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hrows (Q'.le_of_eqv hsum))

private theorem finite_sum_map {I : Type} (term : I → RatPoly) :
    ∀ xs : List I, finitePolySum term xs = polySum (xs.map term)
  | [] => rfl
  | _ :: xs => congrArg (polyAdd _) (finite_sum_map term xs)

/-- The public finite-family API, matching the physical signed
`finitePolySum` expression exactly. -/
theorem weighted_finitePolySum_activeGamma_local_family {I : Type} (n D : Nat)
    (W : RatPoly) (R : Certificate n W) (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n)
    (xs : List I) (term : I → RatPoly) (row : Nat → I → Bool)
    (hterm : ∀ i, i ∈ xs → SupportedQuaternionBlocks n (term i))
    (hrow : ∀ b, b ∈ active → (xs.filter (row b)).length ≤ D)
    (hzero : ∀ b, b ∈ active → ∀ i, i ∈ xs → row b i = false →
      ∀ u v, u < 4 → v < 4 →
        RatPolyCoeffEqv (blockAngularDerivative b u v (term i)) polyZero) :
    quaternionHaar n (polyMul W
      (activeGamma active (finitePolySum term xs) (finitePolySum term xs))) ≤
      Q'.ofNat D * qListSum (xs.map fun i =>
        quaternionHaar n (polyMul W (activeGamma active (term i) (term i)))) := by
  rw [finite_sum_map term xs]
  exact weighted_activeGamma_local_family n D W R active hactive xs term row
    hterm hrow hzero

#print axioms YMGap.Continuum.QuaternionHaarLocalAngularFamily.masked_square_certificate
#print axioms YMGap.Continuum.QuaternionHaarLocalAngularFamily.local_plane_certificate
#print axioms YMGap.Continuum.QuaternionHaarLocalAngularFamily.weighted_blockGamma_local_family
#print axioms YMGap.Continuum.QuaternionHaarLocalAngularFamily.weighted_activeGamma_local_family
#print axioms YMGap.Continuum.QuaternionHaarLocalAngularFamily.weighted_finitePolySum_activeGamma_local_family

end YMGap.Continuum.QuaternionHaarLocalAngularFamily
