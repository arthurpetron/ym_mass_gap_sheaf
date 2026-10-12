/-
# Computed rational-row second Stein identity

For the EXISTING finiteProductGaussian N and its literal rational linear row,
this file derives E[L_d^2*p] = (sum_{i<N} d_i^2)*E[p] + E[D_d(D_d p)].
The polynomial p is arbitrary, and N=0 and zero rows are included. No moment,
product-rule or Gram law is a hypothesis. Variables outside N still evaluate
at ONE; this scalar evaluator does not preserve tail coefficients.

The row product rule is coefficientwise. The derivative of a variable retains
a padded zero exponent vector, so its constant contraction is proved under
the SAME Gaussian evaluation, not falsely identified with polyConst under
arbitrary coefficient probes. Local recursive helpers only expose the existing
row definitions; the main statements use those original definitions.

Consumer: the degree-four/six correlated rational-row contraction in the
adaptive-score audit, section Rational-row covariance (line 25079). Computing
the radial quartic's second derivative and its Gram contraction, actual
transverse mode rows/moduli, and the ORIGINAL compact-Haar/section/source/
OLD-center comparison remain separate obligations. No covariance bundle,
original-law identification, uniform interacting estimate or physical gap is
claimed. Compilation and axiom verification are serialized by the root agent.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP

local infix:50 " ≈ " => Q'.eqv

-- Structural presentations of the existing private row recursions.
private def linearOn (d : Nat → Q') : List Nat → RatPoly
  | [] => polyZero
  | i :: ids => polyAdd (polySmul (d i) (polyVar i)) (linearOn d ids)

private def derivativeOn (d : Nat → Q') (p : RatPoly) : List Nat → RatPoly
  | [] => polyZero
  | i :: ids => polyAdd (polySmul (d i) (ratDerivative i p)) (derivativeOn d p ids)

private theorem linearOn_pin (N : Nat) (d : Nat → Q') :
    finiteLinearRow N d = linearOn d (List.range N) := by
  unfold finiteLinearRow
  generalize List.range N = ids
  induction ids with
  | nil => rfl
  | cons i ids ih =>
      exact congrArg (fun q => polyAdd (polySmul (d i) (polyVar i)) q) ih

private theorem derivativeOn_pin (N : Nat) (d : Nat → Q') (p : RatPoly) :
    finiteRowDerivative N d p = derivativeOn d p (List.range N) := by
  unfold finiteRowDerivative
  generalize List.range N = ids
  induction ids with
  | nil => rfl
  | cons i ids ih =>
      exact congrArg (fun q => polyAdd (polySmul (d i) (ratDerivative i p)) q) ih

/-- Literal computed rational squared row norm, with no positivity premise. -/
def finiteRowNorm2 (N : Nat) (d : Nat → Q') : Q' :=
  qListSum ((List.range N).map fun i => d i * d i)

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (a : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul a p) ≈ a * finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) a p

private theorem gaussian_smul_mul (N : Nat) (a : Q') (q p : RatPoly) :
    finiteProductGaussian N (polyMul (polySmul a q) p) ≈
      a * finiteProductGaussian N (polyMul q p) :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N (RatPolyCoeffEqv.polyMul_smul_left a q p))
    (gaussian_smul N a (polyMul q p))

private theorem derivativeOn_mul (d : Nat → Q') (p q : RatPoly) :
    ∀ ids : List Nat, RatPolyCoeffEqv
      (derivativeOn d (polyMul p q) ids)
      (polyAdd (polyMul (derivativeOn d p ids) q)
        (polyMul p (derivativeOn d q ids)))
  | [] => by
      exact RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.trans
          (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_zero_left q)
            (RatPolyCoeffEqv.mul_zero_right p))
          (RatPolyCoeffEqv.zero_add polyZero))
  | i :: ids => by
      have hfirst : RatPolyCoeffEqv
          (polySmul (d i) (ratDerivative i (polyMul p q)))
          (polyAdd (polyMul (polySmul (d i) (ratDerivative i p)) q)
            (polyMul p (polySmul (d i) (ratDerivative i q)))) :=
        RatPolyCoeffEqv.trans ((ratDerivative_mul i p q).smul (d i))
          (RatPolyCoeffEqv.trans (RatPolyCoeffEqv.smul_add (d i) _ _)
            (RatPolyCoeffEqv.add
              (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.polyMul_smul_left (d i) _ q))
              (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.polyMul_smul_right (d i) p _))))
      have hparts := RatPolyCoeffEqv.add hfirst (derivativeOn_mul d p q ids)
      have hshuffle := RatPolyCoeffEqv.four_add_swap
        (polyMul (polySmul (d i) (ratDerivative i p)) q)
        (polyMul p (polySmul (d i) (ratDerivative i q)))
        (polyMul (derivativeOn d p ids) q)
        (polyMul p (derivativeOn d q ids))
      change RatPolyCoeffEqv
        (polyAdd (polySmul (d i) (ratDerivative i (polyMul p q)))
          (derivativeOn d (polyMul p q) ids))
        (polyAdd
          (polyMul (polyAdd (polySmul (d i) (ratDerivative i p))
            (derivativeOn d p ids)) q)
          (polyMul p (polyAdd (polySmul (d i) (ratDerivative i q))
            (derivativeOn d q ids))))
      rw [polyMul_add_left_exact]
      exact RatPolyCoeffEqv.trans hparts
        (RatPolyCoeffEqv.trans hshuffle
          (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
            (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.mul_add_right p _ _))))

/-- Coefficientwise Leibniz rule for the EXISTING finite rational-row derivative. -/
theorem finiteRowDerivative_mul (N : Nat) (d : Nat → Q') (p q : RatPoly) :
    RatPolyCoeffEqv (finiteRowDerivative N d (polyMul p q))
      (polyAdd (polyMul (finiteRowDerivative N d p) q)
        (polyMul p (finiteRowDerivative N d q))) := by
  rw [derivativeOn_pin, derivativeOn_pin, derivativeOn_pin]
  exact derivativeOn_mul d p q (List.range N)

private theorem gaussianMono_ext (N : Nat) (a b : List Nat)
    (h : ∀ i, i<N → exponentAt a i = exponentAt b i) :
    finiteGaussianMono N a = finiteGaussianMono N b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih =>
      change gaussianMoment1 (exponentAt a N) * finiteGaussianMono N a =
        gaussianMoment1 (exponentAt b N) * finiteGaussianMono N b
      rw [h N (by omega), ih a b (fun i hi => h i (by omega))]

private theorem exponentAt_lower_var_same (i k : Nat) :
    exponentAt (lowerExponentAt i (varMono i)) k = 0 := by
  induction i generalizing k with
  | zero => cases k <;> rfl
  | succ i ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih k

private theorem gaussian_zero_monomial_mul (N : Nat) (z : List Nat)
    (hz : ∀ i, i<N → exponentAt z i = 0) : ∀ p : RatPoly,
    finiteProductGaussian N (polyMul [(z, 1)] p) ≈ finiteProductGaussian N p
  | [] => Q'.eqv_refl _
  | term :: p => by
      rcases term with ⟨m, a⟩
      have hm : finiteGaussianMono N (monoMul z m) = finiteGaussianMono N m :=
        gaussianMono_ext N _ _ (fun i hi => by
          rw [exponentAt_monoMul, hz i hi, Nat.zero_add])
      change (1 * a) * finiteGaussianMono N (monoMul z m) +
          finiteProductGaussian N (polyMul [(z, 1)] p) ≈
        a * finiteGaussianMono N m + finiteProductGaussian N p
      rw [hm]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv a))
        (gaussian_zero_monomial_mul N z hz p)

private theorem gaussian_derivative_var_mul (N i j : Nat) (p : RatPoly) :
    finiteProductGaussian N (polyMul (ratDerivative i (polyVar j)) p) ≈
      (if j=i then (1 : Q') else 0) * finiteProductGaussian N p := by
  change finiteProductGaussian N
      (polyMul (polySmul (Q'.ofNat (exponentAt (varMono j) i))
        [(lowerExponentAt i (varMono j), 1)]) p) ≈ _
  cases Nat.decEq i j with
  | isTrue h =>
      subst i
      rw [exponentAt_varMono, if_pos rfl, if_pos rfl]
      exact Q'.eqv_trans _ _ _ (gaussian_smul_mul N 1 _ p)
        (Q'.mul_eqv_congr_left _ _ _
          (gaussian_zero_monomial_mul N _ (fun k _ => exponentAt_lower_var_same j k) p))
  | isFalse h =>
      rw [exponentAt_varMono, if_neg h, if_neg (Ne.symm h)]
      exact Q'.eqv_trans _ _ _ (gaussian_smul_mul N 0 _ p)
        (Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _)
          (Q'.eqv_symm (Q'.zero_mul_eqv _)))

private theorem sum_pick_absent (i : Nat) (a : Q') : ∀ ids : List Nat, i ∉ ids →
    qListSum (ids.map fun j => if j=i then a else 0) ≈ 0
  | [], _ => Q'.eqv_refl _
  | j :: ids, h => by
      have hji : j≠i := fun heq => h (heq ▸ List.mem_cons_self)
      simp only [List.map_cons, qListSum, if_neg hji]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (sum_pick_absent i a ids (fun hi => h (List.mem_cons_of_mem j hi))))
        (QPoly.q_zero_add_eqv _)

private theorem sum_pick (i : Nat) (a : Q') : ∀ ids : List Nat,
    ids.Nodup → i ∈ ids → qListSum (ids.map fun j => if j=i then a else 0) ≈ a
  | [], _, hi => False.elim (List.not_mem_nil hi)
  | j :: ids, hn, hi => by
      cases Nat.decEq j i with
      | isTrue h =>
          subst j
          simp only [List.map_cons, qListSum]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (sum_pick_absent i a ids (List.nodup_cons.mp hn).1))
            (QPoly.q_add_zero_eqv _)
      | isFalse h =>
          simp only [List.map_cons, qListSum, if_neg h]
          have htail : i ∈ ids := (List.mem_cons.mp hi).resolve_left (Ne.symm h)
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (sum_pick i a ids (List.nodup_cons.mp hn).2 htail))
            (QPoly.q_zero_add_eqv _)

-- Avoid the toolchain's classical simp path in List.nodup_range.
private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = N := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl N)

private theorem gaussian_derivative_linearOn (N i : Nat) (d : Nat → Q') (p : RatPoly) :
    ∀ ids : List Nat,
      finiteProductGaussian N (polyMul (ratDerivative i (linearOn d ids)) p) ≈
        qListSum (ids.map fun j => if j=i then d i else 0) * finiteProductGaussian N p
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | j :: ids => by
      have hfirst : finiteProductGaussian N
          (polyMul (ratDerivative i (polySmul (d j) (polyVar j))) p) ≈
          (if j=i then d i else 0) * finiteProductGaussian N p := by
        have hscaled := Q'.eqv_trans _ _ _
          (finiteProductGaussian_coeffEqv N ((ratDerivative_smul i (d j) (polyVar j)).mul_right p))
          (Q'.eqv_trans _ _ _ (gaussian_smul_mul N (d j) (ratDerivative i (polyVar j)) p)
            (Q'.mul_eqv_congr_left _ _ _ (gaussian_derivative_var_mul N i j p)))
        cases Nat.decEq j i with
        | isTrue h =>
            subst j
            rw [if_pos rfl] at hscaled ⊢
            exact Q'.eqv_trans _ _ _ hscaled
              (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
                (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)))
        | isFalse h =>
            rw [if_neg h] at hscaled ⊢
            exact Q'.eqv_trans _ _ _ hscaled
              (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
                (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _)))
      change finiteProductGaussian N
          (polyMul (ratDerivative i (polyAdd (polySmul (d j) (polyVar j))
            (linearOn d ids))) p) ≈ _
      rw [ratDerivative_add_exact, polyMul_add_left_exact]
      simp only [List.map_cons, qListSum]
      exact Q'.eqv_trans _ _ _ (gaussian_add N _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hfirst (gaussian_derivative_linearOn N i d p ids))
          (Q'.eqv_symm (q_add_mul _ _ _)))

/-- Actual contraction of the literal row's coordinate derivative. The padded
constant monomial is handled by this evaluator, not erased coefficientwise. -/
theorem finiteLinearRow_coordinate_derivative (N i : Nat) (hi : i<N)
    (d : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul (ratDerivative i (finiteLinearRow N d)) p) ≈
      d i * finiteProductGaussian N p := by
  rw [linearOn_pin]
  exact Q'.eqv_trans _ _ _ (gaussian_derivative_linearOn N i d p (List.range N))
    (Q'.mul_eqv_congr_right _ _ _
      (sum_pick i (d i) (List.range N) (range_nodup N) (List.mem_range.mpr hi)))

private theorem gaussian_derivativeOn_linearRow (N : Nat) (d : Nat → Q') (p : RatPoly) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i<N) →
      finiteProductGaussian N (polyMul (derivativeOn d (finiteLinearRow N d) ids) p) ≈
        qListSum (ids.map fun i => d i * d i) * finiteProductGaussian N p
  | [], _ => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | i :: ids, hids => by
      have hfirst := Q'.eqv_trans _ _ _
        (gaussian_smul_mul N (d i) (ratDerivative i (finiteLinearRow N d)) p)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (finiteLinearRow_coordinate_derivative N i (hids i List.mem_cons_self) d p))
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
      change finiteProductGaussian N
        (polyMul (polyAdd (polySmul (d i) (ratDerivative i (finiteLinearRow N d)))
          (derivativeOn d (finiteLinearRow N d) ids)) p) ≈ _
      rw [polyMul_add_left_exact]
      simp only [List.map_cons, qListSum]
      exact Q'.eqv_trans _ _ _ (gaussian_add N _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hfirst
            (gaussian_derivativeOn_linearRow N d p ids
              (fun j hj => hids j (List.mem_cons_of_mem i hj))))
          (Q'.eqv_symm (q_add_mul _ _ _)))

/-- The derivative of the SAME explicit row contracts to its computed Gram
diagonal, for arbitrary p and including the empty dimension. -/
theorem finiteRowDerivative_linearRow_contraction (N : Nat) (d : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N
      (polyMul (finiteRowDerivative N d (finiteLinearRow N d)) p) ≈
      finiteRowNorm2 N d * finiteProductGaussian N p := by
  rw [derivativeOn_pin]
  exact gaussian_derivativeOn_linearRow N d p (List.range N)
    (fun _ hi => List.mem_range.mp hi)

/-- Computed rational-row second Stein identity for EVERY finite polynomial.
The literal Gram sum is produced, not assumed; there is no degree or support
guard and no nondegeneracy requirement. -/
theorem finiteProductGaussian_doubleStein (N : Nat) (d : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N
      (polyMul (polyMul (finiteLinearRow N d) (finiteLinearRow N d)) p) ≈
      finiteRowNorm2 N d * finiteProductGaussian N p +
        finiteProductGaussian N (finiteRowDerivative N d (finiteRowDerivative N d p)) := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.mul_assoc (finiteLinearRow N d) (finiteLinearRow N d) p))
    (Q'.eqv_trans _ _ _
      (finiteProductGaussian_linearRow_stein N d (polyMul (finiteLinearRow N d) p))
      (Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N (finiteRowDerivative_mul N d (finiteLinearRow N d) p))
        (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
          (Q'.add_eqv_congr'
            (finiteRowDerivative_linearRow_contraction N d p)
            (finiteProductGaussian_linearRow_stein N d (finiteRowDerivative N d p))))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein.finiteRowDerivative_mul
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein.finiteLinearRow_coordinate_derivative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein.finiteRowDerivative_linearRow_contraction
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein.finiteProductGaussian_doubleStein
