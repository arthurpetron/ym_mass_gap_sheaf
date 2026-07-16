/-
# Quadratic projective reconstruction for tensor Bernstein certificates

The lower-six E8/E9 charts use the projective substitution

  x * n = c,        r * n^2 = D.

After a chart-dependent polynomial change in `r`, their exact coefficient
tables therefore clear against monomials `D^i * n^(M-u-2*i)`.  This module
derives that clearing from the separable tensor-Bernstein reconstruction;
concrete E8/E9 data remain outside this generic kernel.
-/

import YMGap.Continuum.TensorBernsteinSeparableReconstruction

namespace YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

/-! ## Integer upper-binomial bookkeeping -/

theorem upperBinomialTransform_congr
    (degree : Nat) (a b : Nat → Int) (index : Nat)
    (h : ∀ exponent, exponent < degree + 1 → a exponent = b exponent) :
    upperBinomialTransform degree a index =
      upperBinomialTransform degree b index := by
  unfold upperBinomialTransform
  have hprefix : ∀ count, count ≤ degree + 1 →
      upperBinomialPrefix a count index =
        upperBinomialPrefix b count index := by
    intro count hcount
    induction count with
    | zero => rfl
    | succ count ih =>
        unfold upperBinomialPrefix rowAdd rowScale
        rw [ih (by omega), h count (by omega)]
  exact hprefix (degree + 1) (Nat.le_refl _)

theorem upperBinomialTransform_mul_right
    (degree : Nat) (coefficients : Nat → Int) (z : Int) (index : Nat) :
    upperBinomialTransform degree coefficients index * z =
      upperBinomialTransform degree (fun exponent =>
        coefficients exponent * z) index := by
  unfold upperBinomialTransform
  have hprefix : ∀ count,
      upperBinomialPrefix coefficients count index * z =
        upperBinomialPrefix (fun exponent => coefficients exponent * z)
          count index := by
    intro count
    induction count with
    | zero => simp [upperBinomialPrefix]
    | succ count ih =>
        unfold upperBinomialPrefix rowAdd rowScale
        rw [Int.add_mul, ih]
        simp only [Int.mul_assoc, Int.mul_comm]
  exact hprefix (degree + 1)

/-! ## Quadratically homogeneous raw evaluator -/

/-- Pull a raw `(D,n)` coefficient back to the unique residual exponent
`u = M - 2*i - j`.  Invalid exponent pairs contribute zero. -/
def quadraticRawLift (totalDegree : Nat) (raw : Nat → Nat → Int)
    (u i : Nat) : Int :=
  if u + 2 * i ≤ totalDegree then
    raw i (totalDegree - u - 2 * i)
  else
    0

/-- Dense evaluation organized by the residual inverse-mode exponent `u`.
For supported raw tables this is their ordinary bivariate power evaluation,
with each monomial occurring at its unique residual exponent. -/
def quadraticPowerEval (degreeU degreeR totalDegree : Nat)
    (raw : Nat → Nat → Int) (D n : Q') : Q' :=
  finSum (fun u =>
    finSum (fun i =>
      Q'.ofInt (quadraticRawLift totalDegree raw u i) *
        (D ^ i * n ^ (totalDegree - u - 2 * i))) (degreeR + 1))
    (degreeU + 1)

private theorem pow_add_eqv (value : Q') (a : Nat) : ∀ b,
    value ^ (a + b) ≈ value ^ a * value ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (value ^ a))
  | b + 1 => by
      have ih := pow_add_eqv value a b
      show value * value ^ (a + b) ≈ value ^ a * (value * value ^ b)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left value _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv value (value ^ a) (value ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (value ^ b)
          (Q'.mul_comm_eqv value (value ^ a))) ?_
      exact Q'.mul_assoc_eqv (value ^ a) value (value ^ b)

private theorem pow_eqv_congr {a b : Q'} (h : a ≈ b) : ∀ exponent : Nat,
    a ^ exponent ≈ b ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := pow_eqv_congr h exponent
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a ^ exponent) h)
        (Q'.mul_eqv_congr_left b _ _ ih)

private theorem rearrange4 (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (a * b) c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b))) ?_
  exact Q'.mul_assoc_eqv (a * c) b d

private theorem mul_pow_eqv (a b : Q') : ∀ exponent : Nat,
    (a * b) ^ exponent ≈ a ^ exponent * b ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have ih := mul_pow_eqv a b exponent
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      exact rearrange4 a b (a ^ exponent) (b ^ exponent)

/-! ## Direct quadratic chart -/

private theorem tensor_reorder (a b c : Q') :
    a * (b * c) ≈ (b * a) * c := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  exact Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)

/-- Reorder the tensor power evaluator so that the first coordinate is the
outer sum.  This public form is useful for nonlinear changes in the second
coordinate before projective clearing. -/
theorem tensorPowerEval_by_first
    (degreeX degreeY : Nat) (power : Nat → Nat → Int) (x y : Q') :
    tensorPowerEval degreeX degreeY power x y ≈
      finSum (fun a => x ^ a * signedPowerEval degreeY (power a) y)
        (degreeX + 1) := by
  unfold tensorPowerEval signedPowerEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeY + 1) (fun b _ =>
      finSum_mul_const
        (fun a => Q'.ofInt (power a b) * x ^ a)
        (y ^ b) (degreeX + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_swap
      (fun b a => (Q'.ofInt (power a b) * x ^ a) * y ^ b)
      (degreeY + 1) (degreeX + 1)) ?_
  refine finSum_eqv_congr_lt _ _ (degreeX + 1) ?_
  intro a ha
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt
      (fun b => (Q'.ofInt (power a b) * x ^ a) * y ^ b)
      (fun b => x ^ a * (Q'.ofInt (power a b) * y ^ b))
      (degreeY + 1) (fun b _ => ?_)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofInt (power a b)) (x ^ a) (y ^ b)) ?_
    refine Q'.eqv_trans _ _ _
      (tensor_reorder (Q'.ofInt (power a b)) (x ^ a) (y ^ b)) ?_
    exact Q'.mul_assoc_eqv (x ^ a) (Q'.ofInt (power a b)) (y ^ b)
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun b => Q'.ofInt (power a b) * y ^ b)
        (x ^ a) (degreeY + 1))

/-- Pointwise equality on the finite coefficient rectangle gives equivalent
tensor power evaluations. -/
theorem tensorPowerEval_congr
    (degreeX degreeY : Nat) (power other : Nat → Nat → Int)
    (x y : Q')
    (h : ∀ i, i < degreeX + 1 → ∀ j, j < degreeY + 1 →
      power i j = other i j) :
    tensorPowerEval degreeX degreeY power x y ≈
      tensorPowerEval degreeX degreeY other x y := by
  unfold tensorPowerEval signedPowerEval
  refine finSum_eqv_congr_lt _ _ (degreeY + 1) ?_
  intro j hj
  refine Q'.mul_eqv_congr_right _ _ (y ^ j) ?_
  refine finSum_eqv_congr_lt _ _ (degreeX + 1) ?_
  intro i hi
  change Q'.ofInt (power i j) * x ^ i ≈
    Q'.ofInt (other i j) * x ^ i
  rw [h i hi j hj]
  exact Q'.eqv_refl _

/-- Applying the upper-binomial transform in the second coordinate evaluates
the original power table at `y+1`. -/
theorem tensorPowerEval_upperBinomial_second
    (degreeX degreeY : Nat) (power : Nat → Nat → Int) (x y : Q') :
    tensorPowerEval degreeX degreeY
        (fun a b => upperBinomialTransform degreeY (power a) b) x y ≈
      tensorPowerEval degreeX degreeY power x (y + 1) := by
  refine Q'.eqv_trans _ _ _
    (tensorPowerEval_by_first degreeX degreeY
      (fun a b => upperBinomialTransform degreeY (power a) b) x y) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun a _ =>
      Q'.mul_eqv_congr_left (x ^ a) _ _
        (signedPowerEval_upperBinomialTransform degreeY (power a) y))) ?_
  exact Q'.eqv_symm
    (tensorPowerEval_by_first degreeX degreeY power x (y + 1))

/-- Scaling every coefficient of a signed power row on the right scales its
evaluation by the same exact integer. -/
theorem signedPowerEval_scale_right
    (degree : Nat) (coefficients : Nat → Int) (scale : Int) (y : Q') :
    signedPowerEval degree (fun i => coefficients i * scale) y ≈
      signedPowerEval degree coefficients y * Q'.ofInt scale := by
  unfold signedPowerEval
  refine Q'.eqv_trans _
    (finSum (fun i =>
      (Q'.ofInt (coefficients i) * y ^ i) * Q'.ofInt scale)
      (degree + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (degree + 1) ?_
    intro i hi
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (y ^ i)
        (YMGap.Continuum.RingNormaliser.ofInt_mul (coefficients i) scale)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofInt (coefficients i))
        (Q'.ofInt scale) (y ^ i)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofInt (coefficients i)) _ _
        (Q'.mul_comm_eqv (Q'.ofInt scale) (y ^ i))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofInt (coefficients i))
        (y ^ i) (Q'.ofInt scale))
  · exact Q'.eqv_symm
      (finSum_mul_const
        (fun i => Q'.ofInt (coefficients i) * y ^ i)
        (Q'.ofInt scale) (degree + 1))

/-- Scaling a complete tensor power grid on the right scales its evaluation
by the same exact integer. -/
theorem tensorPowerEval_scale_right
    (degreeX degreeY : Nat) (power : Nat → Nat → Int)
    (scale : Int) (x y : Q') :
    tensorPowerEval degreeX degreeY
        (fun i j => power i j * scale) x y ≈
      tensorPowerEval degreeX degreeY power x y * Q'.ofInt scale := by
  refine Q'.eqv_trans _ _ _
    (tensorPowerEval_by_first degreeX degreeY
      (fun i j => power i j * scale) x y) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun i _ =>
      Q'.mul_eqv_congr_left (x ^ i) _ _
        (signedPowerEval_scale_right degreeY (power i) scale y))) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr_lt _ _ (degreeX + 1) (fun i _ =>
      Q'.eqv_symm
        (Q'.mul_assoc_eqv (x ^ i)
          (signedPowerEval degreeY (power i) y) (Q'.ofInt scale)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finSum_mul_const
        (fun i => x ^ i * signedPowerEval degreeY (power i) y)
        (Q'.ofInt scale) (degreeX + 1))) ?_
  exact Q'.mul_eqv_congr_right _ _ (Q'.ofInt scale)
    (Q'.eqv_symm (tensorPowerEval_by_first degreeX degreeY power x y))

/-- Scaling every raw coefficient on the left scales the quadratically
homogeneous evaluator by the same exact integer.  Keeping this statement at
the evaluator level avoids expanding the dense E8/E9 coefficient grids. -/
theorem quadraticPowerEval_scale_left
    (degreeU degreeR totalDegree : Nat) (raw : Nat → Nat → Int)
    (scale : Int) (D n : Q') :
    quadraticPowerEval degreeU degreeR totalDegree
        (fun i j => scale * raw i j) D n ≈
      quadraticPowerEval degreeU degreeR totalDegree raw D n *
        Q'.ofInt scale := by
  unfold quadraticPowerEval
  refine Q'.eqv_trans _
    (finSum (fun u =>
      finSum (fun i =>
        (Q'.ofInt (quadraticRawLift totalDegree raw u i) *
          (D ^ i * n ^ (totalDegree - u - 2 * i))) *
          Q'.ofInt scale) (degreeR + 1)) (degreeU + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (degreeU + 1) ?_
    intro u hu
    refine finSum_eqv_congr_lt _ _ (degreeR + 1) ?_
    intro i hi
    have hlift :
        quadraticRawLift totalDegree (fun i j => scale * raw i j) u i =
          scale * quadraticRawLift totalDegree raw u i := by
      by_cases hvalid : u + 2 * i ≤ totalDegree
      · simp only [quadraticRawLift, hvalid, ↓reduceIte]
      · simp only [quadraticRawLift, hvalid, ↓reduceIte, Int.mul_zero]
    rw [hlift]
    let coefficient := Q'.ofInt (quadraticRawLift totalDegree raw u i)
    let monomial := D ^ i * n ^ (totalDegree - u - 2 * i)
    let factor := Q'.ofInt scale
    refine Q'.eqv_trans _ ((factor * coefficient) * monomial) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ monomial
        (YMGap.Continuum.RingNormaliser.ofInt_mul scale
          (quadraticRawLift totalDegree raw u i))
    · refine Q'.eqv_trans _ (factor * (coefficient * monomial)) _
        (Q'.mul_assoc_eqv factor coefficient monomial) ?_
      exact Q'.mul_comm_eqv factor (coefficient * monomial)
  · refine Q'.eqv_trans _
      (finSum (fun u =>
        (finSum (fun i =>
          Q'.ofInt (quadraticRawLift totalDegree raw u i) *
            (D ^ i * n ^ (totalDegree - u - 2 * i)))
          (degreeR + 1)) * Q'.ofInt scale) (degreeU + 1)) _ ?_ ?_
    · exact finSum_eqv_congr_lt _ _ (degreeU + 1) (fun u _ =>
        Q'.eqv_symm
          (finSum_mul_const
            (fun i =>
              Q'.ofInt (quadraticRawLift totalDegree raw u i) *
                (D ^ i * n ^ (totalDegree - u - 2 * i)))
            (Q'.ofInt scale) (degreeR + 1)))
    · exact Q'.eqv_symm
        (finSum_mul_const
          (fun u =>
            finSum (fun i =>
              Q'.ofInt (quadraticRawLift totalDegree raw u i) *
                (D ^ i * n ^ (totalDegree - u - 2 * i)))
              (degreeR + 1))
          (Q'.ofInt scale) (degreeU + 1))

/-- The linear projective diagonal returned by the separable kernel becomes
the quadratic raw evaluator when `target * den = D`. -/
theorem diagonalPowerEval_quadraticRawLift
    (degreeU degreeR totalDegree : Nat) (raw : Nat → Nat → Int)
    (den target D : Q') (hD : target * den ≈ D) :
    diagonalPowerEval degreeU degreeR totalDegree
        (quadraticRawLift totalDegree raw) den target ≈
      quadraticPowerEval degreeU degreeR totalDegree raw D den := by
  unfold diagonalPowerEval quadraticPowerEval
  refine finSum_eqv_congr_lt _ _ (degreeU + 1) ?_
  intro u hu
  refine finSum_eqv_congr_lt _ _ (degreeR + 1) ?_
  intro i hi
  by_cases hvalid : u + 2 * i ≤ totalDegree
  · have hshape : totalDegree - u - i =
        i + (totalDegree - u - 2 * i) := by
      omega
    have hsplit : den ^ (totalDegree - u - i) ≈
        den ^ i * den ^ (totalDegree - u - 2 * i) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (congrArg (fun exponent => den ^ exponent) hshape)) ?_
      exact pow_add_eqv den i (totalDegree - u - 2 * i)
    have htarget : target ^ i * den ^ i ≈ D ^ i :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_pow_eqv target den i))
        (pow_eqv_congr hD i)
    unfold quadraticRawLift
    simp only [hvalid, ↓reduceIte]
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (target ^ i) _ _ hsplit) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (target ^ i) (den ^ i)
          (den ^ (totalDegree - u - 2 * i)))) ?_
    exact Q'.mul_eqv_congr_right _ _
      (den ^ (totalDegree - u - 2 * i)) htarget
  · unfold quadraticRawLift
    simp only [hvalid, ↓reduceIte]
    refine Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _) ?_
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

/-! ## Combined consumer -/

/-- Reconstruct a nonlinearly projective tensor power table.  The two
supplied coefficient relations are pointwise exact integer equalities; all
rational clearing is proved here. -/
theorem tensorPowerEval_mul_den_pow_eqv_quadratic
    (degreeU degreeR totalDegree constant : Nat)
    (power preChart raw : Nat → Nat → Int)
    (x y den D : Q')
    (hdegree : degreeU ≤ totalDegree)
    (hxden : x * den ≈ Q'.ofNat constant)
    (hrden : ((y + 1) * den) * den ≈ D)
    (hshift : ∀ u, u < degreeU + 1 → ∀ b, b < degreeR + 1 →
      power u b = upperBinomialTransform degreeR (preChart u) b)
    (hraw : ∀ u, u < degreeU + 1 → ∀ i, i < degreeR + 1 →
      preChart u i * Int.ofNat (constant ^ u) =
        quadraticRawLift totalDegree raw u i) :
    tensorPowerEval degreeU degreeR power x y * den ^ totalDegree ≈
      quadraticPowerEval degreeU degreeR totalDegree raw D den := by
  let target := (y + 1) * den
  have hprojective :
      tensorPowerEval degreeU degreeR power x y * den ^ totalDegree ≈
        diagonalPowerEval degreeU degreeR totalDegree
          (quadraticRawLift totalDegree raw) den target := by
    apply tensorPowerEval_mul_den_pow_eqv_diagonal
      degreeU degreeR totalDegree constant power
      (quadraticRawLift totalDegree raw) x y den target
    · exact hdegree
    · exact hxden
    · exact Q'.eqv_refl target
    · intro u hu b hb
      have hscaled := congrArg
        (fun coefficient : Int =>
          coefficient * Int.ofNat (constant ^ u))
        (hshift u hu b hb)
      refine Eq.trans hscaled ?_
      refine Eq.trans
        (upperBinomialTransform_mul_right degreeR (preChart u)
          (Int.ofNat (constant ^ u)) b) ?_
      exact upperBinomialTransform_congr degreeR
        (fun i => preChart u i * Int.ofNat (constant ^ u))
        (quadraticRawLift totalDegree raw u) b
        (fun i hi => hraw u hu i hi)
    · intro u hu i hi hnonzero
      unfold quadraticRawLift at hnonzero
      split at hnonzero
      · omega
      · simp at hnonzero
  exact Q'.eqv_trans _ _ _ hprojective
    (diagonalPowerEval_quadraticRawLift
      degreeU degreeR totalDegree raw den target D hrden)

/-- Direct form of the quadratic projective consumer.  Here the second power
coordinate is already `r` with `r*den² = D`; the proof inserts the exact
upper-binomial shift internally and then reuses the checked shifted kernel. -/
theorem tensorPowerEval_mul_den_pow_eqv_quadratic_direct
    (degreeU degreeR totalDegree constant : Nat)
    (power raw : Nat → Nat → Int)
    (x r den D : Q')
    (hdegree : degreeU ≤ totalDegree)
    (hxden : x * den ≈ Q'.ofNat constant)
    (hrden : (r * den) * den ≈ D)
    (hraw : ∀ u, u < degreeU + 1 → ∀ i, i < degreeR + 1 →
      power u i * Int.ofNat (constant ^ u) =
        quadraticRawLift totalDegree raw u i) :
    tensorPowerEval degreeU degreeR power x r * den ^ totalDegree ≈
      quadraticPowerEval degreeU degreeR totalDegree raw D den := by
  let y := r + (-1)
  let shifted : Nat → Nat → Int := fun u i =>
    upperBinomialTransform degreeR (power u) i
  have hy : y + 1 ≈ r := by
    dsimp only [y]
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv r (-1) 1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left r _ _ (Q'.neg_add_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' r)
  have hshifted :
      tensorPowerEval degreeU degreeR shifted x y ≈
        tensorPowerEval degreeU degreeR power x r := by
    refine Q'.eqv_trans _ _ _
      (tensorPowerEval_upperBinomial_second degreeU degreeR power x y) ?_
    unfold tensorPowerEval
    refine finSum_eqv_congr_lt _ _ (degreeR + 1) ?_
    intro i hi
    exact Q'.mul_eqv_congr_left _ _ _ (pow_eqv_congr hy i)
  have hshiftedProjective :
      tensorPowerEval degreeU degreeR shifted x y * den ^ totalDegree ≈
        quadraticPowerEval degreeU degreeR totalDegree raw D den := by
    apply tensorPowerEval_mul_den_pow_eqv_quadratic
      degreeU degreeR totalDegree constant shifted power raw x y den D
    · exact hdegree
    · exact hxden
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ den
          (Q'.mul_eqv_congr_right _ _ den hy)) ?_
      exact hrden
    · intro u hu i hi
      rfl
    · exact hraw
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (den ^ totalDegree)
      (Q'.eqv_symm hshifted))
    hshiftedProjective

/-! ## Dependency gates -/

#print axioms upperBinomialTransform_congr
#print axioms upperBinomialTransform_mul_right
#print axioms quadraticRawLift
#print axioms quadraticPowerEval
#print axioms diagonalPowerEval_quadraticRawLift
#print axioms tensorPowerEval_mul_den_pow_eqv_quadratic
#print axioms tensorPowerEval_by_first
#print axioms tensorPowerEval_congr
#print axioms tensorPowerEval_upperBinomial_second
#print axioms signedPowerEval_scale_right
#print axioms tensorPowerEval_scale_right
#print axioms quadraticPowerEval_scale_left
#print axioms tensorPowerEval_mul_den_pow_eqv_quadratic_direct

end YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
