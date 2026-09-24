/- Exact bare-Haar low moments for one exposed four-quaternion heat. -/

import YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
import YMGap.Continuum.QuaternionHaarHeatCertificate
import YMGap.Continuum.PolynomialWeightedSumBounds

namespace YMGap.Continuum.QuaternionHaarExposedHeatMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization (quaternionHaar_polyMul_comm)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

local infix:50 " ≈ " => Q'.eqv

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _))
    (Q'.eqv_refl _)) (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem first_mul_succ (p : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p (n+1)))
      (polyAdd (characterPolynomial p (n+2)) (characterPolynomial p n)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p (n+1))
  let b := characterPolynomial p n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (.refl b))

private theorem character_mean {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) :
    quaternionHaar blocks
      (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin) ≈
      (if spin = 0 then 1 else 0) := by
  cases spin with
  | zero => exact haar_one blocks
  | succ spin =>
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
        (exposedCharacter_haar_zero hb r0 r1 r2 r3 (spin+1) polyOne (by
          change 0 < spin+1
          omega))

/-- Exact exposed-character pairing with the fundamental mode. -/
theorem fundamental_pair {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) :
    let x := (exposedFourWord r0 r1 r2 r3).scalar
    let f := characterPolynomial x 1
    quaternionHaar blocks (polyMul (characterPolynomial x spin) f) ≈
      (if spin = 1 then 1 else 0) := by
  let x := (exposedFourWord r0 r1 r2 r3).scalar
  let f := characterPolynomial x 1
  cases spin with
  | zero =>
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul f))
        (character_mean hb r0 r1 r2 r3 1)
  | succ n =>
      refine Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (first_mul_succ x n))) ?_
      refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
      cases n with
      | zero =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (character_mean hb r0 r1 r2 r3 2)
              (character_mean hb r0 r1 r2 r3 0)) (by decide)
      | succ n =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (character_mean hb r0 r1 r2 r3 (n+3))
              (character_mean hb r0 r1 r2 r3 (n+1)))
            (by simp only [Nat.succ_ne_zero, ↓reduceIte, if_neg (by omega : n+1+1 ≠ 1)]; decide)

/-- Only heat modes zero and two pair with the square of the fundamental. -/
theorem fundamental_square_pair {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) :
    let x := (exposedFourWord r0 r1 r2 r3).scalar
    let f := characterPolynomial x 1
    quaternionHaar blocks (polyMul (characterPolynomial x spin) (polyMul f f)) ≈
      (if spin = 0 then 1 else if spin = 2 then 1 else 0) := by
  let x := (exposedFourWord r0 r1 r2 r3).scalar
  let f := characterPolynomial x 1
  have hreassoc (s : Nat) : RatPolyCoeffEqv
      (polyMul (characterPolynomial x s) (polyMul f f))
      (polyMul f (polyMul f (characterPolynomial x s))) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      (((RatPolyCoeffEqv.mul_comm _ _).mul_right f).trans
        ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
          ((RatPolyCoeffEqv.mul_comm _ _).mul_left f)))
  cases spin with
  | zero =>
      exact Q'.eqv_trans _ _ _ (haar_of_coeff
        ((hreassoc 0).trans ((RatPolyCoeffEqv.refl f).mul
          (RatPolyCoeffEqv.mul_one f))))
        (fundamental_pair hb r0 r1 r2 r3 1)
  | succ n =>
      have hinner := first_mul_succ x n
      have hexpand : RatPolyCoeffEqv
          (polyMul (characterPolynomial x (n+1)) (polyMul f f))
          (polyAdd
            (polyMul f (characterPolynomial x (n+2)))
            (polyMul f (characterPolynomial x n))) :=
        (hreassoc (n+1)).trans
          ((hinner.mul_left f).trans (RatPolyCoeffEqv.mul_add_right f _ _))
      refine Q'.eqv_trans _ _ _ (haar_of_coeff hexpand) ?_
      refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
      cases n with
      | zero =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _)
                (fundamental_pair hb r0 r1 r2 r3 2))
              (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one f))
                (character_mean hb r0 r1 r2 r3 1))) (by decide)
      | succ n =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _)
                (fundamental_pair hb r0 r1 r2 r3 (n+3)))
              (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm _ _ _)
                (fundamental_pair hb r0 r1 r2 r3 (n+1))))
            (by
              cases n with
              | zero => decide
              | succ k =>
                  simp only [Nat.succ_ne_zero, ↓reduceIte,
                    if_neg (by omega : k+1+3 ≠ 1), if_neg (by omega : k+1+1 ≠ 1),
                    if_neg (by omega : k+1+1+1 ≠ 2)]
                  decide)

private theorem sum_insert (blocks : Nat) (g : Nat → RatPoly) (p : RatPoly) : ∀ xs,
    quaternionHaar blocks (polyMul (finitePolySum g xs) p) ≈
      listQSum (fun s => quaternionHaar blocks (polyMul (g s) p)) xs
  | [] => Q'.eqv_refl _
  | s :: xs => by
      change quaternionHaar blocks (polyMul (polyAdd (g s) (finitePolySum g xs)) p) ≈ _
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_insert blocks g p xs))

private theorem sum_append (g : Nat → Q') : ∀ xs ys,
    listQSum g (xs ++ ys) ≈ listQSum g xs + listQSum g ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _ :: xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (sum_append g xs ys))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_congr (f g : Nat → Q') : ∀ xs,
    (∀ s, s ∈ xs → f s ≈ g s) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | s :: xs, h => Q'.add_eqv_congr' (h s List.mem_cons_self)
      (sum_congr f g xs (fun t ht => h t (List.mem_cons_of_mem s ht)))

private theorem sum_zero (g : Nat → Q') : ∀ xs,
    (∀ s, s ∈ xs → g s ≈ 0) → listQSum g xs ≈ 0
  | [], _ => Q'.eqv_refl _
  | s::xs, h => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (h s List.mem_cons_self)
        (sum_zero g xs (fun t ht => h t (List.mem_cons_of_mem s ht)))) (by decide)

private theorem sum_selected (target : Nat) (value : Q') : ∀ extra,
    listQSum (fun s => if s = target then value else 0)
      (List.range (target+1+extra)) ≈ value
  | 0 => by
      rw [Nat.add_zero, List.range_succ]
      refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
      have hz : listQSum (fun s => if s = target then value else 0)
          (List.range target) ≈ 0 := by
        apply sum_zero
        intro s hs
        have hs' := List.mem_range.mp hs
        rw [if_neg (by omega : s ≠ target)]
        exact Q'.eqv_refl _
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hz
        (by simp only [listQSum, ↓reduceIte, Q'.add_zero']; exact Q'.eqv_refl _))
        (Q'.eqv_of_eq (Q'.zero_add' _))
  | extra+1 => by
      rw [show target+1+(extra+1) = (target+1+extra)+1 by omega, List.range_succ]
      refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sum_selected target value extra)
        (by simp only [listQSum, if_neg (by omega : target+1+extra ≠ target), Q'.add_zero']
            exact Q'.eqv_refl _))
        (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem heat_selected {blocks target K : Nat} (hK : target ≤ K)
    (w : Q') (x p : RatPoly)
    (hpair : ∀ spin, quaternionHaar blocks
      (polyMul (characterPolynomial x spin) p) ≈ if spin = target then 1 else 0) :
    quaternionHaar blocks (polyMul (heatPrefix w K x) p) ≈ coeffW w target := by
  unfold heatPrefix
  refine Q'.eqv_trans _ _ _ (sum_insert blocks _ p (List.range (K+1))) ?_
  have hc : ∀ spin, quaternionHaar blocks
      (polyMul (polySmul (coeffW w spin) (characterPolynomial x spin)) p) ≈
      (if spin = target then coeffW w target else 0) := by
    intro spin
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hpair spin)) ?_
    by_cases hs : spin = target
    · subst spin
      simp only
      exact Q'.mul_one_eqv _
    · simp only [if_neg hs]
      exact Q'.mul_zero_eqv _
  have hs := sum_congr
    (fun spin => quaternionHaar blocks
      (polyMul (polySmul (coeffW w spin) (characterPolynomial x spin)) p))
    (fun spin => if spin = target then coeffW w target else 0)
    (List.range (K+1)) (fun spin _ => hc spin)
  refine Q'.eqv_trans _ _ _ hs ?_
  have he : K+1 = target+1+(K-target) := by omega
  rw [he]
  exact sum_selected target (coeffW w target) (K-target)

/-- The exposed heat prefix has exact unit bare-Haar mass. -/
theorem heat_mass {blocks : Nat} (hb : 3 < blocks) (r0 r1 r2 r3 : Bool)
    (w : Q') (K : Nat) :
    quaternionHaar blocks (heatPrefix w K (exposedFourWord r0 r1 r2 r3).scalar) ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _))) ?_
  exact Q'.eqv_trans _ _ _
    (heat_selected (target := 0) (Nat.zero_le K) w _ polyOne
      (fun spin => Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_one _))
        (character_mean hb r0 r1 r2 r3 spin)))
    (Q'.eqv_of_eq (coeffW_zero w))

/-- The exact fundamental mean of the exposed heat law. -/
theorem heat_fundamental_moment {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (hK : 1 ≤ K) :
    let x := (exposedFourWord r0 r1 r2 r3).scalar
    let f := characterPolynomial x 1
    quaternionHaar blocks (polyMul (heatPrefix w K x) f) ≈ 2*RGTransport.qpow w 3 := by
  exact heat_selected (target := 1) hK w _ _ (fundamental_pair hb r0 r1 r2 r3)

private theorem sum_add (f g : Nat → Q') : ∀ xs,
    listQSum (fun s => f s + g s) xs ≈ listQSum f xs + listQSum g xs
  | [] => by change (0 : Q') ≈ 0+0; decide
  | s::xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (sum_add f g xs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => f s | 1 => g s | 2 => listQSum f xs | _ => listQSum g xs))

/-- Exact second moment; the only surviving heat labels are zero and two. -/
theorem heat_fundamental_square_moment {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (hK : 2 ≤ K) :
    let x := (exposedFourWord r0 r1 r2 r3).scalar
    let f := characterPolynomial x 1
    quaternionHaar blocks (polyMul (heatPrefix w K x) (polyMul f f)) ≈
      1 + 3*RGTransport.qpow w 8 := by
  let x := (exposedFourWord r0 r1 r2 r3).scalar
  let f := characterPolynomial x 1
  let a := fun s => if s = 0 then coeffW w 0 else 0
  let b := fun s => if s = 2 then coeffW w 2 else 0
  have hc (s : Nat) : quaternionHaar blocks
      (polyMul (polySmul (coeffW w s) (characterPolynomial x s)) (polyMul f f)) ≈
      a s + b s := by
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (fundamental_square_pair hb r0 r1 r2 r3 s)) ?_
    by_cases h0 : s = 0
    · subst s
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
    · by_cases h2 : s = 2
      · subst s
        exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm (QPoly.q_zero_add_eqv _))
      · simp only [a, b, if_neg h0, if_neg h2]
        exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _) (by decide)
  have hs := Q'.eqv_trans _ _ _ (sum_insert blocks
      (fun s => polySmul (coeffW w s) (characterPolynomial x s)) (polyMul f f)
      (List.range (K+1)))
    (Q'.eqv_trans _ _ _ (sum_congr _ (fun s => a s+b s) (List.range (K+1))
      (fun s _ => hc s)) (sum_add a b (List.range (K+1))))
  have h0 : listQSum a (List.range (K+1)) ≈ coeffW w 0 := by
    have he : K+1=0+1+K := by omega
    rw [he]
    exact sum_selected 0 (coeffW w 0) K
  have h2 : listQSum b (List.range (K+1)) ≈ coeffW w 2 := by
    have he : K+1=2+1+(K-2) := by omega
    rw [he]
    exact sum_selected 2 (coeffW w 2) (K-2)
  exact Q'.eqv_trans _ _ _ hs (Q'.add_eqv_congr' h0 h2)

end YMGap.Continuum.QuaternionHaarExposedHeatMoments

#print axioms YMGap.Continuum.QuaternionHaarExposedHeatMoments.fundamental_pair
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatMoments.fundamental_square_pair
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatMoments.heat_mass
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatMoments.heat_fundamental_moment
#print axioms YMGap.Continuum.QuaternionHaarExposedHeatMoments.heat_fundamental_square_moment
