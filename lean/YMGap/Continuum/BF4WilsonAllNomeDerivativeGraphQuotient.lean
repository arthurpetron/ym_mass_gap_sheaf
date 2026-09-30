/-
# State quotients converge at witnessed original derivative graph points

The graph Taylor estimate is evaluated at one mesh step. Its squared
time factor cancels the squared quotient normalization exactly. The
cutoff comes from the supplied graph radius; no ambient domain or
representative choice is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh
import YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
import YMGap.Continuum.BF4WilsonAllNomeTimeAverages

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value unit_value)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (smul_sub)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation (stateQuotient)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "Sub" => completedSub hw0 hw1
local notation "Smul" => completedSmul hw0 hw1
local notation "M" => meshAction hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem quotient_time_normalization (k : Nat) :
    Q'.eqv (Q'.ofNat (2^k)*value ⟨k,1⟩) 1 := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (unit_value k))
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (half_power_normalizes k))

/-- Exact scaled remainder identity for the UNshifted state quotient. -/
theorem stateQuotient_error_pin (k : Nat) (u v : V) :
    Sub (stateQuotient hw0 hw1 k u) v =
      Smul (Q'.ofNat (2^k)) (remainder hw0 hw1 k 1 u v) := by
  let c := Q'.ofNat (2^k)
  let t := value ⟨k,1⟩
  have hc : Smul c (Smul t v) = v := by
    rw [completedSmul_mul,completedSmul_congr hw0 hw1
      (quotient_time_normalization k),completedSmul_one]
  calc
    Sub (stateQuotient hw0 hw1 k u) v =
        Sub (Smul c (Sub u (M k 1 u))) (Smul c (Smul t v)) := by
          change Sub (Smul c (Sub u (M k 1 u))) v = _
          rw [hc]
    _ = Smul c (Sub (Sub u (M k 1 u)) (Smul t v)) :=
      (smul_sub hw0 hw1 c (Sub u (M k 1 u)) (Smul t v)).symm
    _ = Smul c (remainder hw0 hw1 k 1 u v) := rfl

private theorem quotient_square_normalization (k : Nat) (epsilon : Q') :
    Q'.eqv
      ((Q'.ofNat (2^k)*Q'.ofNat (2^k))*
        ((value ⟨k,1⟩*value ⟨k,1⟩)*epsilon)) epsilon := by
  let c := Q'.ofNat (2^k)
  let t := value ⟨k,1⟩
  have hr : Q'.eqv ((c*c)*((t*t)*epsilon)) (((c*t)*(c*t))*epsilon) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
      (by decide) (fun | 0 => c | 1 => t | _ => epsilon)
  have hct : Q'.eqv (c*t) 1 := quotient_time_normalization k
  have hs : Q'.eqv ((c*t)*(c*t)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hct)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hct)
        (Q'.one_mul_eqv 1))
  exact Q'.eqv_trans _ _ _ hr
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon hs)
      (Q'.one_mul_eqv epsilon))

/-- The radius itself computes a closed-form all-tail mesh-depth cutoff. -/
def stateQuotientModulus {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (epsilon : Q') : Nat :=
  (radius hw0 hw1 G preimages epsilon).den

theorem unit_time_below_radius {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (epsilon : Q') (k : Nat)
    (hk : stateQuotientModulus hw0 hw1 G preimages epsilon ≤ k) :
    value ⟨k,1⟩ ≤ radius hw0 hw1 G preimages epsilon := by
  have hr := radius_positive hw0 hw1 G preimages epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (unit_value k))
    (Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc k)
      (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hk)
        (HalfPow.invSucc_den_le _ hr)))

/-- The unshifted state quotient converges to the graph OUTPUT with the
given explicit all-tail modulus and no additional analytic hypothesis. -/
theorem stateQuotient_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k : Nat)
    (hk : stateQuotientModulus hw0 hw1 G preimages epsilon ≤ k) :
    RCle (dist (stateQuotient hw0 hw1 k u) v) (rat epsilon) := by
  let c := Q'.ofNat (2^k)
  let t := value ⟨k,1⟩
  have ht := unit_time_below_radius hw0 hw1 G preimages epsilon k hk
  have hb := mesh_taylor_bound hw0 hw1 G preimages hpin epsilon he k 1 ht
  have hscaled := RCscale_mono (SumOfSquares.q_mul_self_nonneg c) hb
  have hcast : RCscale (c*c) (rat ((t*t)*epsilon)) =
      rat ((c*c)*((t*t)*epsilon)) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hcast] at hscaled
  have hfinish : RCle (rat ((c*c)*((t*t)*epsilon))) (rat epsilon) :=
    leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_of_eqv (quotient_square_normalization k epsilon))
  have h := RCle_trans hscaled hfinish
  unfold completedDist
  rw [stateQuotient_error_pin,completedInner_smul_left,
    completedInner_smul_right,RCscale_RCscale]
  exact h

/-- The explicit output certificate retains the rational cutoff as data. -/
def stateQuotientCertificate {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {N : Nat // ∀ k, N ≤ k →
      RCle (dist (stateQuotient hw0 hw1 k u) v) (rat epsilon)} :=
  ⟨stateQuotientModulus hw0 hw1 G preimages epsilon,
    stateQuotient_bound hw0 hw1 G preimages hpin epsilon he⟩

#print axioms stateQuotient_error_pin
#print axioms stateQuotientModulus
#print axioms unit_time_below_radius
#print axioms stateQuotient_bound
#print axioms stateQuotientCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphQuotient
