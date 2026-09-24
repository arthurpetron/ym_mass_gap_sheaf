/-
# The computed degree-path Casimir is an actual differential sweep

The first variation of a finite cyclic heat sweep is the sum obtained by
inserting the negative head angular Laplacian at each step. This is proved
on the original Haar carrier by linear reassembly, not joint orthogonality.
-/

import YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
import YMGap.Continuum.SU2QuaternionCyclicModeTaylor

namespace YMGap.Continuum.SU2QuaternionCyclicCasimirSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicHeatLinear
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeReassembly
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem zero_supported (n : Nat) : SupportedQuaternionBlocks n polyZero := by
  intro t ht
  contradiction

private theorem sum_supported (n : Nat) (f : Nat → RatPoly)
    (hf : ∀ d, SupportedQuaternionBlocks n (f d)) : ∀ ids : List Nat,
    SupportedQuaternionBlocks n (polySum (ids.map f))
  | [] => zero_supported n
  | d::ds => polyAdd_supported (hf d) (sum_supported n f hf ds)

private theorem sum_coeff (f g : Nat → RatPoly)
    (h : ∀ d, RatPolyCoeffEqv (f d) (g d)) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [] => .refl _
  | d::ds => (h d).add (sum_coeff f g h ds)

private theorem sum_carrier (n : Nat) (f g : Nat → RatPoly)
    (h : ∀ d, HaarCarrierEqv n (f d) (g d)) : ∀ ids : List Nat,
    HaarCarrierEqv n (polySum (ids.map f)) (polySum (ids.map g))
  | [] => .refl _ _
  | d::ds => HaarCarrierEqv.add (h d) (sum_carrier n f g h ds)

private theorem regroup (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyAdd a b) (polyAdd c d))
      (polyAdd (polyAdd a c) (polyAdd b d)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem sum_add (f g : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySum (ids.map fun d => polyAdd (f d) (g d)))
      (polyAdd (polySum (ids.map f)) (polySum (ids.map g)))
  | [] => .refl _
  | d::ds => ((RatPolyCoeffEqv.refl _).add (sum_add f g ds)).trans
      (regroup (f d) (g d) _ _)

private theorem rotate_sum (n m : Nat) (f : Nat → RatPoly) : ∀ ids : List Nat,
    rotateIterate n m (polySum (ids.map f)) =
      polySum (ids.map fun d => rotateIterate n m (f d))
  | [] => by
      change rotateIterate n m polyZero = polyZero
      induction m with
      | zero => rfl
      | succ m ih => change cycleRotation n (rotateIterate n m polyZero) = polyZero; rw [ih]; rfl
  | d::ds => by simp only [List.map_cons, polySum, rotateIterate_add, rotate_sum n m f ds]

/-- The actual first-order insertion at the current head, then its rotation. -/
def casimirStep (tail : Nat) (p : RatPoly) : RatPoly :=
  cycleRotation (tail+1) (polyNeg (angularLaplacian p))

/-- First-order product rule for the original cyclic sweep. -/
def casimirSweep (tail : Nat) : Nat → RatPoly → RatPoly
  | 0, _ => polyZero
  | m+1, p => polyAdd (rotateIterate (tail+1) m (casimirStep tail p))
      (casimirSweep tail m (cycleRotation (tail+1) p))

theorem casimirStep_supported (tail : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    SupportedQuaternionBlocks (tail+1) (casimirStep tail p) :=
  rotateIterate_supported (tail+1) 1
    (neg_supported (angularLaplacian_supported (by omega) hp))

theorem casimirSweep_supported (tail : Nat) : ∀ (m : Nat) {p : RatPoly},
    SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) (casimirSweep tail m p)
  | 0, _, _ => zero_supported _
  | m+1, _, hp => polyAdd_supported
      (rotateIterate_supported (tail+1) m (casimirStep_supported tail hp))
      (casimirSweep_supported tail m (rotateIterate_supported (tail+1) 1 hp))

private theorem step_carrier (tail : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) (h : HaarCarrierEqv (tail+1) p q) :
    HaarCarrierEqv (tail+1) (casimirStep tail p) (casimirStep tail q) :=
  cycleRotation_carrier (tail+1)
    (neg_supported (angularLaplacian_supported (by omega) hp))
    (neg_supported (angularLaplacian_supported (by omega) hq))
    (HaarCarrierEqv.neg (angularLaplacian_carrier (by omega) h))

theorem casimirSweep_carrier (tail : Nat) : ∀ (m : Nat) {p q : RatPoly},
    SupportedQuaternionBlocks (tail+1) p → SupportedQuaternionBlocks (tail+1) q →
    HaarCarrierEqv (tail+1) p q →
    HaarCarrierEqv (tail+1) (casimirSweep tail m p) (casimirSweep tail m q)
  | 0, _, _, _, _, _ => .refl _ _
  | m+1, _, _, hp, hq, h => HaarCarrierEqv.add
      (rotateIterate_carrier (tail+1) m (casimirStep_supported tail hp)
        (casimirStep_supported tail hq) (step_carrier tail hp hq h))
      (casimirSweep_carrier tail m (rotateIterate_supported (tail+1) 1 hp)
        (rotateIterate_supported (tail+1) 1 hq)
        (cycleRotation_carrier (tail+1) hp hq h))

private theorem step_add (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    HaarCarrierEqv (tail+1) (casimirStep tail (polyAdd p q))
      (polyAdd (casimirStep tail p) (casimirStep tail q)) := by
  have he : RatPolyCoeffEqv (polyNeg (angularLaplacian (polyAdd p q)))
      (polyAdd (polyNeg (angularLaplacian p)) (polyNeg (angularLaplacian q))) :=
    (RatPolyCoeffEqv.neg (angularLaplacian_add p q)).trans
      (coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.var 1)))
        (.add (.neg (.var 0)) (.neg (.var 1))) (by decide)
        (fun | 0 => angularLaplacian p | _ => angularLaplacian q))
  have h := cycleRotation_carrier (tail+1)
    (neg_supported (angularLaplacian_supported (by omega) (polyAdd_supported hp hq)))
    (polyAdd_supported (neg_supported (angularLaplacian_supported (by omega) hp))
      (neg_supported (angularLaplacian_supported (by omega) hq)))
    (RatPolyCoeffEqv.haarCarrier he)
  simpa only [cycleRotation_add, casimirStep] using h

private theorem sweep_add (tail : Nat) : ∀ (m : Nat) (p q : RatPoly),
    SupportedQuaternionBlocks (tail+1) p → SupportedQuaternionBlocks (tail+1) q →
    HaarCarrierEqv (tail+1) (casimirSweep tail m (polyAdd p q))
      (polyAdd (casimirSweep tail m p) (casimirSweep tail m q))
  | 0, _, _, _, _ => .refl _ _
  | m+1, p, q, hp, hq => by
      have hfirst := rotateIterate_carrier (tail+1) m
        (casimirStep_supported tail (polyAdd_supported hp hq))
        (polyAdd_supported (casimirStep_supported tail hp) (casimirStep_supported tail hq))
        (step_add tail p q hp hq)
      rw [rotateIterate_add] at hfirst
      have hsecond := sweep_add tail m (cycleRotation (tail+1) p) (cycleRotation (tail+1) q)
        (rotateIterate_supported (tail+1) 1 hp) (rotateIterate_supported (tail+1) 1 hq)
      rw [← cycleRotation_add] at hsecond
      exact (HaarCarrierEqv.add hfirst hsecond).trans
        (RatPolyCoeffEqv.haarCarrier (regroup _ _ _ _))

private theorem sweep_zero (tail : Nat) : ∀ m : Nat,
    HaarCarrierEqv (tail+1) (casimirSweep tail m polyZero) polyZero
  | 0 => .refl _ _
  | m+1 => by
      have hz : casimirStep tail polyZero = polyZero := rfl
      change HaarCarrierEqv (tail+1)
        (polyAdd (rotateIterate (tail+1) m (casimirStep tail polyZero))
          (casimirSweep tail m polyZero)) polyZero
      rw [hz]
      exact (HaarCarrierEqv.add (rotateIterate_zero (tail+1) m) (sweep_zero tail m)).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero polyZero))

private theorem sweep_sum (tail m : Nat) (f : Nat → RatPoly)
    (hf : ∀ d, SupportedQuaternionBlocks (tail+1) (f d)) : ∀ ids : List Nat,
    HaarCarrierEqv (tail+1) (casimirSweep tail m (polySum (ids.map f)))
      (polySum (ids.map fun d => casimirSweep tail m (f d)))
  | [] => sweep_zero tail m
  | d::ds => (sweep_add tail m _ _ (hf d) (sum_supported (tail+1) f hf ds)).trans
      (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _) (sweep_sum tail m f hf ds))

private theorem fold_congr (tail : Nat) : ∀ (m : Nat) (p : RatPoly)
    (u v : List Nat → Q'), (∀ ds, Q'.eqv (u ds) (v ds)) →
    RatPolyCoeffEqv (modeFold tail m p u) (modeFold tail m p v)
  | 0, p, _, _, h => RatPolyCoeffEqv.smul_coefficient (h []) p
  | m+1, p, _u, _v, h => sum_coeff _ _
      (fun d => fold_congr tail m (nextPiece tail p d) _ _ (fun ds => h (d::ds))) _

private theorem fold_add (tail : Nat) : ∀ (m : Nat) (p : RatPoly) (u v : List Nat → Q'),
    RatPolyCoeffEqv (modeFold tail m p (fun ds => u ds + v ds))
      (polyAdd (modeFold tail m p u) (modeFold tail m p v))
  | 0, p, u, v => (RatPolyCoeffEqv.add_smul_same (u []) (v []) p).symm
  | m+1, p, u, v => (sum_coeff _ _
      (fun d => fold_add tail m (nextPiece tail p d) (fun ds => u (d::ds))
        (fun ds => v (d::ds))) _).trans (sum_add _ _ _)

private theorem fold_const (tail m : Nat) (p : RatPoly) (c : Q')
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (modeFold tail m p (fun _ => c))
      (polySmul c (rotateIterate (tail+1) m p)) :=
  (RatPolyCoeffEqv.haarCarrier (fold_congr tail m p _ _
    (fun _ => (Q'.mul_one_eqv c).symm))).trans
    ((RatPolyCoeffEqv.haarCarrier (modeFold_smul tail m p (fun _ => 1) c)).trans
      (HaarCarrierEqv.smul c (modeFold_one_carrier tail m p hp)))

/-- The computed path-Casimir tree equals the differential product rule. -/
theorem modeFold_casimir_carrier (tail : Nat) : ∀ (m : Nat) (p : RatPoly),
    SupportedQuaternionBlocks (tail+1) p →
    HaarCarrierEqv (tail+1) (modeFold tail m p totalCasimir) (casimirSweep tail m p)
  | 0, p, _ => RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_smul p)
  | m+1, p, hp => by
      let ids := branchDegrees tail p
      let c := fun d => Q'.ofNat (d*(d+2))
      let next := nextPiece tail p
      have hn (d : Nat) : SupportedQuaternionBlocks (tail+1) (next d) :=
        nextPiece_supported tail p d
      have hbranch (d : Nat) : HaarCarrierEqv (tail+1)
          (modeFold tail m (next d) (fun ds => totalCasimir (d::ds)))
          (polyAdd (polySmul (c d) (rotateIterate (tail+1) m (next d)))
            (casimirSweep tail m (next d))) :=
        (RatPolyCoeffEqv.haarCarrier (fold_add tail m (next d) (fun _ => c d) totalCasimir)).trans
          (HaarCarrierEqv.add (fold_const tail m (next d) (c d) (hn d))
            (modeFold_casimir_carrier tail m (next d) (hn d)))
      have htree := (sum_carrier (tail+1) _ _ hbranch ids).trans
        (RatPolyCoeffEqv.haarCarrier (sum_add _ _ ids))
      have hrot := rotateIterate_carrier (tail+1) m
        (sum_supported (tail+1) (fun d => polySmul (c d) (next d))
          (fun d => polySmul_supported (hn d) _) ids)
        (casimirStep_supported tail hp) (branchCasimir_rotation_carrier tail p hp)
      rw [rotate_sum] at hrot
      simp only [rotateIterate_smul] at hrot
      have hrest := (sweep_sum tail m next hn ids).symm.trans
        (casimirSweep_carrier tail m (sum_supported (tail+1) next hn ids)
          (rotateIterate_supported (tail+1) 1 hp) (branchPieces_one_carrier tail p hp))
      exact htree.trans (HaarCarrierEqv.add hrot hrest)

/-- Pair the actual full-cycle coefficient with any signed insertion. -/
theorem pairCasimir_sweep (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    Q'.eqv (pairCasimir tail p test)
      (quaternionHaar (tail+1) (polyMul test (casimirSweep tail (tail+1) p))) :=
  Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p test totalCasimir).symm
    (modeFold_casimir_carrier tail (tail+1) p hp test)

end YMGap.Continuum.SU2QuaternionCyclicCasimirSweep

#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSweep.casimirStep_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSweep.casimirSweep_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSweep.casimirSweep_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSweep.modeFold_casimir_carrier
#print axioms YMGap.Continuum.SU2QuaternionCyclicCasimirSweep.pairCasimir_sweep
