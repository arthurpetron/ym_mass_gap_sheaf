/-
# Three-column conditional Gram with the ORIGINAL shared tail

Three head copies of the complete positive W multiply the signed
determinant wedge of columns (a,c,1). Integrating its square gives six
times M*Gram(a,c)-J, J=A^2*H-2*A*b*C+U*b^2. No signed-input positivity,
normalizer inverse or conditional-mean mismatch omission is used.
Zero heads/tail are included. A useful comparison of M^2*Gram against
the SAME surviving interacting norm remains a separate analytic task.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionMultiHeadThreeGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini (partialHaarHead)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product lift_supported)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (partialHaarHeads_add partialHaarHeads_neg partialHaarHeads_smul)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (copy copy_mul copySupported copyCertificate partial_copy replica_product)
open YMGap.Continuum.SU2QuaternionMultiHeadConditionalGram (conditionalGram)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "I" heads:arg p:arg => partialHaarHeads heads p

/-- The literal ratio-free difference M*Gram-J. -/
def threeGramDifference (heads : Nat) (W a c : RatPoly) : RatPoly :=
  let M := I heads W
  let A := I heads (polyMul W a)
  let b := I heads (polyMul W c)
  let U := I heads (polyMul W (polyMul a a))
  let H := I heads (polyMul W (polyMul c c))
  let C := I heads (polyMul W (polyMul a c))
  let J := polyAdd (polyMul (polyMul A A) H)
    (polyAdd (polyNeg (polyAdd (polyMul (polyMul A b) C) (polyMul (polyMul A b) C)))
      (polyMul U (polyMul b b)))
  polyAdd (polyMul M (conditionalGram heads W a c)) (polyNeg J)

/-- Six original conditional moments, exposed for actual transfer consumers. -/
theorem threeGramDifference_expansion (heads : Nat) (W a c : RatPoly) :
    let M := I heads W
    let A := I heads (polyMul W a)
    let b := I heads (polyMul W c)
    let U := I heads (polyMul W (polyMul a a))
    let H := I heads (polyMul W (polyMul c c))
    let C := I heads (polyMul W (polyMul a c))
    RatPolyCoeffEqv (threeGramDifference heads W a c)
      (polyAdd (polyAdd (polyMul (polyMul M U) H)
        (polyAdd (polyMul (polyMul A b) C) (polyMul (polyMul A b) C)))
        (polyNeg (polyAdd (polyAdd (polyMul (polyMul A A) H) (polyMul U (polyMul b b)))
          (polyMul M (polyMul C C))))) := by
  dsimp only [threeGramDifference, conditionalGram]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 5) (.var 5)))))
      (.neg (.add (.mul (.mul (.var 1) (.var 1)) (.var 4))
        (.add (.neg (.add (.mul (.mul (.var 1) (.var 2)) (.var 5))
          (.mul (.mul (.var 1) (.var 2)) (.var 5)))) (.mul (.var 3) (.mul (.var 2) (.var 2)))))))
    (.add (.add (.mul (.mul (.var 0) (.var 3)) (.var 4))
      (.add (.mul (.mul (.var 1) (.var 2)) (.var 5)) (.mul (.mul (.var 1) (.var 2)) (.var 5))))
      (.neg (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 4)) (.mul (.var 3) (.mul (.var 2) (.var 2))))
        (.mul (.var 0) (.mul (.var 5) (.var 5))))))
    (by decide) (fun
      | 0 => I heads W
      | 1 => I heads (polyMul W a)
      | 2 => I heads (polyMul W c)
      | 3 => I heads (polyMul W (polyMul a a))
      | 4 => I heads (polyMul W (polyMul c c))
      | _ => I heads (polyMul W (polyMul a c)))

/-- Slots 1,2,3 are distinct; every surviving tail coordinate is shared. -/
def tripleTensor (heads : Nat) (p q r : RatPoly) : RatPoly :=
  polyMul (polyMul (copy heads (copy heads p)) (liftBoundary heads (copy heads q)))
    (liftBoundary heads (liftBoundary heads r))

private theorem lift_compose : ∀ (first second : Nat) (p : RatPoly),
    liftBoundary first (liftBoundary second p) = liftBoundary (first+second) p
  | 0, _, _ => by simp only [Nat.zero_add, liftBoundary]
  | first+1, second, p => by
      simp only [liftBoundary, Nat.succ_add, lift_compose first second p]

private theorem heads_compose : ∀ (first second : Nat) (p : RatPoly),
    I (first+second) p = I second (I first p)
  | 0, second, p => by
      simp only [Nat.zero_add, partialHaarHeads]
  | first+1, second, p => by
      rw [show first+1+second = (first+second)+1 by omega]
      exact heads_compose first second (partialHaarHead p)

/-- Exact three-copy product pin, without any independence of the shared tail. -/
theorem triple_product_pin (heads : Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (I (3*heads) (tripleTensor heads p q r))
      (polyMul (polyMul (I heads p) (I heads q)) (I heads r)) := by
  rw [show 3*heads = (heads+heads)+heads by omega, heads_compose]
  have hfirst : RatPolyCoeffEqv (I (heads+heads) (tripleTensor heads p q r))
      (polyMul (I (heads+heads) (polyMul (copy heads (copy heads p))
        (liftBoundary heads (copy heads q)))) r) := by
    unfold tripleTensor
    rw [lift_compose]
    exact partialHaarHeads_mul_lift (heads+heads) _ r
  have hpq := replica_product heads (copy heads p) (copy heads q)
  rw [partial_copy, partial_copy, ← lift_product] at hpq
  refine (partialHaarHeads_congr heads (hfirst.trans (hpq.mul_right r))).trans ?_
  exact (partialHaarHeads_congr heads (RatPolyCoeffEqv.mul_comm _ r)).trans
    ((partialHaarHeads_mul_lift heads r (polyMul (I heads p) (I heads q))).trans
      (RatPolyCoeffEqv.mul_comm _ _))

private theorem tensor_mul (heads : Nat) (p q r a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul (tripleTensor heads p q r) (tripleTensor heads a b c))
      (tripleTensor heads (polyMul p a) (polyMul q b) (polyMul r c)) := by
  dsimp only [tripleTensor]
  simp only [copy_mul, lift_product]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 3) (.var 4)) (.var 5)))
    (.mul (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5)))
    (by decide) (fun
      | 0 => copy heads (copy heads p)
      | 1 => liftBoundary heads (copy heads q)
      | 2 => liftBoundary heads (liftBoundary heads r)
      | 3 => copy heads (copy heads a)
      | 4 => liftBoundary heads (copy heads b)
      | _ => liftBoundary heads (liftBoundary heads c))

private inductive Column where
  | first | second | unit

private def column (a c : RatPoly) : Column → RatPoly
  | .first => a
  | .second => c
  | .unit => polyOne

private abbrev Row := Bool × (Column × (Column × Column))

/-- The six permutations of the three literal columns, including unit copies. -/
private def rows : List Row :=
  [(false, .first, .second, .unit), (false, .unit, .first, .second),
   (false, .second, .unit, .first), (true, .first, .unit, .second),
   (true, .second, .first, .unit), (true, .unit, .second, .first)]

private def signed (negative : Bool) (p : RatPoly) : RatPoly :=
  if negative then polyNeg p else p

private def term (heads : Nat) (a c : RatPoly) (row : Row) : RatPoly :=
  signed row.1 (tripleTensor heads (column a c row.2.1)
    (column a c row.2.2.1) (column a c row.2.2.2))

/-- The original six-term antisymmetric determinant wedge. -/
def threeGramWedge (heads : Nat) (a c : RatPoly) : RatPoly :=
  polySum (rows.map (term heads a c))

def threeGramReplica (heads : Nat) (W a c : RatPoly) : RatPoly :=
  polyMul (tripleTensor heads W W W)
    (polyMul (threeGramWedge heads a c) (threeGramWedge heads a c))

private theorem signed_congr (negative : Bool) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (signed negative p) (signed negative q) := by
  cases negative
  · exact h
  · exact RatPolyCoeffEqv.neg h

private def productTerm (heads : Nat) (W a c : RatPoly) (row other : Row) : RatPoly :=
  signed (row.1 != other.1) (tripleTensor heads
    (polyMul W (polyMul (column a c row.2.1) (column a c other.2.1)))
    (polyMul W (polyMul (column a c row.2.2.1) (column a c other.2.2.1)))
    (polyMul W (polyMul (column a c row.2.2.2) (column a c other.2.2.2))))

private theorem productTerm_pin (heads : Nat) (W a c : RatPoly) (row other : Row) :
    RatPolyCoeffEqv (polyMul (tripleTensor heads W W W)
      (polyMul (term heads a c row) (term heads a c other)))
      (productTerm heads W a c row other) := by
  have hsign (x y : Bool) (P Q R : RatPoly) : RatPolyCoeffEqv
      (polyMul R (polyMul (signed x P) (signed y Q)))
      (signed (x != y) (polyMul R (polyMul P Q))) := by
    have h := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 2) (.mul (if x then .neg (.var 0) else .var 0)
        (if y then .neg (.var 1) else .var 1)))
      (if x != y then .neg (.mul (.var 2) (.mul (.var 0) (.var 1)))
        else .mul (.var 2) (.mul (.var 0) (.var 1)))
      (by cases x <;> cases y <;> decide) (fun
        | 0 => P
        | 1 => Q
        | _ => R)
    cases x <;> cases y <;> exact h
  refine (hsign row.1 other.1 _ _ _).trans (signed_congr _ ?_)
  exact ((tensor_mul heads _ _ _ _ _ _).mul_left (tripleTensor heads W W W)).trans
    (tensor_mul heads W W W _ _ _)

private theorem sum_congr {α : Type} (xs : List α) (f g : α → RatPoly)
    (h : ∀ x, RatPolyCoeffEqv (f x) (g x)) :
    RatPolyCoeffEqv (polySum (xs.map f)) (polySum (xs.map g)) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (h x).add ih

private theorem weighted_sum_right {α : Type} (W p : RatPoly) (xs : List α)
    (f g : α → RatPoly) (h : ∀ x, RatPolyCoeffEqv (polyMul W (polyMul p (f x))) (g x)) :
    RatPolyCoeffEqv (polyMul W (polyMul p (polySum (xs.map f)))) (polySum (xs.map g)) := by
  induction xs with
  | nil =>
      exact ((RatPolyCoeffEqv.mul_zero_right p).mul_left W).trans
        (RatPolyCoeffEqv.mul_zero_right W)
  | cons x xs ih =>
      exact ((RatPolyCoeffEqv.mul_add_right p _ _).mul_left W).trans
        ((RatPolyCoeffEqv.mul_add_right W _ _).trans ((h x).add ih))

private theorem weighted_sum_product {α β : Type} (W : RatPoly) (xs : List α) (ys : List β)
    (f : α → RatPoly) (g : β → RatPoly) (out : α → β → RatPoly)
    (h : ∀ x y, RatPolyCoeffEqv (polyMul W (polyMul (f x) (g y))) (out x y)) :
    RatPolyCoeffEqv (polyMul W (polyMul (polySum (xs.map f)) (polySum (ys.map g))))
      (polySum (xs.map fun x => polySum (ys.map (out x)))) := by
  induction xs with
  | nil => exact RatPolyCoeffEqv.mul_zero_right W
  | cons x xs ih =>
      change RatPolyCoeffEqv (polyMul W (polyMul (polyAdd _ _) _)) (polyAdd _ _)
      rw [polyMul_add_left_exact]
      exact (RatPolyCoeffEqv.mul_add_right W _ _).trans
        ((weighted_sum_right W (f x) ys g (out x) (h x)).add ih)

private theorem integral_zero : ∀ (heads : Nat), I heads polyZero = polyZero
  | 0 => rfl
  | heads+1 => integral_zero heads

private theorem integral_sum (heads : Nat) (ps : List RatPoly) :
    RatPolyCoeffEqv (I heads (polySum ps)) (polySum (ps.map (partialHaarHeads heads))) := by
  induction ps with
  | nil =>
      change RatPolyCoeffEqv (I heads polyZero) polyZero
      rw [integral_zero]
      exact .refl _
  | cons p ps ih =>
      change RatPolyCoeffEqv (I heads (polyAdd p (polySum ps))) (polyAdd _ _)
      rw [partialHaarHeads_add]
      exact (RatPolyCoeffEqv.refl _).add ih

private def moment (heads : Nat) (W a c : RatPoly) : Column → Column → RatPoly
  | .first, .first => I heads (polyMul W (polyMul a a))
  | .second, .second => I heads (polyMul W (polyMul c c))
  | .first, .second => I heads (polyMul W (polyMul a c))
  | .second, .first => I heads (polyMul W (polyMul a c))
  | .first, .unit => I heads (polyMul W a)
  | .unit, .first => I heads (polyMul W a)
  | .second, .unit => I heads (polyMul W c)
  | .unit, .second => I heads (polyMul W c)
  | .unit, .unit => I heads W

private theorem moment_pin (heads : Nat) (W a c : RatPoly) (x y : Column) :
    RatPolyCoeffEqv (I heads (polyMul W (polyMul (column a c x) (column a c y))))
      (moment heads W a c x y) := by
  cases x <;> cases y
  · exact .refl _
  · exact .refl _
  · exact partialHaarHeads_congr heads ((RatPolyCoeffEqv.mul_one a).mul_left W)
  · exact partialHaarHeads_congr heads ((RatPolyCoeffEqv.mul_comm c a).mul_left W)
  · exact .refl _
  · exact partialHaarHeads_congr heads ((RatPolyCoeffEqv.mul_one c).mul_left W)
  · exact partialHaarHeads_congr heads ((RatPolyCoeffEqv.one_mul a).mul_left W)
  · exact partialHaarHeads_congr heads ((RatPolyCoeffEqv.one_mul c).mul_left W)
  · exact partialHaarHeads_congr heads
      (((RatPolyCoeffEqv.mul_one polyOne).mul_left W).trans (RatPolyCoeffEqv.mul_one W))

private def image (heads : Nat) (W a c : RatPoly) (row other : Row) : RatPoly :=
  signed (row.1 != other.1) (polyMul
    (polyMul (moment heads W a c row.2.1 other.2.1)
      (moment heads W a c row.2.2.1 other.2.2.1))
    (moment heads W a c row.2.2.2 other.2.2.2))

private theorem productIntegral_pin (heads : Nat) (W a c : RatPoly) (row other : Row) :
    RatPolyCoeffEqv (I (3*heads) (productTerm heads W a c row other))
      (image heads W a c row other) := by
  let X := tripleTensor heads
    (polyMul W (polyMul (column a c row.2.1) (column a c other.2.1)))
    (polyMul W (polyMul (column a c row.2.2.1) (column a c other.2.2.1)))
    (polyMul W (polyMul (column a c row.2.2.2) (column a c other.2.2.2)))
  have hi : RatPolyCoeffEqv (I (3*heads) (signed (row.1 != other.1) X))
      (signed (row.1 != other.1) (I (3*heads) X)) := by
    cases h : (row.1 != other.1)
    · exact .refl _
    · exact partialHaarHeads_neg (3*heads) _
  exact hi.trans (signed_congr _ ((triple_product_pin heads _ _ _).trans
    (((moment_pin heads W a c row.2.1 other.2.1).mul
      (moment_pin heads W a c row.2.2.1 other.2.2.1)).mul
      (moment_pin heads W a c row.2.2.2 other.2.2.2))))

private theorem replica_image (heads : Nat) (W a c : RatPoly) :
    RatPolyCoeffEqv (I (3*heads) (threeGramReplica heads W a c))
      (polySum (rows.map fun row => polySum (rows.map (image heads W a c row)))) := by
  have h := weighted_sum_product (tripleTensor heads W W W) rows rows
    (term heads a c) (term heads a c) (productTerm heads W a c) (productTerm_pin heads W a c)
  refine (partialHaarHeads_congr (3*heads) h).trans ?_
  refine (integral_sum (3*heads) _).trans ?_
  simp only [List.map_map]
  apply sum_congr rows
  intro row
  exact (integral_sum (3*heads) _).trans
    (sum_congr rows _ _ (productIntegral_pin heads W a c row))

section ReplicaContraction

-- Only the closed six-row syntax is reduced here, never the original
-- moment polynomials or their finite Haar integrations.
attribute [local irreducible] polyMul polyAdd polyNeg polySmul partialHaarHeads

set_option maxHeartbeats 2000000 in
/-- Integrating the actual three-head wedge square is SIX times M*Gram-J. -/
theorem threeGramReplica_identity (heads : Nat) (W a c : RatPoly) :
    RatPolyCoeffEqv (I (3*heads) (threeGramReplica heads W a c))
      (polySmul 6 (threeGramDifference heads W a c)) := by
  refine (replica_image heads W a c).trans ?_
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.mul (.var 3) (.var 4)) (.var 0)) (.add (.mul (.mul (.var 1) (.var 5)) (.var 2)) (.add (.mul (.mul (.var 5) (.var 2)) (.var 1)) (.add (.neg (.mul (.mul (.var 3) (.var 2)) (.var 2))) (.add (.neg (.mul (.mul (.var 5) (.var 5)) (.var 0))) (.add (.neg (.mul (.mul (.var 1) (.var 4)) (.var 1))) (.var 6))))))) (.add (.add (.mul (.mul (.var 1) (.var 5)) (.var 2)) (.add (.mul (.mul (.var 0) (.var 3)) (.var 4)) (.add (.mul (.mul (.var 2) (.var 1)) (.var 5)) (.add (.neg (.mul (.mul (.var 1) (.var 1)) (.var 4))) (.add (.neg (.mul (.mul (.var 2) (.var 3)) (.var 2))) (.add (.neg (.mul (.mul (.var 0) (.var 5)) (.var 5))) (.var 6))))))) (.add (.add (.mul (.mul (.var 5) (.var 2)) (.var 1)) (.add (.mul (.mul (.var 2) (.var 1)) (.var 5)) (.add (.mul (.mul (.var 4) (.var 0)) (.var 3)) (.add (.neg (.mul (.mul (.var 5) (.var 0)) (.var 5))) (.add (.neg (.mul (.mul (.var 4) (.var 1)) (.var 1))) (.add (.neg (.mul (.mul (.var 2) (.var 2)) (.var 3))) (.var 6))))))) (.add (.add (.neg (.mul (.mul (.var 3) (.var 2)) (.var 2))) (.add (.neg (.mul (.mul (.var 1) (.var 1)) (.var 4))) (.add (.neg (.mul (.mul (.var 5) (.var 0)) (.var 5))) (.add (.mul (.mul (.var 3) (.var 0)) (.var 4)) (.add (.mul (.mul (.var 5) (.var 1)) (.var 2)) (.add (.mul (.mul (.var 1) (.var 2)) (.var 5)) (.var 6))))))) (.add (.add (.neg (.mul (.mul (.var 5) (.var 5)) (.var 0))) (.add (.neg (.mul (.mul (.var 2) (.var 3)) (.var 2))) (.add (.neg (.mul (.mul (.var 4) (.var 1)) (.var 1))) (.add (.mul (.mul (.var 5) (.var 1)) (.var 2)) (.add (.mul (.mul (.var 4) (.var 3)) (.var 0)) (.add (.mul (.mul (.var 2) (.var 5)) (.var 1)) (.var 6))))))) (.add (.add (.neg (.mul (.mul (.var 1) (.var 4)) (.var 1))) (.add (.neg (.mul (.mul (.var 0) (.var 5)) (.var 5))) (.add (.neg (.mul (.mul (.var 2) (.var 2)) (.var 3))) (.add (.mul (.mul (.var 1) (.var 2)) (.var 5)) (.add (.mul (.mul (.var 2) (.var 5)) (.var 1)) (.add (.mul (.mul (.var 0) (.var 4)) (.var 3)) (.var 6))))))) (.var 6)))))))
    (.add (.mul (.const 6) (.add (.add (.mul (.mul (.var 0) (.var 3)) (.var 4)) (.add (.mul (.mul (.var 1) (.var 2)) (.var 5)) (.mul (.mul (.var 1) (.var 2)) (.var 5)))) (.neg (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 4)) (.mul (.var 3) (.mul (.var 2) (.var 2)))) (.mul (.var 0) (.mul (.var 5) (.var 5))))))) (.mul (.const 7) (.var 6)))
    (by decide) (fun
      | 0 => I heads W
      | 1 => I heads (polyMul W a)
      | 2 => I heads (polyMul W c)
      | 3 => I heads (polyMul W (polyMul a a))
      | 4 => I heads (polyMul W (polyMul c c))
      | 5 => I heads (polyMul W (polyMul a c))
      | _ => polyZero)
  -- polySum ends in the empty polynomial, not in a coefficient-zero
  -- singleton. The seven sentinels were represented by that SAME var 6.
  exact hr.trans (((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.mul_zero_right _)).trans
    ((RatPolyCoeffEqv.add_zero _).trans ((cap_mul_left 6 _).trans
    ((threeGramDifference_expansion heads W a c).symm.smul 6))
    ))

end ReplicaContraction

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem tensor_supported (tail heads : Nat) {p q r : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+heads) p)
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hr : SupportedQuaternionBlocks (tail+heads) r) :
    SupportedQuaternionBlocks (tail+3*heads) (tripleTensor heads p q r) := by
  have hp' : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads p) := by
    simpa only [Nat.add_assoc] using copySupported tail heads hp
  have hfirst : SupportedQuaternionBlocks (tail+3*heads) (copy heads (copy heads p)) := by
    simpa only [show (tail+heads)+(heads+heads) = tail+3*heads by omega]
      using copySupported (tail+heads) heads hp'
  have hmiddle : SupportedQuaternionBlocks (tail+3*heads) (liftBoundary heads (copy heads q)) := by
    simpa only [show (tail+(heads+heads))+heads = tail+3*heads by omega]
      using lift_supported (copySupported tail heads hq) heads
  have hlast : SupportedQuaternionBlocks (tail+3*heads) (liftBoundary heads (liftBoundary heads r)) := by
    simpa only [show ((tail+heads)+heads)+heads = tail+3*heads by omega]
      using lift_supported (lift_supported hr heads) heads
  exact supported_polyMul (supported_polyMul hfirst hmiddle) hlast

private theorem column_supported (tail heads : Nat) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c) (x : Column) :
    SupportedQuaternionBlocks (tail+heads) (column a c x) := by
  cases x
  · exact ha
  · exact hc
  · exact supported_one _

private theorem sum_supported {α : Type} (blocks : Nat) (xs : List α) (f : α → RatPoly)
    (hf : ∀ x, SupportedQuaternionBlocks blocks (f x)) :
    SupportedQuaternionBlocks blocks (polySum (xs.map f)) := by
  induction xs with
  | nil =>
      intro t ht
      cases ht
  | cons x xs ih =>
      exact supported_add (hf x) ih

/-- The complete positive W is retained in all three copies.
Neither signed column a nor signed column c needs a positivity witness. -/
def threeGramReplica_certificate (tail heads : Nat) (W a c : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c)
    (PW : Certificate (tail+heads) W) :
    Certificate (tail+3*heads) (threeGramReplica heads W a c) := by
  have hW' : SupportedQuaternionBlocks ((tail+heads)+heads) (copy heads W) := by
    simpa only [Nat.add_assoc] using copySupported tail heads hW
  have PW' : Certificate ((tail+heads)+heads) (copy heads W) := by
    simpa only [Nat.add_assoc] using copyCertificate tail heads W hW PW
  have Pfirst : Certificate (tail+3*heads) (copy heads (copy heads W)) := by
    simpa only [show (tail+heads)+(heads+heads) = tail+3*heads by omega]
      using copyCertificate (tail+heads) heads (copy heads W) hW' PW'
  have Pmiddle : Certificate (tail+3*heads) (liftBoundary heads (copy heads W)) := by
    simpa only [show (tail+(heads+heads))+heads = tail+3*heads by omega]
      using lift_certificate heads (copyCertificate tail heads W hW PW)
  have Plast : Certificate (tail+3*heads) (liftBoundary heads (liftBoundary heads W)) := by
    simpa only [show ((tail+heads)+heads)+heads = tail+3*heads by omega]
      using lift_certificate heads (lift_certificate heads PW)
  have hwedge : SupportedQuaternionBlocks (tail+3*heads) (threeGramWedge heads a c) := by
    apply sum_supported
    intro row
    have hs := tensor_supported tail heads
      (column_supported tail heads ha hc row.2.1)
      (column_supported tail heads ha hc row.2.2.1)
      (column_supported tail heads ha hc row.2.2.2)
    dsimp only [term, signed]
    cases row.1
    · exact hs
    · exact supported_neg hs
  exact ((Pfirst.mul Pmiddle).mul Plast).mul (Certificate.square _ hwedge)

private theorem sixth_six (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (Q'.invSucc 5) (polySmul 6 p)) p :=
  (RatPolyCoeffEqv.smul_assoc _ _ p).trans
    ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((Q'.invSucc 5)*6) 1) p).trans
      (RatPolyCoeffEqv.one_smul p))

/-- The constructed three-column conditional Gram difference.
No normalizer is inverted or cancelled, and every surviving tail stays shared. -/
def conditionalThreeGram_certificate (tail heads : Nat) (W a c : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (ha : SupportedQuaternionBlocks (tail+heads) a)
    (hc : SupportedQuaternionBlocks (tail+heads) c)
    (PW : Certificate (tail+heads) W) :
    Certificate tail (threeGramDifference heads W a c) :=
  .ofCoeff (sixth_six _).symm
    (.smul (Q'.invSucc 5) (by decide)
      (.ofCoeff (threeGramReplica_identity heads W a c).symm
        (partialHaarHeads_certificate tail (3*heads)
          (threeGramReplica_certificate tail heads W a c hW ha hc PW))))

#print axioms threeGramDifference
#print axioms threeGramDifference_expansion
#print axioms triple_product_pin
#print axioms threeGramReplica_identity
#print axioms threeGramReplica_certificate
#print axioms conditionalThreeGram_certificate

end YMGap.Continuum.SU2QuaternionMultiHeadThreeGram
