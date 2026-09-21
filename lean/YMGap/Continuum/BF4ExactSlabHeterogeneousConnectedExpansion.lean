/-
# Signed connected cancellation with face-dependent original couplings

The exact original action has a separate nome and cutoff at each face.
Disconnected selected supports cancel; finite inclusion-exclusion therefore
keeps only the existing computed connected selections. Spectator families
resum to the SAME heterogeneous partition square before absolute values.

Together with HeterogeneousHeatComparison this supplies the algebra,
per-coefficient bound and relative normalization inputs for a varying-background
spatial estimate. HeterogeneousDistanceDecay supplies the subsequent core sum.
-/
import YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison
import YMGap.Continuum.BF4ExactSlabLocalFactorProduct
import YMGap.Continuum.QuaternionHaarBiadditive

namespace YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound (pairedHeatRate)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabHeterogeneousHeatComparison (factor partition)
open YMGap.Continuum.BF4ExactSlabLocalFactorProduct (factorMoment)
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion (connectedSelections)
open YMGap.Continuum.BF4ExactSlabSpectatorResummation (disjoint_subfaces)
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.PolynomialBiadditiveMobius
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

variable (w : Nat → Q') (K : Nat → Nat) (extent : Nat)

def moment (ids : List Nat) (p : RatPoly) : Q' := factorMoment (factor w K extent) extent ids p

theorem partition_factorizes (xs ys : List Nat)
    (hd : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys)) :
    partition w K extent (xs++ys) ≈ partition w K extent xs * partition w K extent ys :=
  BF4ExactSlabLocalFactorProduct.partition_factorizes extent xs ys
    (fun id _ => heatFace_local (w id) (K id) extent id)
    (fun id _ => heatFace_local (w id) (K id) extent id)
    (fun id _ => heatFace_supported (w id) (K id) extent id)
    (fun id _ => heatFace_supported (w id) (K id) extent id) hd

theorem mixed_moment_factorizes (xs ys : List Nat) (left right : List Z4Link)
    (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys))
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    moment w K extent (xs++ys) (polyMul p q) ≈ moment w K extent xs p * moment w K extent ys q :=
  BF4ExactSlabLocalFactorProduct.mixed_moment_factorizes extent xs ys left right p q hp hq
    (fun id _ => heatFace_local (w id) (K id) extent id)
    (fun id _ => heatFace_local (w id) (K id) extent id)
    (fun id _ => heatFace_supported (w id) (K id) extent id)
    (fun id _ => heatFace_supported (w id) (K id) extent id) hl hr hd

theorem left_moment_factorizes (xs ys : List Nat) (left right : List Z4Link)
    (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p) (hl : LinkLocal extent left p) :
    moment w K extent (xs++ys) p ≈ moment w K extent xs p * partition w K extent ys :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_one p).symm.mul (RatPolyCoeffEqv.refl _)))
    (Q'.eqv_trans _ _ _
      (mixed_moment_factorizes w K extent xs ys left right hd p polyOne hp (supported_one _) hl (BlockLocal.one _ _))
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

private theorem right_moment_factorizes (xs ys : List Nat) (left right : List Z4Link)
    (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys))
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks extent) q) (hr : LinkLocal extent right q) :
    moment w K extent (xs++ys) q ≈ partition w K extent xs * moment w K extent ys q :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.one_mul q).symm.mul (RatPolyCoeffEqv.refl _)))
    (Q'.eqv_trans _ _ _
      (mixed_moment_factorizes w K extent xs ys left right hd polyOne q (supported_one _) hq (BlockLocal.one _ _) hr)
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

def connectedNumerator (ids : List Nat) (p q : RatPoly) : Q' :=
  moment w K extent ids (polyMul p q) * partition w K extent ids +
    -(moment w K extent ids p * moment w K extent ids q)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Exact cancellation for a supplied support split; not independence of the full slab. -/
theorem connectedNumerator_zero (xs ys : List Nat) (left right : List Z4Link)
    (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys))
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    connectedNumerator w K extent (xs++ys) p q ≈ 0 := by
  have hf : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys) :=
    fun link hx hy => hd link (List.mem_append.mpr (Or.inr hx)) (List.mem_append.mpr (Or.inr hy))
  have h := Q'.add_eqv_congr'
    (qmul (mixed_moment_factorizes w K extent xs ys left right hd p q hp hq hl hr)
      (partition_factorizes w K extent xs ys hf))
    (Q'.neg_eqv_congr _ _ (qmul (left_moment_factorizes w K extent xs ys left right hd p hp hl)
      (right_moment_factorizes w K extent xs ys left right hd q hq hr)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))) (.const 0) (by decide)
    (fun | 0 => moment w K extent xs p | 1 => partition w K extent xs
         | 2 => partition w K extent ys | _ => moment w K extent ys q))

theorem connectedNumerator_perm {xs ys : List Nat} (h : xs.Perm ys) (p q : RatPoly) :
    connectedNumerator w K extent xs p q ≈ connectedNumerator w K extent ys p q := by
  have he := polynomialProduct_perm (factor w K extent) h
  have hn (r : RatPoly) : moment w K extent xs r ≈ moment w K extent ys r :=
    haar_of_coeff ((RatPolyCoeffEqv.refl r).mul he)
  exact Q'.add_eqv_congr' (qmul (hn (polyMul p q)) (haar_of_coeff he))
    (Q'.neg_eqv_congr _ _ (qmul (hn p) (hn q)))

def connectedCoefficient (p q : RatPoly) (ids : List Nat) : Q' :=
  coefficient (fun ys => connectedNumerator w K extent ys p q) ids

theorem connectedCoefficient_pair_pin (p q : RatPoly) (ids : List Nat) :
    connectedCoefficient w K extent p q ids ≈
      pairedCoefficient (connected (blocks extent) p q)
        (fun id => faceHeatTail (w id) extent id 1 (K id)) ids :=
  Q'.eqv_trans _ _ _ (coefficient_congr _ _ ids (fun ys _ => Q'.eqv_symm
    (connected_diagonal (blocks extent) p q (polynomialProduct (factor w K extent) ys))))
    (pairedCoefficient_pin _ (factor w K extent) (fun id => faceHeatTail (w id) extent id 1 (K id))
      (fun id => faceHeat_eq_one_add (w id) extent id (K id)) ids)

/-- The actual signed coefficient pays a common small factor per selected
face. This bound alone is not a volume-independent connected sum. -/
theorem connectedCoefficient_bound {W : Q'}
    (hw0 : ∀ id, id ∈ slabPhysicalFaceEdges extent → (0 : Q') ≤ w id)
    (hwW : ∀ id, id ∈ slabPhysicalFaceEdges extent → w id ≤ W)
    (hW1 : W ≤ (1 : Q')) (hsmall : heatRatio W ≤ HalfPow.half)
    (p q : RatPoly) (c d : Q') (P : Interval (blocks extent) p c) (Q : Interval (blocks extent) q d)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Q'.abs (connectedCoefficient w K extent p q ids) ≤ (c*d+c*d)*(pairedHeatRate W)^ids.length :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (connectedCoefficient_pair_pin w K extent p q ids)))
    (pairedCoefficient_bound _ (blocks extent) (c*d+c*d) (heatRemainderBound W)
      (connected_bound P Q) (fun id => faceHeatTail (w id) extent id 1 (K id)) ids
      (fun id hid => BF4ExactSlabHeterogeneousHeatComparison.remainderInterval
        w K extent hw0 hwW hW1 hsmall id (hi id hid)))

section Separated
variable (p q : RatPoly) (left right : List Z4Link)
  (hp : SupportedQuaternionBlocks (blocks extent) p) (hq : SupportedQuaternionBlocks (blocks extent) q)
  (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
include hp hq hl hr

theorem numerator_zero_of_separator (ids : List Nat) (S : Separator extent left right ids) :
    connectedNumerator w K extent ids p q ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (connectedNumerator_perm w K extent (cut_partition ids S.cut) p q))
    (connectedNumerator_zero w K extent (cutLeft ids S.cut) (cutRight ids S.cut) left right S.disjoint p q hp hq hl hr)

theorem coefficient_zero_of_separator (ids : List Nat) (S : Separator extent left right ids) :
    connectedCoefficient w K extent p q ids ≈ 0 :=
  coefficient_zero_on _ _ (fun ys hy => numerator_zero_of_separator w K extent p q left right hp hq hl hr ys
    (S.restrict (fun id hid => selected_mem hy id hid)))

private theorem coefficient_zero_of_discard (ids : List Nat) (hk : keep extent left right ids = false) :
    connectedCoefficient w K extent p q ids ≈ 0 := by
  cases he : findSeparator extent left right ids with
  | none => simp only [keep, he, Option.isNone] at hk; cases hk
  | some S => exact coefficient_zero_of_separator w K extent p q left right hp hq hl hr ids S

/-- The SAME computed connected supports suffice, even with varying nomes and cutoffs. -/
theorem connectedNumerator_filtered (ids : List Nat) :
    connectedNumerator w K extent ids p q ≈
      listQSum (connectedCoefficient w K extent p q) (connectedSelections extent left right ids) :=
  reconstruct_filtered _ _ _ (fun ys _ hk => coefficient_zero_of_discard w K extent p q left right hp hq hl hr ys hk)
end Separated

def partitionSquare (ids : List Nat) : Q' := partition w K extent ids * partition w K extent ids

section Spectators
variable (p q : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (blocks extent) p) (hq : SupportedQuaternionBlocks (blocks extent) q)
  (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)
include hp hq hlp hlq

theorem numerator_spectator_factorizes (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    connectedNumerator w K extent (core++spectators) p q ≈
      connectedNumerator w K extent core p q * partitionSquare w K extent spectators := by
  have hn (r : RatPoly) (h : SupportedQuaternionBlocks (blocks extent) r) (hl : LinkLocal extent links r) :=
    left_moment_factorizes w K extent core spectators links [] hd r h hl
  have hz := partition_factorizes w K extent core spectators
    (fun link hc hs => hd link (List.mem_append.mpr (Or.inr hc)) hs)
  have he := Q'.add_eqv_congr'
    (qmul (hn (polyMul p q) (supported_polyMul hp hq) (BlockLocal.mul hlp hlq)) hz)
    (Q'.neg_eqv_congr _ _ (qmul (hn p hp hlp) (hn q hq hlq)))
  exact Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))
      (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 4)))))
    (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.mul (.var 4) (.var 4))) (by decide)
    (fun | 0 => moment w K extent core (polyMul p q) | 1 => partition w K extent core
         | 2 => moment w K extent core p | 3 => moment w K extent core q | _ => partition w K extent spectators))

theorem coefficient_spectator_factorizes (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    connectedCoefficient w K extent p q (core++spectators) ≈
      connectedCoefficient w K extent p q core * coefficient (partitionSquare w K extent) spectators :=
  coefficient_factorizes _ _ _ core spectators (fun a ha b hb =>
    numerator_spectator_factorizes w K extent p q links hp hq hlp hlq a b
      (disjoint_subfaces hd (fun id hi => selected_mem ha id hi) (fun id hi => selected_mem hb id hi)))

/-- Resum signed spectators BEFORE bounding: the exact varying-action Z^2 returns. -/
theorem spectatorSum_pin (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    listQSum (fun selected => connectedCoefficient w K extent p q (core++selected)) (selections spectators) ≈
      connectedCoefficient w K extent p q core * partitionSquare w K extent spectators :=
  Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun selected hs =>
    coefficient_spectator_factorizes w K extent p q links hp hq hlp hlq core selected
      (disjoint_subfaces hd (fun _ h => h) (fun id hi => selected_mem hs id hi))))
    (Q'.eqv_trans _ _ _ (listQSum_mul_left _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (reconstruct (partitionSquare w K extent) spectators)))
end Spectators

end YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion

#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.moment
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.partition_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.mixed_moment_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.left_moment_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedNumerator
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedNumerator_zero
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedNumerator_perm
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedCoefficient_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedCoefficient_bound
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.numerator_zero_of_separator
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.coefficient_zero_of_separator
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.connectedNumerator_filtered
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.partitionSquare
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.numerator_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.coefficient_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabHeterogeneousConnectedExpansion.spectatorSum_pin
