/-
# Exact finite heat Stein telescope for original distinct-link Wilson words

Keep the ENTIRE source fixed. Replace one literal lower letter at a time
by its upper letter, retaining the quaternion order and every other heat
factor. The four coordinate defects are paired with their computed Green
gradients. This is a signed identity, not a vector amplification inequality,
source-independent eigenpin, or quantitative interacting estimate.
-/

import YMGap.Continuum.SU2QuaternionSelectedHeatStein
import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
import YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect

namespace YMGap.Continuum.SU2QuaternionProductHeatWilsonStein

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionSelectedHeatStein
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul
local notation:max "H" n:arg => quaternionHaar n

private def fourPoly (f : Fin 4 → RatPoly) : RatPoly :=
  polyFour (f 0) (f 1) (f 2) (f 3)

private def fourValue (f : Fin 4 → Q') : Q' := f 0+(f 1+(f 2+f 3))

private def basisExpr (i : Fin 4) : PolyQuaternionExpr :=
  ⟨if i.val = 0 then .const 1 else .const 0,
   if i.val = 1 then .const 1 else .const 0,
   if i.val = 2 then .const 1 else .const 0,
   if i.val = 3 then .const 1 else .const 0⟩

private def basis (i : Fin 4) : PolyQuaternion :=
  let E := basisExpr i
  ⟨coeffEvalExpr (fun _ => polyZero) E.scalar,
   coeffEvalExpr (fun _ => polyZero) E.iPart,
   coeffEvalExpr (fun _ => polyZero) E.jPart,
   coeffEvalExpr (fun _ => polyZero) E.kPart⟩

/-- Every ordered prefix/suffix coefficient, including orientation signs. -/
def sandwichCoefficient (p s : PolyQuaternion) (reverse : Bool) (i : Fin 4) : RatPoly :=
  ((p ⋄ (if reverse then (basis i).conj else basis i)) ⋄ s).scalar

private theorem four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  simp only [Fin.ext_iff]
  omega

private theorem basis_supported (n : Nat) (i : Fin 4) : QuaternionSupported n (basis i) := by
  rcases four_cases i with rfl | rfl | rfl | rfl
  all_goals constructor <;> exact polySmul_supported (supported_one n) _

private theorem basis_degree (block : Nat) (i : Fin 4) :
    HasPolyQuaternionBlockDegree block 0 (basis i) := by
  rcases four_cases i with rfl | rfl | rfl | rfl
  all_goals constructor <;> exact (hasQuaternionBlockDegree_one block).smul _

private theorem coefficient_supported {n : Nat} {p s : PolyQuaternion}
    (hp : QuaternionSupported n p) (hs : QuaternionSupported n s)
    (reverse : Bool) (i : Fin 4) :
    SupportedQuaternionBlocks n (sandwichCoefficient p s reverse i) := by
  cases reverse
  · exact ((hp.mul (basis_supported n i)).mul hs).scalar
  · exact ((hp.mul (basis_supported n i).conj).mul hs).scalar

private theorem coefficient_degree {block : Nat} {p s : PolyQuaternion}
    (hp : HasPolyQuaternionBlockDegree block 0 p)
    (hs : HasPolyQuaternionBlockDegree block 0 s) (reverse : Bool) (i : Fin 4) :
    HasQuaternionBlockDegree block 0 (sandwichCoefficient p s reverse i) := by
  cases reverse
  · simpa only [Nat.zero_add] using ((hp.mul (basis_degree block i)).mul hs).scalar
  · simpa only [Nat.zero_add] using ((hp.mul (basis_degree block i).conj).mul hs).scalar

private def linearEnv (p c s : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => c.scalar | 5 => c.iPart | 6 => c.jPart | 7 => c.kPart
  | 8 => s.scalar | 9 => s.iPart | 10 => s.jPart | _ => s.kPart

private def coefficientExpr (reverse : Bool) (i : Fin 4) : PolyExpr :=
  (PolyQuaternionExpr.mul
    (PolyQuaternionExpr.mul (.coordinate 0)
      (if reverse then (basisExpr i).conj else basisExpr i)) (.coordinate 8)).scalar

private def assemblyExpr (reverse : Bool) : PolyExpr :=
  .add (.mul (coefficientExpr reverse 0) (.var 4))
    (.add (.mul (coefficientExpr reverse 1) (.var 5))
      (.add (.mul (coefficientExpr reverse 2) (.var 6))
        (.mul (coefficientExpr reverse 3) (.var 7))))

private theorem sandwich_linear (p s : PolyQuaternion) (block : Nat) (reverse : Bool) :
    RatPolyCoeffEqv (p ⋄ (orientedCoordinateQuaternion block reverse ⋄ s)).scalar
      (fourPoly (fun j => polyMul (sandwichCoefficient p s reverse j)
        (polyVar (4*block+j.val)))) := by
  let c := PolyQuaternion.coordinateVariable block
  cases reverse
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (.coordinate 0)
        (PolyQuaternionExpr.mul (.coordinate 4) (.coordinate 8))).scalar
      (assemblyExpr false) (by decide) (linearEnv p c s)
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (.coordinate 0)
        (PolyQuaternionExpr.mul (PolyQuaternionExpr.conj (.coordinate 4)) (.coordinate 8))).scalar
      (assemblyExpr true) (by decide) (linearEnv p c s)

private theorem four_congr (f g : Fin 4 → RatPoly) (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (fourPoly f) (fourPoly g) :=
  (h 0).add ((h 1).add ((h 2).add (h 3)))

private theorem four_add (f g : Fin 4 → RatPoly) :
    RatPolyCoeffEqv (polyAdd (fourPoly f) (fourPoly g))
      (fourPoly (fun i => polyAdd (f i) (g i))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3))))
      (.add (.var 4) (.add (.var 5) (.add (.var 6) (.var 7)))))
    (.add (.add (.var 0) (.var 4))
      (.add (.add (.var 1) (.var 5))
        (.add (.add (.var 2) (.var 6)) (.add (.var 3) (.var 7)))))
    (by decide) (fun
      | 0 => f 0 | 1 => f 1 | 2 => f 2 | 3 => f 3
      | 4 => g 0 | 5 => g 1 | 6 => g 2 | _ => g 3)

private theorem four_mul_difference (c x y : Fin 4 → RatPoly) (t : Q') :
    RatPolyCoeffEqv
      (polyAdd (fourPoly (fun j => polyMul (c j) (x j)))
        (polySmul t (fourPoly (fun j => polyMul (c j) (y j)))))
      (fourPoly (fun j => polyMul (c j) (polyAdd (x j) (polySmul t (y j))))) := by
  have hs : RatPolyCoeffEqv
      (polySmul t (fourPoly (fun j => polyMul (c j) (y j))))
      (fourPoly (fun j => polySmul t (polyMul (c j) (y j)))) :=
    (polyFour_smul t (polyMul (c 0) (y 0)) (polyMul (c 1) (y 1))
      (polyMul (c 2) (y 2)) (polyMul (c 3) (y 3))).symm
  have hj (j : Fin 4) : RatPolyCoeffEqv
      (polyAdd (polyMul (c j) (x j)) (polySmul t (polyMul (c j) (y j))))
      (polyMul (c j) (polyAdd (x j) (polySmul t (y j)))) :=
    ((RatPolyCoeffEqv.refl (polyMul (c j) (x j))).add
      (RatPolyCoeffEqv.polyMul_smul_right t (c j) (y j)).symm).trans
        (RatPolyCoeffEqv.mul_add_right (c j) (x j) (polySmul t (y j))).symm
  exact ((RatPolyCoeffEqv.refl (fourPoly (fun j => polyMul (c j) (x j)))).add hs).trans
    ((four_add _ _).trans (four_congr _ _ hj))

private theorem sandwich_difference (p s : PolyQuaternion) (a b : Nat)
    (reverse : Bool) (w : Q') :
    RatPolyCoeffEqv
      (polyAdd (p ⋄ (orientedCoordinateQuaternion a reverse ⋄ s)).scalar
        (polySmul (-(qpow w 3)) (p ⋄ (orientedCoordinateQuaternion b reverse ⋄ s)).scalar))
      (fourPoly (fun j => polyMul (sandwichCoefficient p s reverse j)
        (coordinateDifference a b w j))) := by
  exact ((sandwich_linear p s a reverse).add
    ((sandwich_linear p s b reverse).smul (-(qpow w 3)))).trans
      (four_mul_difference (sandwichCoefficient p s reverse)
        (fun j => polyVar (4*a+j.val)) (fun j => polyVar (4*b+j.val)) (-(qpow w 3)))

private theorem haar_four (n : Nat) (W : RatPoly) (f : Fin 4 → RatPoly) :
    H n (polyMul W (fourPoly f)) ≈ fourValue (fun j => H n (polyMul W (f j))) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n W _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n W _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polyMul_add_right n W _ _))))

private theorem fourValue_congr (f g : Fin 4 → Q') (h : ∀ i, f i ≈ g i) :
    fourValue f ≈ fourValue g := Q'.add_eqv_congr' (h 0)
      (Q'.add_eqv_congr' (h 1) (Q'.add_eqv_congr' (h 2) (h 3)))

private theorem one_supported (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem letter_supported {n i : Nat} (hi : i < n) (reverse : Bool) :
    QuaternionSupported n (orientedCoordinateQuaternion i reverse) := by
  cases reverse
  · exact QuaternionSupported.coordinate hi
  · exact (QuaternionSupported.coordinate hi).conj

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ => one_supported n
  | e::es, h => (letter_supported (h e List.mem_cons_self) e.reverse).mul
      (word_supported n block es (fun e he => h e (List.mem_cons_of_mem _ he)))

private theorem lift_supported_quaternion {n : Nat} {p : PolyQuaternion}
    (hp : QuaternionSupported n p) : QuaternionSupported (n+n) (liftQuaternion n p) :=
  ⟨lift_supported hp.scalar n, lift_supported hp.iPart n,
    lift_supported hp.jPart n, lift_supported hp.kPart n⟩

private theorem lift_degree (n i : Nat) (hi : i < n) (p : PolyQuaternion) :
    HasPolyQuaternionBlockDegree i 0 (liftQuaternion n p) :=
  ⟨independent_has_degree_zero (lift_lower_independent n p.scalar i hi),
    independent_has_degree_zero (lift_lower_independent n p.iPart i hi),
    independent_has_degree_zero (lift_lower_independent n p.jPart i hi),
    independent_has_degree_zero (lift_lower_independent n p.kPart i hi)⟩

/-- One literal link contribution, all FOUR coordinates and all remaining
original heat factors included. The source q is the same in every term. -/
def linkGradientSum (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (i : Fin n) (p s : PolyQuaternion) (reverse : Bool) (q r : RatPoly) : Q' :=
  let tail := n+n-1
  fourValue (fun j => selectedGradientPair tail (by have := i.isLt; omega)
    ⟨i.val, by have := i.isLt; omega⟩ ⟨n+i.val, by have := i.isLt; omega⟩ w K j q
    (polyMul (polyMul (productHeat n w K (eraseIndex i.val ids))
      (sandwichCoefficient (liftQuaternion n p) s reverse j)) (liftBoundary n r)))

private theorem haar_carrier_transport {m n : Nat} (h : m = n) (p : RatPoly) :
    H m p ≈ H n p := by
  cases h
  exact Q'.eqv_refl _

-- The Green polynomial must stay opaque when only carrier proof arguments
-- differ. Rewriting the whole goal would also rewrite the tail inside it.
attribute [local irreducible] selectedGradientPair

private theorem link_step (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (i : Fin n) (hi : i.val ∈ ids) (p s : PolyQuaternion) (reverse : Bool)
    (hp : QuaternionSupported n p) (hs : QuaternionSupported (n+n) s)
    (hds : HasPolyQuaternionBlockDegree i.val 0 s) (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (n+n) q) (hr : SupportedQuaternionBlocks n r) :
    H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
      (polyMul
        (polyAdd (liftQuaternion n p ⋄ (orientedCoordinateQuaternion i.val reverse ⋄ s)).scalar
          (polySmul (-(qpow w 3))
            (liftQuaternion n p ⋄ (orientedCoordinateQuaternion (n+i.val) reverse ⋄ s)).scalar))
        (liftBoundary n r))) ≈ linkGradientSum n w K ids i p s reverse q r := by
  let rest := eraseIndex i.val ids
  have hperm := select_perm i.val hi
  have hnrest := List.nodup_cons.mp (hperm.nodup_iff.mp hnd)
  have hrest : ∀ j, j ∈ rest → j < n := fun j hj =>
    hids j (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hj))
  have hsum := sandwich_difference (liftQuaternion n p) s i.val (n+i.val) reverse w
  have hfull := polynomialProduct_perm (fun j => heatAt j (n+j) w K) hperm
  have hsplit : H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
      (polyMul (fourPoly (fun j => polyMul (sandwichCoefficient (liftQuaternion n p) s reverse j)
        (coordinateDifference i.val (n+i.val) w j))) (liftBoundary n r))) ≈
      fourValue (fun j => H (n+n)
        (polyMul (polyMul q
          (polyMul (polyMul (productHeat n w K rest)
            (sandwichCoefficient (liftQuaternion n p) s reverse j)) (liftBoundary n r)))
          (polyMul (heatAt i.val (n+i.val) w K) (coordinateDifference i.val (n+i.val) w j)))) := by
    have hreorder : RatPolyCoeffEqv
        (polyMul (polyMul (productHeat n w K ids) q)
          (polyMul (fourPoly (fun j => polyMul (sandwichCoefficient (liftQuaternion n p) s reverse j)
            (coordinateDifference i.val (n+i.val) w j))) (liftBoundary n r)))
        (polyMul (polyMul (polyMul (productHeat n w K ids) q) (liftBoundary n r))
          (fourPoly (fun j => polyMul (sandwichCoefficient (liftQuaternion n p) s reverse j)
            (coordinateDifference i.val (n+i.val) w j)))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
        (fun | 0 => productHeat n w K ids | 1 => q
             | 2 => fourPoly (fun j => polyMul (sandwichCoefficient (liftQuaternion n p) s reverse j)
                 (coordinateDifference i.val (n+i.val) w j)) | _ => liftBoundary n r)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hreorder)
      (Q'.eqv_trans _ _ _ (haar_four _ _ _)
        (fourValue_congr _ _ (fun j => haar_of_coeff
          ((((hfull.mul_right q).mul_right (liftBoundary n r)).mul_right _).trans
            (coeffEvalExpr_eqv_of_normalize_eq
              (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
                (.mul (.var 4) (.var 5)))
              (.mul (.mul (.var 2) (.mul (.mul (.var 1) (.var 4)) (.var 3)))
                (.mul (.var 0) (.var 5))) (by decide)
              (fun | 0 => heatAt i.val (n+i.val) w K | 1 => productHeat n w K rest
                   | 2 => q | 3 => liftBoundary n r
                   | 4 => sandwichCoefficient (liftQuaternion n p) s reverse j
                   | _ => coordinateDifference i.val (n+i.val) w j))))))
  have hfirst := haar_of_coeff (blocks := n+n) ((hsum.mul_right (liftBoundary n r)).mul_left
    (polyMul (productHeat n w K ids) q))
  refine Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _ hsplit ?_)
  apply fourValue_congr
  intro j
  have hc := coefficient_supported (lift_supported_quaternion hp) hs reverse j
  have hdc := coefficient_degree (lift_degree n i.val i.isLt p) hds reverse j
  have hretain := supported_polyMul
    (supported_polyMul (productHeat_supported n w K rest hrest) hc) (lift_supported hr n)
  have hdretain := ((independent_has_degree_zero
    (productHeat_independent_lower n w K rest hrest i.val i.isLt hnrest.1)).mul hdc).mul
      (independent_has_degree_zero (lift_lower_independent n r i.val i.isLt))
  have he : n+n = (n+n-1)+1 := by have := i.isLt; omega
  have hq' : SupportedQuaternionBlocks ((n+n-1)+1) q := he ▸ hq
  have hretain' : SupportedQuaternionBlocks ((n+n-1)+1)
      (polyMul (polyMul (productHeat n w K rest)
        (sandwichCoefficient (liftQuaternion n p) s reverse j)) (liftBoundary n r)) :=
    he ▸ hretain
  have hstein := selected_coordinate_retained_source_gradient (n+n-1) (by have := i.isLt; omega)
    ⟨i.val, by omega⟩ ⟨n+i.val, by have := i.isLt; omega⟩
    (by change i.val ≠ n+i.val; have := i.isLt; omega) w K hK j q _ hq' hretain' hdretain
  exact Q'.eqv_trans _ _ _ (haar_carrier_transport he _) hstein

/-- Finite signed ordered sum. The original ids, source q and upper test r
are unchanged by recursion; only the literal upper prefix grows. -/
def wordGradientSum (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (block : OrientedBF4Link → Nat) :
    (es : List OrientedBF4Link) → (∀ e, e ∈ es → block e < n) →
      PolyQuaternion → RatPoly → RatPoly → Q'
  | [], _, _, _, _ => 0
  | e::es, hrange, p, q, r =>
      linkGradientSum n w K ids ⟨block e, hrange e List.mem_cons_self⟩ p
        (wordAt block es) e.reverse q r +
      qpow w 3 * wordGradientSum n w K ids block es
        (fun f hf => hrange f (List.mem_cons_of_mem e hf))
        (p ⋄ orientedCoordinateQuaternion (block e) e.reverse) q r

private def wordDifference (n : Nat) (w : Q') (block : OrientedBF4Link → Nat)
    (p : PolyQuaternion) (es : List OrientedBF4Link) : RatPoly :=
  polyAdd (liftQuaternion n p ⋄ wordAt block es).scalar
    (polySmul (-(qpow w (3*es.length))) (liftQuaternion n (p ⋄ wordAt block es)).scalar)

private theorem rate_step (w : Q') (m : Nat) :
    qpow w (3*(m+1)) ≈ qpow w 3 * qpow w (3*m) := by
  rw [show 3*(m+1) = 3+3*m by omega]
  exact qpow_add w 3 (3*m)

private theorem lift_letter (n i : Nat) (reverse : Bool) :
    liftQuaternion n (orientedCoordinateQuaternion i reverse) =
      orientedCoordinateQuaternion (n+i) reverse := by
  cases reverse <;> simp only [orientedCoordinateQuaternion, Bool.false_eq_true,
    if_false, if_true, liftQuaternion_conj, liftQuaternion_coordinateVariable]

private theorem telescope (L M U : RatPoly) (a b : Q') :
    RatPolyCoeffEqv (polyAdd L (polySmul (-(a*b)) U))
      (polyAdd (polyAdd L (polySmul (-a) M))
        (polySmul a (polyAdd M (polySmul (-b) U)))) := by
  have hneg : -a+a ≈ 0 :=
    poly_identity_of_normal_eq (.add (.neg (.var 0)) (.var 0)) (.const 0)
      (by decide) (fun _ => a)
  have hmul : a*(-b) ≈ -(a*b) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun
        | 0 => a
        | _ => b)
  have h : RatPolyCoeffEqv
      (polyAdd (polyAdd L (polySmul (-a) M))
        (polySmul a (polyAdd M (polySmul (-b) U))))
      (polyAdd (polyAdd (polyAdd L (polySmul (-a) M)) (polySmul a M))
        (polySmul a (polySmul (-b) U))) :=
    ((RatPolyCoeffEqv.refl (polyAdd L (polySmul (-a) M))).add
      (RatPolyCoeffEqv.smul_add a M (polySmul (-b) U))).trans
        (RatPolyCoeffEqv.add_assoc (polyAdd L (polySmul (-a) M))
          (polySmul a M) (polySmul a (polySmul (-b) U))).symm
  have hc : RatPolyCoeffEqv
      (polyAdd (polyAdd L (polySmul (-a) M)) (polySmul a M)) L :=
    (RatPolyCoeffEqv.add_assoc _ _ _).trans
      (((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.add_smul_same (-a) a M).trans
          ((RatPolyCoeffEqv.smul_coefficient hneg M).trans
            (RatPolyCoeffEqv.zero_smul M)))).trans (RatPolyCoeffEqv.add_zero L))
  exact (h.trans (hc.add ((RatPolyCoeffEqv.smul_assoc a (-b) U).trans
    (RatPolyCoeffEqv.smul_coefficient hmul U)))).symm

private theorem wordDifference_step (n : Nat) (w : Q') (block : OrientedBF4Link → Nat)
    (p : PolyQuaternion) (e : OrientedBF4Link) (es : List OrientedBF4Link) :
    RatPolyCoeffEqv (wordDifference n w block p (e::es))
      (polyAdd
        (polyAdd (liftQuaternion n p ⋄ (orientedCoordinateQuaternion (block e) e.reverse ⋄ wordAt block es)).scalar
          (polySmul (-(qpow w 3))
            (liftQuaternion n p ⋄ (orientedCoordinateQuaternion (n+block e) e.reverse ⋄ wordAt block es)).scalar))
        (polySmul (qpow w 3)
          (wordDifference n w block (p ⋄ orientedCoordinateQuaternion (block e) e.reverse) es))) := by
  let c := orientedCoordinateQuaternion (block e) e.reverse
  have hm : RatPolyCoeffEqv (liftQuaternion n p ⋄
      (orientedCoordinateQuaternion (n+block e) e.reverse ⋄ wordAt block es)).scalar
      (liftQuaternion n (p ⋄ c) ⋄ wordAt block es).scalar := by
    rw [liftQuaternion_mul, lift_letter]
    exact (PolyQuaternionCoeffEqv.mul_assoc _ _ _).scalar.symm
  have hu : RatPolyCoeffEqv (liftQuaternion n (p ⋄ wordAt block (e::es))).scalar
      (liftQuaternion n ((p ⋄ c) ⋄ wordAt block es)).scalar := by
    change RatPolyCoeffEqv (liftBoundary n _ ) (liftBoundary n _)
    exact lift_coeff n (PolyQuaternionCoeffEqv.mul_assoc _ _ _).scalar.symm
  have hr := Q'.neg_eqv_congr _ _ (rate_step w es.length)
  exact ((RatPolyCoeffEqv.refl _).add
    ((hu.smul _).trans (RatPolyCoeffEqv.smul_coefficient hr _))).trans
      ((telescope _ _ _ (qpow w 3) (qpow w (3*es.length))).trans
        ((RatPolyCoeffEqv.refl _).add
          ((hm.add (RatPolyCoeffEqv.refl _)).smul _)))

/-- Entire supported source, original full heat, and arbitrary upper test.
No source projection, mean replacement or source-degree assumption occurs. -/
theorem word_retained_source_gradient (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (p : PolyQuaternion) (hp : QuaternionSupported n p) (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (n+n) q) (hr : SupportedQuaternionBlocks n r) :
    H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
      (polyMul (wordDifference n w block p es) (liftBoundary n r))) ≈
      wordGradientSum n w K ids block es (fun e he => hids _ (hselected e he)) p q r := by
  induction es generalizing p with
  | nil =>
      have hzero : RatPolyCoeffEqv (wordDifference n w block p []) polyZero := by
        have hp0 := lift_coeff n (PolyQuaternionCoeffEqv.mul_one p).scalar
        exact ((PolyQuaternionCoeffEqv.mul_one (liftQuaternion n p)).scalar.add
          (hp0.smul (-1))).trans (RatPolyCoeffEqv.add_neg_smul _)
      exact haar_of_coeff (((hzero.mul_right _).mul_left _).trans
        (((RatPolyCoeffEqv.mul_zero_left _).mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))
  | cons e es ih =>
      have hn := List.nodup_cons.mp hword
      have hi := hids _ (hselected e List.mem_cons_self)
      have htail : ∀ f, f ∈ es → block f ∈ ids :=
        fun f hf => hselected f (List.mem_cons_of_mem e hf)
      have hrange : ∀ f, f ∈ es → block f < n := fun f hf => hids _ (htail f hf)
      have hs := word_supported (n+n) block es (fun f hf => by have := hrange f hf; omega)
      have hds := word_independent (block e) block es (fun f hf he =>
        hn.1 (List.mem_map.mpr ⟨f,hf,he.symm⟩))
      have hlink := link_step n w K hK ids hnd hids ⟨block e,hi⟩
        (hselected e List.mem_cons_self) p (wordAt block es) e.reverse hp hs hds q r hq hr
      have hp' := hp.mul (letter_supported hi e.reverse)
      have ht := ih hn.2 htail (p ⋄ orientedCoordinateQuaternion (block e) e.reverse) hp'
      have hcoeff := (wordDifference_step n w block p e es).mul_right (liftBoundary n r)
      have hsplit := haar_of_coeff (blocks := n+n)
        (hcoeff.mul_left (polyMul (productHeat n w K ids) q))
      rw [polyMul_add_left_exact] at hsplit
      exact Q'.eqv_trans _ _ _ hsplit
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
          (Q'.add_eqv_congr' hlink
            (Q'.eqv_trans _ _ _
              (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).mul_left _))
              (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _)
                (Q'.mul_eqv_congr_left _ _ _ ht)))))

private theorem shuffle (A q f r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul A q) (polyMul f r))
      (polyMul (polyMul (polyMul A q) r) f) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun | 0 => A | 1 => q | 2 => f | _ => r)

private theorem defect_pair_kernel (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f r : RatPoly) (a : Q') :
    H n (polyMul r (multiplicationDefect n w K ids q f a)) ≈
      H (n+n) (polyMul (polyMul (productHeat n w K ids) q)
        (polyMul (polyAdd f (polySmul (-a) (liftBoundary n f))) (liftBoundary n r))) := by
  let A := productHeat n w K ids
  have hfirst := productMap_pairing n w K ids (polyMul q f) r
  have hfirst' : RatPolyCoeffEqv (polyMul A (polyMul (polyMul q f) (liftBoundary n r)))
      (polyMul (polyMul A q) (polyMul f (liftBoundary n r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (by decide)
      (fun | 0 => A | 1 => q | 2 => f | _ => liftBoundary n r)
  have hsecond' : RatPolyCoeffEqv (polyMul r (polyMul (productMap n w K ids q) f))
      (polyMul (polyMul r f) (productMap n w K ids q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => r | 1 => productMap n w K ids q | _ => f)
  have hsecond := Q'.eqv_trans _ _ _ (haar_of_coeff hsecond')
    (productMap_pairing n w K ids q (polyMul r f))
  rw [lift_product] at hsecond
  have hsecond'' : RatPolyCoeffEqv
      (polyMul A (polyMul q (polyMul (liftBoundary n r) (liftBoundary n f))))
      (polyMul (polyMul A q) (polyMul (liftBoundary n f) (liftBoundary n r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 2))) (by decide)
      (fun | 0 => A | 1 => q | 2 => liftBoundary n r | _ => liftBoundary n f)
  have hsplit : H (n+n) (polyMul (polyMul A q)
      (polyMul (polyAdd f (polySmul (-a) (liftBoundary n f))) (liftBoundary n r))) ≈
      H (n+n) (polyMul (polyMul A q) (polyMul f (liftBoundary n r)))+
        (-a)*H (n+n) (polyMul (polyMul A q)
          (polyMul (liftBoundary n f) (liftBoundary n r))) := by
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (haar_of_coeff ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).mul_left _))
          (quaternionHaar_polyMul_smul_right _ _ _ _)))
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ hfirst (haar_of_coeff hfirst'))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ hsecond (haar_of_coeff hsecond'')))))
      (Q'.eqv_symm hsplit))

/-- Literal multiplicationDefect on the original heat and SAME entire source.
The right side is a computed finite signed sum of full-source derivatives,
not a decomposition hypothesis or a supplied Poisson solution. -/
theorem multiplicationDefect_word_source_gradient (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks n q) (hr : SupportedQuaternionBlocks n r) :
    H n (polyMul r (multiplicationDefect n w K ids q (wordAt block es).scalar
      (qpow w (3*es.length)))) ≈
      wordGradientSum n w K ids block es (fun e he => hids _ (hselected e he))
        PolyQuaternion.one q r := by
  have hrange : ∀ e, e ∈ es → block e < n := fun e he => hids _ (hselected e he)
  have hw := word_supported n block es hrange
  have hw2 := word_supported (n+n) block es (fun e he => by have := hrange e he; omega)
  have hq2 : SupportedQuaternionBlocks (n+n) q :=
    fun t ht => Nat.le_trans (hq t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  let a := qpow w (3*es.length)
  let W := polyMul (polyMul (productHeat n w K ids) q) (liftBoundary n r)
  have hW := supported_polyMul
    (supported_polyMul (productHeat_supported n w K ids hids) hq2) (lift_supported hr n)
  have hl := ((liftQuaternion_one (n+n) n).mul
    (PaddedQuaternionCoeffEqv.refl (n+n) (wordAt block es))).trans
      (PaddedQuaternionCoeffEqv.of_coeff (PolyQuaternionCoeffEqv.one_mul _))
  have hu := lift_coeff n (PolyQuaternionCoeffEqv.one_mul (wordAt block es)).scalar
  have hdiff : PaddedPolynomialCoeffEqv (n+n)
      (wordDifference n w block PolyQuaternion.one es)
      (polyAdd (wordAt block es).scalar
        (polySmul (-a) (liftBoundary n (wordAt block es).scalar))) :=
    PaddedPolynomialCoeffEqv.add hl.scalar
      ((PaddedPolynomialCoeffEqv.of_coeff (blocks := n+n) hu).smul (-a))
  have hleftSupport : SupportedQuaternionBlocks (n+n)
      (wordDifference n w block PolyQuaternion.one es) :=
    supported_add (((lift_supported_quaternion (one_supported n)).mul hw2).scalar)
      (polySmul_supported (lift_supported ((one_supported n).mul hw).scalar n) _)
  have hrightSupport : SupportedQuaternionBlocks (n+n)
      (polyAdd (wordAt block es).scalar (polySmul (-a) (liftBoundary n (wordAt block es).scalar))) :=
    supported_add hw2.scalar (polySmul_supported (lift_supported hw.scalar n) _)
  have hpin := PaddedPolynomialCoeffEqv.haar_insert hdiff hleftSupport hrightSupport W hW
  have ht := word_retained_source_gradient n w K hK ids hnd hids block es hword hselected
    PolyQuaternion.one (one_supported n) q r hq2 hr
  exact Q'.eqv_trans _ _ _ (defect_pair_kernel n w K ids q _ r a)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (shuffle _ _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpin)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (shuffle _ _ _ _).symm) ht)))

/-- Actual fundamental trace, including its factor TWO. No new source or
center is introduced: the exact upper test is only multiplied by two. -/
theorem multiplicationDefect_fundamental_word_source_gradient
    (n : Nat) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks n q) (hr : SupportedQuaternionBlocks n r) :
    H n (polyMul r (multiplicationDefect n w K ids q
      (characterPolynomial (wordAt block es).scalar 1) (qpow w (3*es.length)))) ≈
      wordGradientSum n w K ids block es (fun e he => hids _ (hselected e he))
        PolyQuaternion.one q (polySmul 2 r) := by
  let f := (wordAt block es).scalar
  let a := qpow w (3*es.length)
  have hmap := productMap_congr n w K ids (RatPolyCoeffEqv.polyMul_smul_right 2 q f)
  have hlin : RatPolyCoeffEqv (multiplicationDefect n w K ids q (polySmul 2 f) a)
      (polySmul 2 (multiplicationDefect n w K ids q f a)) :=
    ((hmap.trans (productMap_smul n w K ids 2 (polyMul q f))).add
      (((RatPolyCoeffEqv.polyMul_smul_right 2 _ f).smul (-a)).trans
        ((RatPolyCoeffEqv.smul_assoc (-a) 2 _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-a) 2) _).trans
            (RatPolyCoeffEqv.smul_assoc 2 (-a) _).symm)))).trans
              (RatPolyCoeffEqv.smul_add 2 _ _).symm
  have hp := multiplicationDefect_word_source_gradient n w K hK ids hnd hids block es
    hword hselected q (polySmul 2 r) hq (polySmul_supported hr 2)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((hlin.mul_left r).trans
    ((RatPolyCoeffEqv.polyMul_smul_right 2 r _).trans
      (RatPolyCoeffEqv.polyMul_smul_left 2 r _).symm))) hp

end YMGap.Continuum.SU2QuaternionProductHeatWilsonStein

#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.sandwichCoefficient
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.linkGradientSum
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.wordGradientSum
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.word_retained_source_gradient
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.multiplicationDefect_word_source_gradient
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonStein.multiplicationDefect_fundamental_word_source_gradient
