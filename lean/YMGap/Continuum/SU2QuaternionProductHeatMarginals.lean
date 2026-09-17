/-
# Exact selected-pair product heat on the original Haar carrier

Every selected lower link is paired with its original upper copy. Unselected
links are still integrated against Haar. The two marginals, conditional head
removal and orthogonality retain arbitrary supported polynomials, including
all spectator coordinates. Heat normalization is asserted only after Haar
integration, never as a false free-polynomial coefficient identity.
-/

import YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

namespace YMGap.Continuum.SU2QuaternionProductHeatMarginals

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (partialHaarHeads_supported_constant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv

def productHeat (n : Nat) (w : Q') (K : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (fun i => heatAt i (n+i) w K) ids

def productMap (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (f : RatPoly) : RatPoly :=
  kernelMap n (productHeat n w K ids) f

theorem productHeat_supported (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
      SupportedQuaternionBlocks (n+n) (productHeat n w K ids)
  | [], _ => supported_one _
  | i::ids, hi => supported_polyMul
      (heat_supported (by have := hi i List.mem_cons_self; omega)
        (by have := hi i List.mem_cons_self; omega) w K)
      (productHeat_supported n w K ids (fun j hj => hi j (List.mem_cons_of_mem i hj)))

theorem productMap_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (productMap n w K ids f) :=
  kernelMap_supported (productHeat_supported n w K ids hids) hf

theorem productMap_congr (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    {f g : RatPoly} (h : RatPolyCoeffEqv f g) :
    RatPolyCoeffEqv (productMap n w K ids f) (productMap n w K ids g) :=
  kernelMap_congr n _ h

theorem productMap_add (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (f g : RatPoly) :
    RatPolyCoeffEqv (productMap n w K ids (polyAdd f g))
      (polyAdd (productMap n w K ids f) (productMap n w K ids g)) :=
  kernelMap_add n _ f g

theorem productMap_nil (n : Nat) (w : Q') (K : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    RatPolyCoeffEqv (productMap n w K [] f) (cap (quaternionHaar n f)) :=
  (partialHaarHeads_congr n (RatPolyCoeffEqv.one_mul f)).trans
    (partialHaarHeads_supported_constant n hf)

private theorem scalar_conj_comm (p q : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.mul p (PolyQuaternion.conj q)).scalar
      (PolyQuaternion.mul q (PolyQuaternion.conj p)).scalar := by
  let environment : Nat → RatPoly := fun
    | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
    | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart
  simpa only [PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, environment,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) environment)

theorem heatAt_symm (a b : Nat) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (heatAt a b w K) (heatAt b a w K) := by
  have hs : RatPolyCoeffEqv (scalarAt a b) (scalarAt b a) :=
    scalar_conj_comm (PolyQuaternion.coordinateVariable a) (PolyQuaternion.coordinateVariable b)
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact .refl _
  | cons spin spins ih => exact ((characterPolynomial_coeffEqv hs spin).smul _).add ih

private theorem heat_vacuum_left (n i : Nat) (hi : i < n) (w : Q') (K : Nat)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (n+n) r)
    (hd : HasQuaternionBlockDegree i 0 r) :
    quaternionHaar (n+n) (polyMul (heatAt i (n+i) w K) r) ≈ quaternionHaar (n+n) r := by
  have he : (n+n-1)+1 = n+n := by omega
  have h := pair_vacuum (n+n-1) (by omega) ⟨i,by omega⟩ ⟨n+i,by omega⟩
    (by change i ≠ n+i; omega) w K r (by simpa only [he] using hr) hd
  simpa only [he] using h

private theorem heat_vacuum_right (n i : Nat) (hi : i < n) (w : Q') (K : Nat)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (n+n) r)
    (hd : HasQuaternionBlockDegree (n+i) 0 r) :
    quaternionHaar (n+n) (polyMul (heatAt i (n+i) w K) r) ≈ quaternionHaar (n+n) r := by
  have he : (n+n-1)+1 = n+n := by omega
  have h := pair_vacuum (n+n-1) (by omega) ⟨n+i,by omega⟩ ⟨i,by omega⟩
    (by change n+i ≠ i; omega) w K r (by simpa only [he] using hr) hd
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((heatAt_symm i (n+i) w K).mul_right r))
    (by simpa only [he] using h)

theorem productHeat_degree_zero (n slot : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → slot ≠ i ∧ slot ≠ n+i) →
      HasQuaternionBlockDegree slot 0 (productHeat n w K ids)
  | [], _ => hasQuaternionBlockDegree_one slot
  | i::ids, hi =>
      (heat_independent slot i (n+i) (hi i List.mem_cons_self).1
        (hi i List.mem_cons_self).2 w K).mul
        (productHeat_degree_zero n slot w K ids
          (fun j hj => hi j (List.mem_cons_of_mem i hj)))

theorem productHeat_independent_lower (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i < n) (hnot : i ∉ ids) :
    QuaternionBlockIndependent i (productHeat n w K ids) :=
  degree_zero_independent (productHeat_degree_zero n i w K ids
    (fun j hj => ⟨(by intro he; subst j; exact hnot hj), (by have := hids j hj; omega)⟩))

theorem productHeat_independent_upper (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (_hi : i < n) (hnot : i ∉ ids) :
    QuaternionBlockIndependent (n+i) (productHeat n w K ids) :=
  degree_zero_independent (productHeat_degree_zero n (n+i) w K ids
    (fun j hj => ⟨(by have := hids j hj; omega),
      (by
        intro he
        have hij : i = j := by omega
        subst j
        exact hnot hj)⟩))

private theorem lift_lower_degree (n : Nat) (f : RatPoly) :
    ∀ i, i < n → HasQuaternionBlockDegree i 0 (liftBoundary n f) := by
  induction n with
  | zero => intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
      intro i hi term hterm
      change term ∈ liftHead (liftBoundary n f) at hterm
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp hterm
      cases i with
      | zero => rfl
      | succ i =>
          have h := ih i (by omega) source hsource
          change quaternionBlockDegree (0::0::0::0::source.1) (i+1) = 0
          unfold quaternionBlockDegree exponentAt
          rw [Nat.mul_succ]
          change quaternionBlockDegree source.1 i = 0
          exact h

theorem lift_lower_independent (n : Nat) (g : RatPoly) (i : Nat) (hi : i < n) :
    QuaternionBlockIndependent i (liftBoundary n g) :=
  degree_zero_independent (lift_lower_degree n g i hi)

private theorem exponent_zero : ∀ (m : List Nat) (i : Nat),
    m.length ≤ i → exponentAt m i = 0
  | [], _, _ => rfl
  | _::_, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _::m, i+1, h => by
      change exponentAt m i = 0
      exact exponent_zero m i (by simp only [List.length_cons] at h; omega)

theorem supported_upper_independent {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (i : Nat) :
    QuaternionBlockIndependent (n+i) f := by
  apply degree_zero_independent
  intro term hterm
  have hl := hf term hterm
  unfold quaternionBlockDegree
  rw [exponent_zero term.1 _ (by omega), exponent_zero term.1 _ (by omega),
    exponent_zero term.1 _ (by omega), exponent_zero term.1 _ (by omega)]

private theorem product_vacuum (n : Nat) (w : Q') (K : Nat) (upper : Bool)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (n+n) r) :
    ∀ ids : List Nat, ids.Nodup → (∀ i, i ∈ ids → i < n) →
      (∀ i, i ∈ ids → HasQuaternionBlockDegree (if upper then n+i else i) 0 r) →
      quaternionHaar (n+n) (polyMul (productHeat n w K ids) r) ≈ quaternionHaar (n+n) r
  | [], _, _, _ => haar_of_coeff (RatPolyCoeffEqv.one_mul r)
  | i::ids, hn, hi, hd => by
      have hin := hi i List.mem_cons_self
      have hnd := List.nodup_cons.mp hn
      have hit (j : Nat) (hj : j ∈ ids) : j < n := hi j (List.mem_cons_of_mem i hj)
      have hdt (j : Nat) (hj : j ∈ ids) := hd j (List.mem_cons_of_mem i hj)
      have hrest := supported_polyMul (productHeat_supported n w K ids hit) hr
      have hleft := independent_has_degree_zero
        (productHeat_independent_lower n w K ids hit i hin hnd.1)
      have hright := independent_has_degree_zero
        (productHeat_independent_upper n w K ids hit i hin hnd.1)
      have hpeel : quaternionHaar (n+n)
          (polyMul (heatAt i (n+i) w K) (polyMul (productHeat n w K ids) r)) ≈
          quaternionHaar (n+n) (polyMul (productHeat n w K ids) r) := by
        cases upper with
        | false => exact heat_vacuum_left n i hin w K _ hrest (hleft.mul (hd i List.mem_cons_self))
        | true => exact heat_vacuum_right n i hin w K _ hrest (hright.mul (hd i List.mem_cons_self))
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
        (Q'.eqv_trans _ _ _ hpeel (product_vacuum n w K upper r hr ids hnd.2 hit hdt))

theorem productHeat_upper_marginal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar (n+n) (polyMul (productHeat n w K ids) (liftBoundary n f)) ≈
      quaternionHaar n f :=
  Q'.eqv_trans _ _ _
    (product_vacuum n w K false _ (lift_supported hf n) ids hn hids
      (fun i hi => lift_lower_degree n f i (hids i hi)))
    (haar_liftBoundary n n f)

theorem productHeat_lower_marginal (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar (n+n) (polyMul (productHeat n w K ids) f) ≈ quaternionHaar n f :=
  Q'.eqv_trans _ _ _
    (product_vacuum n w K true f
      (fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))) ids hn hids
      (fun i _ => independent_has_degree_zero (supported_upper_independent hf i)))
    (quaternionHaar_extend_supported_endpoint (by omega : n ≤ n+n) f hf)

/-- Exact pairing with the actual lower integration and upper drop convention. -/
theorem productMap_pairing (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (f g : RatPoly) :
    quaternionHaar n (polyMul g (productMap n w K ids f)) ≈
      quaternionHaar (n+n) (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g))) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing n n (polyMul (productHeat n w K ids) f) g))
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)))

private theorem head_degree {i d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree (i+1) d p) :
    HasQuaternionBlockDegree i d (partialHaarHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change quaternionBlockDegree (s.1.drop 4) i = d
  simpa only [quaternionBlockDegree, exponentAt_drop,
    show 4+4*i = 4*(i+1) by omega,
    show 4+(4*i+1) = 4*(i+1)+1 by omega,
    show 4+(4*i+2) = 4*(i+1)+2 by omega,
    show 4+(4*i+3) = 4*(i+1)+3 by omega] using hp s hs

private theorem heads_degree (n i d : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree (n+i) d p) :
    HasQuaternionBlockDegree i d (partialHaarHeads n p) := by
  induction n generalizing p with
  | zero => simpa only [Nat.zero_add] using hp
  | succ n ih =>
      apply ih
      apply head_degree (i := n+i)
      simpa only [Nat.succ_add, Nat.add_succ] using hp

private theorem lift_head_degree {i d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree i d p) :
    HasQuaternionBlockDegree (i+1) d (liftHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have he (j : Nat) : exponentAt (0::0::0::0::s.1) (4*(i+1)+j) =
      exponentAt s.1 (4*i+j) := by
    rw [show 4*(i+1)+j = (4*i+j)+4 by omega]
    rfl
  change exponentAt (0::0::0::0::s.1) (4*(i+1)+0) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+1) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+2) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+3) = d
  rw [he 0, he 1, he 2, he 3]
  exact hp s hs

private theorem lift_degree (n i d : Nat) {p : RatPoly}
    (hp : HasQuaternionBlockDegree i d p) :
    HasQuaternionBlockDegree (n+i) d (liftBoundary n p) := by
  induction n with
  | zero => simpa only [Nat.zero_add] using hp
  | succ n ih =>
      simpa only [Nat.succ_add, Nat.add_succ] using lift_head_degree ih

theorem lift_upper_independent (n : Nat) {g : RatPoly} {i : Nat}
    (hg : QuaternionBlockIndependent i g) :
    QuaternionBlockIndependent (n+i) (liftBoundary n g) :=
  degree_zero_independent (lift_degree n i 0 (independent_has_degree_zero hg))

/-- An unselected upper coordinate remains literally absent from the output. -/
theorem productMap_independent_of_not_mem (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i < n) (hnot : i ∉ ids)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    QuaternionBlockIndependent i (productMap n w K ids f) :=
  degree_zero_independent (heads_degree n i 0
    ((independent_has_degree_zero (productHeat_independent_upper n w K ids hids i hi hnot)).mul
      (independent_has_degree_zero (supported_upper_independent hf i))))

private theorem support_pair {n : Nat} {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) : SupportedQuaternionBlocks (n+n) f :=
  fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))

/-- Exact supported-test head removal for a conditionally constant input. -/
theorem productMap_cons_input_independent (n : Nat) (w : Q') (K : Nat)
    (i : Nat) (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) (f : RatPoly)
    (hf : SupportedQuaternionBlocks n f) (hd : QuaternionBlockIndependent i f) :
    SupportedHaarEqv n (productMap n w K (i::ids) f) (productMap n w K ids f) := by
  intro g hg
  have hr := supported_polyMul (productHeat_supported n w K ids hids)
    (supported_polyMul (support_pair hf) (lift_supported hg n))
  have hind := quaternionBlockIndependent_polyMul
    (productHeat_independent_lower n w K ids hids i hi hnot)
    (quaternionBlockIndependent_polyMul hd (lift_lower_independent n g i hi))
  have hpeel : quaternionHaar (n+n)
      (polyMul (productHeat n w K (i::ids)) (polyMul f (liftBoundary n g))) ≈
      quaternionHaar (n+n) (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (heat_vacuum_left n i hi w K _ hr (independent_has_degree_zero hind))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K (i::ids) f g)
    (Q'.eqv_trans _ _ _ hpeel (Q'.eqv_symm (productMap_pairing n w K ids f g)))

theorem head_removal (n : Nat) (w : Q') (K : Nat) (i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    SupportedHaarEqv n
      (productMap n w K (i::ids) (project i f))
      (productMap n w K ids (project i f)) :=
  productMap_cons_input_independent n w K i ids hi hnot hids _
    (project_supported i hf) (project_independent i f)

/-- The matching upper-endpoint marginal removes the head against an independent test. -/
theorem productMap_cons_test_independent (n : Nat) (w : Q') (K : Nat)
    (i : Nat) (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) (f g : RatPoly)
    (hf : SupportedQuaternionBlocks n f) (hg : SupportedQuaternionBlocks n g)
    (hd : QuaternionBlockIndependent i g) :
    quaternionHaar n (polyMul g (productMap n w K (i::ids) f)) ≈
      quaternionHaar n (polyMul g (productMap n w K ids f)) := by
  have hr := supported_polyMul (productHeat_supported n w K ids hids)
    (supported_polyMul (support_pair hf) (lift_supported hg n))
  have hind := quaternionBlockIndependent_polyMul
    (productHeat_independent_upper n w K ids hids i hi hnot)
    (quaternionBlockIndependent_polyMul (supported_upper_independent hf i) (lift_upper_independent n hd))
  have hpeel : quaternionHaar (n+n)
      (polyMul (productHeat n w K (i::ids)) (polyMul f (liftBoundary n g))) ≈
      quaternionHaar (n+n) (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (heat_vacuum_right n i hi w K _ hr (independent_has_degree_zero hind))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K (i::ids) f g)
    (Q'.eqv_trans _ _ _ hpeel (Q'.eqv_symm (productMap_pairing n w K ids f g)))

/-- A missing kinetic factor annihilates a genuinely conditionally centered input. -/
theorem productMap_absent_pair_zero (n : Nat) (w : Q') (K : Nat)
    (i : Nat) (ids : List Nat) (hi : i < n) (hnot : i ∉ ids)
    (hids : ∀ j, j ∈ ids → j < n) (f g : RatPoly)
    (hc : RatPolyCoeffEqv (project i f) polyZero) :
    quaternionHaar n (polyMul g (productMap n w K ids f)) ≈ 0 := by
  let r := polyMul (productHeat n w K ids) (liftBoundary n g)
  have hr : QuaternionBlockIndependent i r := quaternionBlockIndependent_polyMul
    (productHeat_independent_lower n w K ids hids i hi hnot) (lift_lower_independent n g i hi)
  have halg : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g))) (polyMul r f) :=
    ((RatPolyCoeffEqv.mul_comm f (liftBoundary n g)).mul_left _).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids f g)
    (Q'.eqv_trans _ _ _ (haar_of_coeff halg)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlock (n+n) i (by omega) r f hr)
        (haar_of_coeff ((hc.mul_left r).trans (RatPolyCoeffEqv.mul_zero_right r)))))

/-- The projected and fluctuating outputs are orthogonal on the SAME n-block carrier. -/
theorem cross_orthogonal (n : Nat) (w : Q') (K : Nat) (i : Nat) (ids : List Nat)
    (hi : i < n) (hnot : i ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (polyMul
      (productMap n w K ids (project i f))
      (productMap n w K (i::ids) (fluctuation i f))) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (productMap_cons_test_independent n w K i ids hi hnot hids _ _
      (fluctuation_supported i hf)
      (productMap_supported n w K ids hids (project_supported i hf))
      (productMap_independent_of_not_mem n w K ids hids i hi hnot _ (project_supported i hf)))
    (productMap_absent_pair_zero n w K i ids hi hnot hids _ _ (project_fluctuation_zero i f))

end YMGap.Continuum.SU2QuaternionProductHeatMarginals

#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_congr
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_add
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_nil
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.heatAt_symm
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_degree_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_independent_lower
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_independent_upper
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.lift_lower_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.supported_upper_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_upper_marginal
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat_lower_marginal
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.lift_upper_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_independent_of_not_mem
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_cons_input_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.head_removal
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_cons_test_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.productMap_absent_pair_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatMarginals.cross_orthogonal
