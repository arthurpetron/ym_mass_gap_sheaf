/-
# A same-operator form for the actual omitted heat modes

The ragged tree depends on its input. A computed maximum over ALL its
branches supplies a saturating auxiliary cutoff. At one common saturation
cutoff for two inputs, their omitted pairings are differences of the SAME
two product-heat forms. This proves symmetry, not an assumed spectral join.
The actual omitted diagonal is positive, so the existing constructive
Cauchy--Schwarz theorem applies. The resulting bound uses Haar squares,
not absolute leaf sums. No original action or heat cutoff is replaced.
-/

import YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
import YMGap.Continuum.SU2QuaternionProductHeatDualForm

namespace YMGap.Continuum.SU2QuaternionCyclicOmittedOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCutoffDebt
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Maximum over all computed degrees, including every rotated descendant.
It carries the finite witness; no existential degree envelope is erased. -/
def pathMax (tail : Nat) : Nat → RatPoly → Nat
  | 0, _ => 0
  | m+1, p => ((branchDegrees tail p).map fun d =>
      max d (pathMax tail m (nextPiece tail p d))).foldr Nat.max 0

private theorem member_le_max (f : Nat → Nat) : ∀ (ids : List Nat) (d : Nat),
    d ∈ ids → f d ≤ (ids.map f).foldr Nat.max 0
  | [], _, h => by contradiction
  | a::ids, d, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst d
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (member_le_max f ids d ht) (Nat.le_max_right _ _)

/-- Every valid full-depth path is retained at the computed envelope. -/
theorem pathMax_retained (tail : Nat) :
    ∀ (m : Nat) (p : RatPoly) (ds : List Nat) (M : Nat),
      ds.length = m → ValidPath tail p ds → pathMax tail m p ≤ M →
      retained M ds = true
  | 0, _, [], _, _, _, _ => rfl
  | 0, _, _::_, _, hlen, _, _ => False.elim (Nat.noConfusion hlen)
  | _+1, _, [], _, hlen, _, _ => False.elim (Nat.noConfusion hlen)
  | m+1, p, d::ds, M, hlen, hpath, hM => by
      have hb : max d (pathMax tail m (nextPiece tail p d)) ≤ pathMax tail (m+1) p :=
        member_le_max (fun k => max k (pathMax tail m (nextPiece tail p k)))
          (branchDegrees tail p) d hpath.1
      have hd : d ≤ M := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hb hM)
      have ht : pathMax tail m (nextPiece tail p d) ≤ M :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hb hM)
      have hrest := pathMax_retained tail m (nextPiece tail p d) ds M
        (by simp only [List.length_cons] at hlen; omega)
        hpath.2 ht
      simp only [retained, hd, decide_true, hrest, Bool.true_and]

private theorem leafSum_neg (tail m : Nat) (p test : RatPoly) (weight : List Nat → Q') :
    leafSum tail m p test (fun ds => -(weight ds)) ≈ -(leafSum tail m p test weight) :=
  Q'.eqv_trans _ _ _ (leafSum_congr tail m p test _ _ (fun ds _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.neg (.const 1)) (.var 0))
      (by decide) (fun _ => weight ds)))
    (Q'.eqv_trans _ _ _ (leafSum_smul tail m p test (-1) weight)
      (poly_identity_of_normal_eq (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => leafSum tail m p test weight)))

private theorem leafSum_sub (tail m : Nat) (p test : RatPoly) (a b : List Nat → Q') :
    leafSum tail m p test (fun ds => a ds-b ds) ≈
      leafSum tail m p test a-leafSum tail m p test b :=
  Q'.eqv_trans _ _ _ (leafSum_add tail m p test a (fun ds => -(b ds)))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (leafSum_neg tail m p test b))

private theorem sub_flip (a b c : Q') (h : a ≈ b-c) : c ≈ b-a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
    (by decide) (fun | 0 => b | _ => c)))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ h.symm))

private theorem attenuation_pair (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p test (productAttenuation w K) ≈
      kineticPair (tail+1) w K (List.range (tail+1)) test p :=
  Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p test _).symm
    ((productMap_modeFold tail w K p hp).symm test)

/-- Exact omitted operator identification at any supplied computed saturation
cutoff. The input tree, original cutoff K and arbitrary signed test are kept. -/
theorem pairOmitted_at_saturation (tail : Nat) (w : Q') (K M : Nat)
    (p test : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hM : pathMax tail (tail+1) p ≤ M) :
    pairOmitted tail w K p test ≈
      kineticPair (tail+1) w M (List.range (tail+1)) test p -
        kineticPair (tail+1) w K (List.range (tail+1)) test p := by
  have hweights (ds : List Nat) (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
      omittedDebt w K ds ≈ productAttenuation w M ds-productAttenuation w K ds := by
    have hs := productAttenuation_retained w M ds
    simp only [pathMax_retained tail (tail+1) p ds M hlen hpath hM, if_true] at hs
    exact Q'.eqv_trans _ _ _
      (sub_flip _ _ _ (productAttenuation_debt w K ds))
      (Q'.add_eqv_congr' hs.symm (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _
    (leafSum_pairing_congr tail (tail+1) p test test (omittedDebt w K)
      (fun ds => productAttenuation w M ds-productAttenuation w K ds)
      (fun ds hlen hpath => Q'.mul_eqv_congr_right _ _ _ (hweights ds hlen hpath)))
    (Q'.eqv_trans _ _ _ (leafSum_sub tail (tail+1) p test _ _)
      (Q'.add_eqv_congr' (attenuation_pair tail w M p test hp)
        (Q'.neg_eqv_congr _ _ (attenuation_pair tail w K p test hp))))

/-- Both independently computed trees are compared at ONE finite envelope. -/
theorem pairOmitted_symm (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairOmitted tail w K p test ≈ pairOmitted tail w K test p := by
  let M := max (pathMax tail (tail+1) p) (pathMax tail (tail+1) test)
  have hids : ∀ i, i ∈ List.range (tail+1) → i < tail+1 := fun i hi => List.mem_range.mp hi
  exact Q'.eqv_trans _ _ _ (pairOmitted_at_saturation tail w K M p test hp (Nat.le_max_left _ _))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (kineticPair_symm (tail+1) w M _ hids test p ht hp)
      (Q'.neg_eqv_congr _ _ (kineticPair_symm (tail+1) w K _ hids test p ht hp)))
      (pairOmitted_at_saturation tail w K M test p ht (Nat.le_max_right _ _)).symm)

theorem pairOmitted_test_congr (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    pairOmitted tail w K p left ≈ pairOmitted tail w K p right :=
  Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p left _).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (h.mul_right _))
      (leafSum_modeFold tail (tail+1) p right _))

theorem pairOmitted_test_add (tail : Nat) (w : Q') (K : Nat) (p f g : RatPoly) :
    pairOmitted tail w K p (polyAdd f g) ≈
      pairOmitted tail w K p f+pairOmitted tail w K p g := by
  have hs : H (tail+1) (polyMul (polyAdd f g)
      (modeFold tail (tail+1) p (omittedDebt w K))) ≈
      H (tail+1) (polyMul f (modeFold tail (tail+1) p (omittedDebt w K)))+
        H (tail+1) (polyMul g (modeFold tail (tail+1) p (omittedDebt w K))) := by
    rw [polyMul_add_left_exact]
    exact quaternionHaar_append _ _ _
  exact Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p (polyAdd f g) _).symm
    (Q'.eqv_trans _ _ _ hs (Q'.add_eqv_congr'
      (leafSum_modeFold tail (tail+1) p f _) (leafSum_modeFold tail (tail+1) p g _)))

theorem pairOmitted_test_smul (tail : Nat) (w : Q') (K : Nat) (c : Q') (p f : RatPoly) :
    pairOmitted tail w K p (polySmul c f) ≈ c*pairOmitted tail w K p f :=
  Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p (polySmul c f) _).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c f _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) c _)
        (Q'.mul_eqv_congr_left _ _ _ (leafSum_modeFold tail (tail+1) p f _))))

private theorem zero_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 0 polyOne) p) p :=
  ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl p)).trans
    (RatPolyCoeffEqv.zero_add p)

private theorem neg_add (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul (-1) p) p) (polySmul 0 polyOne) :=
  (RatPolyCoeffEqv.add_comm _ _).trans
    ((RatPolyCoeffEqv.add_neg_smul p).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)

/-- The ORIGINAL omitted form, not a supplied PSD interface or an OS carrier.
The existing generic form machinery is used only for finite algebra. -/
def omittedGNSData (tail : Nat) (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : GNSData where
  V := {p : RatPoly // SupportedQuaternionBlocks (tail+1) p}
  veq := fun p q => RatPolyCoeffEqv p.val q.val
  veq_refl := fun _ => RatPolyCoeffEqv.refl _
  veq_symm := fun h => h.symm
  veq_trans := fun h h' => h.trans h'
  zero := ⟨polySmul 0 polyOne, polySmul_supported (supported_one (tail+1)) 0⟩
  add := fun p q => ⟨polyAdd p.val q.val, supported_add p.property q.property⟩
  neg := fun p => ⟨polySmul (-1) p.val, polySmul_supported p.property (-1)⟩
  smul := fun c p => ⟨polySmul c p.val, polySmul_supported p.property c⟩
  add_congr := fun h h' => h.add h'
  neg_congr := fun h => h.smul (-1)
  smul_congr := fun c {_ _} h => h.smul c
  add_assoc := fun _ _ _ => RatPolyCoeffEqv.add_assoc _ _ _
  add_comm := fun _ _ => RatPolyCoeffEqv.add_comm _ _
  zero_add := fun p => zero_add p.val
  neg_add := fun p => neg_add p.val
  B := fun p q => pairOmitted tail w K q.val p.val
  B_congr_left := fun q h => pairOmitted_test_congr tail w K q.val h
  B_add_left := fun p q r => pairOmitted_test_add tail w K r.val p.val q.val
  B_smul_left := fun c p q => pairOmitted_test_smul tail w K c q.val p.val
  B_symm := fun p q => pairOmitted_symm tail w K q.val p.val q.property p.property
  self_nonneg := fun p => pairOmitted_diagonal_nonnegative tail hw K p.val p.property

theorem pairOmitted_cauchySchwarz (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (p test : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairOmitted tail w K p test*pairOmitted tail w K p test ≤
      pairOmitted tail w K p p*pairOmitted tail w K test test :=
  Q'.le_trans' _ _ _ ((omittedGNSData tail w hw0 K).cauchy_schwarz ⟨test,ht⟩ ⟨p,hp⟩)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- Sharp mixed Haar-norm cap; the cutoff coefficient is squared because the
pairing is squared. No roots, source positivity or degree guard are assumed. -/
theorem pairOmitted_square_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairOmitted tail w K p test*pairOmitted tail w K p test ≤
      (omittedRate w K*omittedRate w K)*
        (H (tail+1) (polyMul p p)*H (tail+1) (polyMul test test)) := by
  have hpp := pairOmitted_diagonal_nonnegative tail hw0 K p hp
  have htt := pairOmitted_diagonal_nonnegative tail hw0 K test ht
  have hup := pairOmitted_diagonal_le_haar tail hw0 hw1 K p hp
  have hut := pairOmitted_diagonal_le_haar tail hw0 hw1 K test ht
  have hprod := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hup htt)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hut (Q'.le_trans' _ _ _ hpp hup))
  exact Q'.le_trans' _ _ _ (pairOmitted_cauchySchwarz tail hw0 K p test hp ht)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => omittedRate w K
                       | 1 => H (tail+1) (polyMul p p)
                       | _ => H (tail+1) (polyMul test test)))))

/-- The sign needed by the source energy is bounded directly, not by an
absolute leaf budget. Sharp Cauchy--Schwarz remains available separately. -/
theorem neg_pairOmitted_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    -(pairOmitted tail w K p test) ≤
      HalfPow.half*(omittedRate w K*(H (tail+1) (polyMul p p)+
        H (tail+1) (polyMul test test))) := by
  let D := omittedGNSData tail w hw0 K
  let a : D.V := ⟨test,ht⟩
  let b : D.V := ⟨p,hp⟩
  let v := D.add (D.smul 1 a) (D.smul 1 b)
  have hpos := Q'.mul_nonneg _ _ HalfPow.half_nonneg (D.self_nonneg v)
  have hexp := Q'.mul_eqv_congr_left HalfPow.half _ _ (D.diag_expand 1 1 a b)
  have hreg : HalfPow.half*D.B v v ≈
      HalfPow.half*(D.B b b+D.B a a) + (HalfPow.half*2)*(D.B a b) :=
    Q'.eqv_trans _ _ _ hexp (poly_identity_of_normal_eq
      (.mul (.var 3)
        (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
                    (.mul (.const 1) (.mul (.const 1) (.var 1))))
              (.add (.mul (.const 1) (.mul (.const 1) (.var 1)))
                    (.mul (.const 1) (.mul (.const 1) (.var 2))))))
      (.add (.mul (.var 3) (.add (.var 2) (.var 0)))
        (.mul (.mul (.var 3) (.const 2)) (.var 1)))
      (by decide) (fun | 0 => D.B a a | 1 => D.B a b
                       | 2 => D.B b b | _ => HalfPow.half))
  have hcross : (HalfPow.half*2)*(D.B a b) ≈ -(-(D.B a b)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : HalfPow.half*2 ≈ (1 : Q')))
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.neg_neg_eqv _).symm)
  have hpin := Q'.eqv_trans _ _ _ hreg (Q'.add_eqv_congr' (Q'.eqv_refl _) hcross)
  have hyoung : -(pairOmitted tail w K p test) ≤
      HalfPow.half*(pairOmitted tail w K p p+pairOmitted tail w K test test) :=
    OSReconstructionProgress.q_le_of_sub_nonneg
      (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hpin))
  have hnorm := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add (pairOmitted_diagonal_le_haar tail hw0 hw1 K p hp)
      (pairOmitted_diagonal_le_haar tail hw0 hw1 K test ht)) HalfPow.half_nonneg
  exact Q'.le_trans' _ _ _ hyoung (Q'.le_trans' _ _ _ hnorm
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv _ _ _).symm)))

/-- COMPLETE cubic budgets retained; BOTH omitted terms now use actual Haar
squares. This is not an OWN-variance-relative or changing-family estimate. -/
def sourceHaarErrorBudget (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly) : Q' :=
  ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)) *
    (pairCubicBudget tail a (polyMul a (polyMul f f)) +
      pairCubicBudget tail (polyMul a f) (polyMul a f)) +
    omittedRate w K *
      (HalfPow.half*(H (tail+1) (polyMul a a)+
        H (tail+1) (polyMul (polyMul a (polyMul f f)) (polyMul a (polyMul f f))))+
        H (tail+1) (polyMul (polyMul a f) (polyMul a f)))

private theorem neg_lower_le {a b : Q'} (h : -b ≤ a) : -a ≤ b :=
  Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (Q'.le_of_eqv (Q'.neg_neg_eqv b))

/-- An actual error estimate, not comparison with the old mixed absolute
budget, which can be larger. The original signed terms are unchanged. -/
theorem sourceError_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceCubic tail w a f-sourceOmitted tail w K a f ≤
      sourceHaarErrorBudget tail w K a f := by
  have hc := Q'.add_le_add (pairCubic_bounds tail hw0 hw1 a (polyMul a (polyMul f f))).2
    (neg_lower_le (pairCubic_bounds tail hw0 hw1 (polyMul a f) (polyMul a f)).1)
  have ho := Q'.add_le_add
    (neg_pairOmitted_le_haar tail hw0 hw1 K a (polyMul a (polyMul f f)) ha
      (supported_polyMul ha (supported_polyMul hf hf)))
    (pairOmitted_diagonal_le_haar tail hw0 hw1 K (polyMul a f) (supported_polyMul ha hf))
  have hleft : sourceCubic tail w a f-sourceOmitted tail w K a f ≈
      sourceCubic tail w a f+
        (-(pairOmitted tail w K a (polyMul a (polyMul f f)))+
          pairOmitted tail w K (polyMul a f) (polyMul a f)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.add (.neg (.var 1)) (.var 2))) (by decide)
      (fun | 0 => sourceCubic tail w a f
           | 1 => pairOmitted tail w K a (polyMul a (polyMul f f))
           | _ => pairOmitted tail w K (polyMul a f) (polyMul a f))
  have hsum := Q'.add_le_add hc ho
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.add (.mul (.var 3) (.mul (.var 4) (.add (.var 5) (.var 6))))
          (.mul (.var 4) (.var 7))))
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 4) (.add (.mul (.var 3) (.add (.var 5) (.var 6))) (.var 7))))
      (by decide) (fun
        | 0 => (((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)
        | 1 => pairCubicBudget tail a (polyMul a (polyMul f f))
        | 2 => pairCubicBudget tail (polyMul a f) (polyMul a f)
        | 3 => HalfPow.half
        | 4 => omittedRate w K
        | 5 => H (tail+1) (polyMul a a)
        | 6 => H (tail+1) (polyMul (polyMul a (polyMul f f)) (polyMul a (polyMul f f)))
        | _ => H (tail+1) (polyMul (polyMul a f) (polyMul a f))))))

/-- Actual full source energy with no absolute omitted-mode budget. The
second-order signed coefficient and both cubic costs remain unchanged. -/
theorem sourceEnergy_le_secondOrder_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
          (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
          sourceHaarErrorBudget tail w K a f) := by
  have hgroup :
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
          sourceCubic tail w a f-sourceOmitted tail w K a f ≈
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
          (sourceCubic tail w a f-sourceOmitted tail w K a f) := Q'.add_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sourceEnergy_secondOrder tail w K a f ha hf))
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv hgroup)
      (Q'.add_le_add_left _ _ _ (sourceError_le_haar tail hw0 hw1 K a f ha hf))))

end YMGap.Continuum.SU2QuaternionCyclicOmittedOperator

#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pathMax
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pathMax_retained
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_at_saturation
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_symm
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_test_congr
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_test_add
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_test_smul
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.omittedGNSData
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_cauchySchwarz
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.pairOmitted_square_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.neg_pairOmitted_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.sourceHaarErrorBudget
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.sourceError_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedOperator.sourceEnergy_le_secondOrder_haar
