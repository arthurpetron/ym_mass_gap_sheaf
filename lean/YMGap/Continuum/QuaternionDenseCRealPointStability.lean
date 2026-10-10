/-
Quantitative stability of the ACTUAL sampled dense-data extension.
Eventual input-value distance passes to two supplied row images with two
shrinking sampling errors. This produces source-row continuity, stability
under changing dense input, and the image's own sound bound. Distinct inner
rates and continuity radii are retained; no early-approximation bound,
representative choice, monotonicity, or integral identity is assumed.
Consumer: admissibility and limit comparison of completed translations.
Completed-multiplier Haar invariance, full Haar/J04 and Clay remain open.
-/

import YMGap.Continuum.QuaternionDenseCRealPointExtension

namespace YMGap.Continuum.QuaternionDenseCRealPointStability

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.QuaternionDenseCRealPointExtension

/-- Explicit outer cutoff paying two shrinking sampling errors after K. -/
def rowDistanceRate (K : Nat) (epsilon : Q') : Nat :=
  max K (HalfPow.half * epsilon).den

private theorem sample_budget (eta epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : (HalfPow.half * epsilon).den ≤ n) :
    (eta + Q'.invSucc n) + Q'.invSucc n ≤ eta + epsilon := by
  have hs : Q'.invSucc n ≤ HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le _ (Q'.mul_pos (by decide) he))
  have ht : Q'.invSucc n + Q'.invSucc n ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hs hs)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv eta (Q'.invSucc n) (Q'.invSucc n)))
    (Q'.add_le_add_left _ _ _ ht)

variable (F : UnitNorm → CReal) (RF : ∀ q, InnerRegularity (F q))
variable (rhoF : Q' → Q')
variable (positiveF : ∀ e, (0 : Q') < e → (0 : Q') < rhoF e)
variable (modF : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoF e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)
variable (G : UnitNorm → CReal) (RG : ∀ q, InnerRegularity (G q))
variable (rhoG : Q' → Q')
variable (positiveG : ∀ e, (0 : Q') < e → (0 : Q') < rhoG e)
variable (modG : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rhoG e →
    leRat (CReal.abs (CReal.add (G q) (CReal.neg (G x)))) e)

include positiveF modF positiveG modG in
/-- Literal output stages retain the input error and BOTH sample errors.
The source rows and dense input presentations may be different. -/
theorem rowImage_distance_stage (X Y : CauchyPoint) (eta : Q') (K : Nat)
    (hD : ∀ n, K ≤ n →
      leRat (CReal.abs (CReal.add (F (X.seq n))
        (CReal.neg (G (Y.seq n))))) eta)
    (n : Nat) (hn : K ≤ n) :
    Q'.abs ((rowImage F RF rhoF positiveF modF X).approx n +
      -((rowImage G RG rhoG positiveG modG Y).approx n)) ≤
        (eta + Q'.invSucc n) + Q'.invSucc n :=
  sample_difference_le_asymmetric (F (X.seq n)) (G (Y.seq n))
    (RF (X.seq n)) (RG (Y.seq n)) eta (Q'.invSucc n) (Q'.invSucc n)
    (hD n hn) (Q'.invSucc_pos n) (Q'.invSucc_pos n)

/-- Sound output distance, paid at the explicit rowDistanceRate.
No input bound or monotonicity of any supplied rate is required. -/
theorem rowImage_distance (X Y : CauchyPoint) (eta : Q') (K : Nat)
    (hD : ∀ n, K ≤ n →
      leRat (CReal.abs (CReal.add (F (X.seq n))
        (CReal.neg (G (Y.seq n))))) eta) :
    leRat (CReal.abs (CReal.add
      (rowImage F RF rhoF positiveF modF X)
      (CReal.neg (rowImage G RG rhoG positiveG modG Y)))) eta := by
  intro epsilon he
  refine ⟨rowDistanceRate K epsilon, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (rowImage_distance_stage F RF rhoF positiveF modF G RG rhoG positiveG modG
      X Y eta K hD n (Nat.le_trans (Nat.le_max_left _ _) hn))
    (sample_budget eta epsilon he n (Nat.le_trans (Nat.le_max_right _ _) hn))

/-- The supplied continuity radius gives quantitative continuity on two
actual completion rows. eta must be positive, exactly as in modF. -/
theorem rowImage_source_distance (X Y : CauchyPoint) (eta : Q')
    (heta : (0 : Q') < eta) (K : Nat)
    (hsource : ∀ n, K ≤ n → distSq (X.seq n).val (Y.seq n).val ≤ rhoF eta) :
    leRat (CReal.abs (CReal.add
      (rowImage F RF rhoF positiveF modF X)
      (CReal.neg (rowImage F RF rhoF positiveF modF Y)))) eta :=
  rowImage_distance F RF rhoF positiveF modF F RF rhoF positiveF modF
    X Y eta K (fun n hn => modF eta heta _ _ (hsource n hn))

/-- Uniform dense input-value distance survives on the same supplied row.
eta may be zero; no relation between the two radii or inner rates is needed. -/
theorem rowImage_input_distance (X : CauchyPoint) (eta : Q')
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) eta) :
    leRat (CReal.abs (CReal.add
      (rowImage F RF rhoF positiveF modF X)
      (CReal.neg (rowImage G RG rhoG positiveG modG X)))) eta :=
  rowImage_distance F RF rhoF positiveF modF G RG rhoG positiveG modG
    X X eta 0 (fun n _ => hD (X.seq n))

private theorem distance_order_pair {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leEv a (CReal.add b (CReal.ofQ' eta)) ∧
      leEv b (CReal.add a (CReal.ofQ' eta)) := by
  have forward (u v : CReal)
      (hu : leRat (CReal.abs (CReal.add u (CReal.neg v))) eta) :
      leEv u (CReal.add v (CReal.ofQ' eta)) := by
    intro e he
    obtain ⟨K, hK⟩ := hu e he
    refine ⟨K, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le (hK n hn))
      (Q'.ge_of_eqv (Q'.add_assoc_eqv (v.approx n) eta e))
  refine ⟨forward a b h, forward b a ?_⟩
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

/-- The actual RC-valued extensions preserve dense distance on EVERY Point;
quotient induction does not select a CReal representative. -/
theorem pointExtension_input_distance (eta : Q')
    (hD : ∀ q, leRat (CReal.abs (CReal.add (F q) (CReal.neg (G q)))) eta)
    (x : Point) :
    RCle (pointExtension F RF rhoF positiveF modF x)
      (RCadd (pointExtension G RG rhoG positiveG modG x)
        (Quotient.mk crealSetoid (CReal.ofQ' eta))) ∧
    RCle (pointExtension G RG rhoG positiveG modG x)
      (RCadd (pointExtension F RF rhoF positiveF modF x)
        (Quotient.mk crealSetoid (CReal.ofQ' eta))) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [pointExtension_mk, pointExtension_mk]
  exact distance_order_pair
    (rowImage_input_distance F RF rhoF positiveF modF G RG rhoG positiveG modG
      X eta hD)

include positiveF modF in
/-- Sound input bounds pay one sampling tolerance at each actual stage. -/
theorem rowImage_bound_stage (M : Q')
    (hM : ∀ q, leRat (CReal.abs (F q)) M) (X : CauchyPoint) (n : Nat) :
    Q'.abs ((rowImage F RF rhoF positiveF modF X).approx n) ≤ M + Q'.invSucc n :=
  sample_abs_le (F (X.seq n)) (RF (X.seq n)) M (Q'.invSucc n)
    (hM (X.seq n)) (Q'.invSucc_pos n)

/-- The actual completion-row image has the SAME sound bound M, with the
explicit outer cutoff epsilon.den; no raw early-row bound is used. -/
theorem rowImage_bound (M : Q') (hM : ∀ q, leRat (CReal.abs (F q)) M)
    (X : CauchyPoint) :
    leRat (CReal.abs (rowImage F RF rhoF positiveF modF X)) M := by
  intro epsilon he
  refine ⟨epsilon.den, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (rowImage_bound_stage F RF rhoF positiveF modF M hM X n)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le epsilon he)))

#print axioms rowDistanceRate
#print axioms rowImage_distance_stage
#print axioms rowImage_distance
#print axioms rowImage_source_distance
#print axioms rowImage_input_distance
#print axioms pointExtension_input_distance
#print axioms rowImage_bound_stage
#print axioms rowImage_bound

end YMGap.Continuum.QuaternionDenseCRealPointStability
