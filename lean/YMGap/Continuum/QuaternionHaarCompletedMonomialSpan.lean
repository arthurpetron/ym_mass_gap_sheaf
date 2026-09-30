/-
# Completed pairing vanishing from a finite monomial test list

For the same certified weighted Haar form, vanishing of a completed vector's
pairing against each unit monomial in a finite list implies vanishing against
any supported dense polynomial whose literal terms are covered by that list.
The proof uses the actual completed bilinear/scalar laws; it chooses no
representative and inverts no Gram matrix.
-/

import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.QuaternionHaarWeightedMonomialSpan

namespace YMGap.Continuum.QuaternionHaarCompletedMonomialSpan

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem polySmul_sub_equiv (s : Q') (a b : RatPoly) :
    RatPolyCoeffEqv
      (polySmul s (polyAdd a (polySmul (-1) b)))
      (polyAdd (polySmul s a) (polySmul (-1) (polySmul s b))) := by
  have hdouble : RatPolyCoeffEqv
      (polySmul s (polySmul (-1) b))
      (polySmul (-1) (polySmul s b)) := by
    exact (RatPolyCoeffEqv.smul_assoc s (-1) b).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv s (-1)) b).trans
        (RatPolyCoeffEqv.smul_assoc (-1) s b).symm)
  exact (RatPolyCoeffEqv.smul_add s a (polySmul (-1) b)).trans
    ((RatPolyCoeffEqv.refl (polySmul s a)).add hdouble)

/-- The weighted polynomial GNS datum has its honest rational completion
scalar action; its underlying `GNSData` is definitionally `weightedGNSData`. -/
def weightedSmulGNSData (blocks : Nat) (weight : RatPoly)
    (H : Certificate blocks weight) : SmulGNSData where
  toGNSData := weightedGNSData blocks weight H
  smul_sub := by
    intro s a b
    change RatPolyCoeffEqv
      (polySmul s (polyAdd a.val (polySmul (-1) b.val)))
      (polyAdd (polySmul s a.val) (polySmul (-1) (polySmul s b.val)))
    exact polySmul_sub_equiv s a.val b.val

private theorem rc_add_zero_zero : RCadd RCzero RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    QPoly.q_zero_add_eqv (CReal.czero.approx n)))

private theorem rc_scale_zero (c : Q') : RCscale c RCzero = RCzero := by
  exact RCscale_RCzero c

private theorem singleton_coefficient (monomial : List Nat) (coefficient : Q') :
    RatPolyCoeffEqv [(monomial, coefficient)]
      (polySmul coefficient [(monomial, 1)]) := by
  intro testWeight
  change coefficient * testWeight monomial + 0 ≈
    (coefficient * 1) * testWeight monomial + 0
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv coefficient)))

/-- Pairing against a finite-moment-null test list annihilates every
supported dense polynomial whose literal terms occur in that list. -/
theorem completedPair_zero_of_test_list
    (blocks : Nat) (weight : RatPoly) (H : Certificate blocks weight)
    (x : GNSCompletionSpace (weightedGNSData blocks weight H))
    (q : RatPoly) (hq : SupportedQuaternionBlocks blocks q)
    (monomials : List (List Nat))
    (hmonomials : ∀ m, m ∈ monomials →
      SupportedQuaternionBlocks blocks [(m, 1)])
    (hcover : ∀ term, term ∈ q → term.1 ∈ monomials)
    (hzero : ∀ m (hm : m ∈ monomials),
      (weightedGNSData blocks weight H).cinnerCompl x
        (embedV (weightedGNSData blocks weight H) ⟨[(m, 1)], hmonomials m hm⟩)
        = RCzero) :
    (weightedGNSData blocks weight H).cinnerCompl x
      (embedV (weightedGNSData blocks weight H) ⟨q, hq⟩) = RCzero := by
  let S := weightedSmulGNSData blocks weight H
  let D := weightedGNSData blocks weight H
  suffices hmain : ∀ q : RatPoly, ∀ hq : SupportedQuaternionBlocks blocks q,
      (∀ term, term ∈ q → term.1 ∈ monomials) →
      D.cinnerCompl x (embedV D ⟨q, hq⟩) = RCzero from hmain q hq hcover
  intro q
  induction q with
  | nil =>
      intro hq _
      have hv : D.veq (D.zero) ⟨[], hq⟩ := by
        exact RatPolyCoeffEqv.zero_smul polyOne
      have he : embedV D ⟨[], hq⟩ = embedV D D.zero :=
        (Quotient.sound (embed_null_of_rad D (rad_of_veq D hv))).symm
      rw [he, D.cinnerCompl_embedZero_right]
  | cons term rest ih =>
      intro hq hcover
      have hheadSupported : SupportedQuaternionBlocks blocks [term] := by
        intro t ht
        have ht' : t = term := List.mem_singleton.mp ht
        subst t
        exact hq term List.mem_cons_self
      have htailSupported : SupportedQuaternionBlocks blocks rest := by
        intro t ht
        exact hq t (List.mem_cons_of_mem term ht)
      have htailCover : ∀ t, t ∈ rest → t.1 ∈ monomials := by
        intro t ht
        exact hcover t (List.mem_cons_of_mem term ht)
      have htail := ih htailSupported htailCover
      have hunitSupported : SupportedQuaternionBlocks blocks [(term.1, 1)] :=
        hmonomials term.1 (hcover term List.mem_cons_self)
      let unit : D.V := ⟨[(term.1, 1)], hunitSupported⟩
      have hhead : D.cinnerCompl x (embedV D ⟨[term], hheadSupported⟩) = RCzero := by
        have he : embedV D ⟨[term], hheadSupported⟩ =
            S.cSmul term.2 (embedV D unit) := by
          calc
            embedV D ⟨[term], hheadSupported⟩ =
                embedV D (D.smul term.2 unit) :=
              Quotient.sound (embed_null_of_rad D
                (rad_of_veq D (singleton_coefficient term.1 term.2)))
            _ = S.cSmul term.2 (embedV D unit) := (S.cSmul_embed term.2 unit).symm
        have hs : D.cinnerCompl x (S.cSmul term.2 (embedV D unit)) =
            RCscale term.2 (D.cinnerCompl x (embedV D unit)) :=
          S.cinnerCompl_cSmul_right term.2 x (embedV D unit)
        rw [he, hs, hzero term.1 (hcover term List.mem_cons_self), rc_scale_zero]
      have hdecomp : D.cAdd (embedV D ⟨[term], hheadSupported⟩)
          (embedV D ⟨rest, htailSupported⟩) = embedV D ⟨term :: rest, hq⟩ := by
        rw [D.cAdd_embed]
        rfl
      rw [← hdecomp, D.cinnerCompl_cAdd_right, hhead, htail, rc_add_zero_zero]

#print axioms weightedSmulGNSData
#print axioms completedPair_zero_of_test_list

end YMGap.Continuum.QuaternionHaarCompletedMonomialSpan
