/-
# Actual Bochner margin as finite nome rows

The rows use all six ORIGINAL head rotation fields. Their evaluation agrees
at coefficient strength with the DEFINED Gamma2-Gamma, not with a surrogate
Hessian. The existing Bochner certificate and actual conditional saturation
then construct positivity of this fixed finite input. Shared output variables
and spectators are retained. No derivative sign, variance inequality, uniform
positive prefix up to nome one, or changing-family bound is assumed or proved.
-/

import YMGap.Continuum.RatPolyNomeRowCutoff
import YMGap.Continuum.SU2QuaternionAngularBochner
import YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation

namespace YMGap.Continuum.SU2QuaternionBochnerNomeRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionAngularBochner
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.RatPolyNomeRowCutoff
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatPositiveSaturation

private def sixRows (f : Nat → Nat → Rows) : Rows :=
  f 0 1 ++ (f 0 2 ++ (f 0 3 ++ (f 1 2 ++ (f 1 3 ++ f 2 3))))

def laplacianNomeRows (A : Rows) : Rows :=
  sixRows fun i j => mapRows (angularDerivative i j) (mapRows (angularDerivative i j) A)

def mixedNomeRows (A B : Rows) : Rows :=
  sixRows fun i j => mulRows (mapRows (angularDerivative i j) A)
    (mapRows (angularDerivative i j) B)

def energyNomeRows (A : Rows) : Rows := mixedNomeRows A A

def gamma2Rows (A : Rows) : Rows :=
  mapRows (polySmul HalfPow.half) (laplacianNomeRows (energyNomeRows A)) ++
    mapRows polyNeg (mixedNomeRows A (laplacianNomeRows A))

def bochnerMarginRows (A : Rows) : Rows :=
  gamma2Rows A ++ mapRows polyNeg (energyNomeRows A)

private theorem eval_sixRows (f : Nat → Nat → Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (sixRows f) r) (six fun i j => evalRows (f i j) r) :=
  (evalRows_append _ _ r).trans ((RatPolyCoeffEqv.refl _).add
    ((evalRows_append _ _ r).trans ((RatPolyCoeffEqv.refl _).add
      ((evalRows_append _ _ r).trans ((RatPolyCoeffEqv.refl _).add
        ((evalRows_append _ _ r).trans ((RatPolyCoeffEqv.refl _).add
          (evalRows_append _ _ r))))))))

private theorem six_coeff {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) :=
  (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))))))

private theorem laplacian_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (angularLaplacian p) (angularLaplacian q) :=
  six_coeff fun i j _ _ => angularDerivative_congr i j (angularDerivative_congr i j h)

private theorem mixed_coeff {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    RatPolyCoeffEqv (mixedGamma p q) (mixedGamma p' q') :=
  six_coeff fun i j _ _ => (angularDerivative_congr i j hp).mul
    (angularDerivative_congr i j hq)

theorem evalRows_laplacianNomeRows (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (laplacianNomeRows A) r)
      (angularLaplacian (evalRows A r)) :=
  (eval_sixRows _ r).trans (six_coeff fun i j _ _ =>
    (evalRows_angularDerivative i j _ r).trans
      (angularDerivative_congr i j (evalRows_angularDerivative i j A r)))

theorem evalRows_mixedNomeRows (A B : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mixedNomeRows A B) r)
      (mixedGamma (evalRows A r) (evalRows B r)) :=
  (eval_sixRows _ r).trans (six_coeff fun i j _ _ =>
    (evalRows_mul _ _ r).trans
      ((evalRows_angularDerivative i j A r).mul (evalRows_angularDerivative i j B r)))

private theorem eval_scaleRows (c : Q') (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mapRows (polySmul c) A) r)
      (polySmul c (evalRows A r)) := by
  induction A with
  | nil => exact (RatPolyCoeffEqv.smul_zero c).symm
  | cons a A ih =>
      have hc : RatPolyCoeffEqv
          (polySmul (QPoly.eval a.1 r) (polySmul c a.2))
          (polySmul c (polySmul (QPoly.eval a.1 r) a.2)) :=
        (RatPolyCoeffEqv.smul_assoc _ _ _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv _ _) _).trans
            (RatPolyCoeffEqv.smul_assoc _ _ _).symm)
      exact (hc.add ih).trans (RatPolyCoeffEqv.smul_add c _ _).symm

private theorem eval_negRows (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (mapRows polyNeg A) r) (polyNeg (evalRows A r)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      have hc : RatPolyCoeffEqv
          (polySmul (QPoly.eval a.1 r) (polyNeg a.2))
          (polyNeg (polySmul (QPoly.eval a.1 r) a.2)) := by
        intro weight
        induction a.2 with
        | nil => exact Q'.eqv_refl _
        | cons term p hp =>
            exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_right _ _ (weight term.1)
                (Q'.mul_neg_eqv (QPoly.eval a.1 r) term.2)) hp
      exact (hc.add ih).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.neg (.var 0)) (.neg (.var 1))) (.neg (.add (.var 0) (.var 1)))
          (by decide) (fun | 0 => polySmul (QPoly.eval a.1 r) a.2 | _ => evalRows A r))

theorem evalRows_gamma2Rows (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (gamma2Rows A) r) (gamma2 (evalRows A r)) := by
  have he : RatPolyCoeffEqv (evalRows (energyNomeRows A) r) (angularSquare (evalRows A r)) :=
    evalRows_mixedNomeRows A A r
  exact (evalRows_append _ _ r).trans
    (((eval_scaleRows _ _ r).trans
      (((evalRows_laplacianNomeRows _ r).trans (laplacian_coeff he)).smul HalfPow.half)).add
      ((eval_negRows _ r).trans
        (RatPolyCoeffEqv.neg ((evalRows_mixedNomeRows _ _ r).trans
          (mixed_coeff (RatPolyCoeffEqv.refl _) (evalRows_laplacianNomeRows A r))))))

theorem evalRows_bochnerMarginRows (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (bochnerMarginRows A) r)
      (polyAdd (gamma2 (evalRows A r)) (polyNeg (angularSquare (evalRows A r)))) :=
  (evalRows_append _ _ r).trans ((evalRows_gamma2Rows A r).add
    ((eval_negRows _ r).trans (RatPolyCoeffEqv.neg (evalRows_mixedNomeRows A A r))))

private abbrev RowSupported (blocks : Nat) (A : Rows) : Prop :=
  ∀ row, row ∈ A → SupportedQuaternionBlocks blocks row.2

private theorem append_support {blocks : Nat} {A B : Rows}
    (hA : RowSupported blocks A) (hB : RowSupported blocks B) : RowSupported blocks (A++B) := by
  intro row hrow
  rcases List.mem_append.mp hrow with h | h
  · exact hA row h
  · exact hB row h

private theorem map_support {blocks : Nat} {A : Rows} (f : RatPoly → RatPoly)
    (hA : RowSupported blocks A)
    (hf : ∀ p, SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks (f p)) :
    RowSupported blocks (mapRows f A) := by
  intro row hrow
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hrow
  exact hf a.2 (hA a ha)

private theorem mul_support {blocks : Nat} {A B : Rows}
    (hA : RowSupported blocks A) (hB : RowSupported blocks B) : RowSupported blocks (mulRows A B) := by
  intro row hrow
  obtain ⟨a, ha, hrow⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
  exact supported_polyMul (hA a ha) (hB b hb)

private theorem six_support {blocks : Nat} (f : Nat → Nat → Rows)
    (hf : ∀ i j, i<4 → j<4 → RowSupported blocks (f i j)) : RowSupported blocks (sixRows f) :=
  append_support (hf 0 1 (by decide) (by decide))
    (append_support (hf 0 2 (by decide) (by decide))
      (append_support (hf 0 3 (by decide) (by decide))
        (append_support (hf 1 2 (by decide) (by decide))
          (append_support (hf 1 3 (by decide) (by decide)) (hf 2 3 (by decide) (by decide))))))

private theorem lap_support {blocks : Nat} (hb : 0<blocks) {A : Rows}
    (hA : RowSupported blocks A) : RowSupported blocks (laplacianNomeRows A) :=
  six_support _ fun i j hi hj => map_support _
    (map_support _ hA (fun _ hp => angularDerivative_supported hb hi hj hp))
    (fun _ hp => angularDerivative_supported hb hi hj hp)

private theorem mixed_support {blocks : Nat} (hb : 0<blocks) {A B : Rows}
    (hA : RowSupported blocks A) (hB : RowSupported blocks B) : RowSupported blocks (mixedNomeRows A B) :=
  six_support _ fun i j hi hj => mul_support
    (map_support _ hA (fun _ hp => angularDerivative_supported hb hi hj hp))
    (map_support _ hB (fun _ hp => angularDerivative_supported hb hi hj hp))

private theorem neg_support {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term hterm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hterm
  exact hp a ha

/-- Support of every fixed margin row, before choosing any nome. -/
theorem bochnerMarginRows_supported {blocks : Nat} (hb : 0<blocks) (A : Rows)
    (hA : ∀ row, row ∈ A → SupportedQuaternionBlocks blocks row.2) :
    ∀ row, row ∈ bochnerMarginRows A → SupportedQuaternionBlocks blocks row.2 :=
  append_support
    (append_support
      (map_support _ (lap_support hb (mixed_support hb hA hA)) (fun _ hp => polySmul_supported hp _))
      (map_support _ (mixed_support hb hA (lap_support hb hA)) (fun _ hp => neg_support hp)))
    (map_support _ (mixed_support hb hA hA) (fun _ hp => neg_support hp))

/-- Constructed Bochner positivity transported through coefficient equality,
not a generic retained-output diagonal pullback. -/
def bochnerMarginRows_certificate {blocks : Nat} (hb : 0<blocks) (A : Rows)
    (hA : ∀ row, row ∈ A → SupportedQuaternionBlocks blocks row.2) (r : Q') :
    Certificate blocks (evalRows (bochnerMarginRows A) r) :=
  .ofCoeff (evalRows_bochnerMarginRows A r)
    (bochner_curvature_certificate hb (evalRows_supported A hA r))

/-- Concrete positivity at any strict auxiliary nome, with the fixed row
cutoff computed once and the larger positive prefix supplied internally. -/
def conditional_bochnerMarginRows_certificate (tail : Nat) (ht : 0<tail)
    (u : Q') (hu0 : (0:Q')<u) (hu1 : u<(1:Q')) (K : Nat) (A : Rows)
    (hA : ∀ row, row ∈ A → SupportedQuaternionBlocks (tail+1) row.2) (r : Q')
    (hK : rowCutoff (tail+1) (bochnerMarginRows A) ≤ K) :
    Certificate tail (conditionalHeat u K (evalRows (bochnerMarginRows A) r)) := by
  have hb : 0<tail+1 := Nat.zero_lt_succ tail
  have hmode : SU2QuaternionPolynomialHarmonicExpansion.modeCutoff (tail+1)
      (evalRows (bochnerMarginRows A) r) ≤ K := by
    rw [rowCutoff_spec (tail+1) hb]
    exact hK
  exact conditionalHeat_saturated_certificate tail ht u hu0 hu1 K
    (evalRows_supported _ (bochnerMarginRows_supported hb A hA) r) hmode
    (bochnerMarginRows_certificate hb A hA r)

end YMGap.Continuum.SU2QuaternionBochnerNomeRows

#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.laplacianNomeRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.mixedNomeRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.energyNomeRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.gamma2Rows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.bochnerMarginRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.evalRows_laplacianNomeRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.evalRows_mixedNomeRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.evalRows_gamma2Rows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.evalRows_bochnerMarginRows
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.bochnerMarginRows_supported
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.bochnerMarginRows_certificate
#print axioms YMGap.Continuum.SU2QuaternionBochnerNomeRows.conditional_bochnerMarginRows_certificate
