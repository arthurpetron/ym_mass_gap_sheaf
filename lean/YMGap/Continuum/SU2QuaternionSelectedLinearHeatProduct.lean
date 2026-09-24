/-
# Selected-block heat transmission for finite linear forms

Finite coordinate-linear forms at an arbitrary original source block are
transported to a distinct target block.  Their exact quadratic trace channel
is reassembled as the existing coefficient Gram polynomial.  Every coefficient
and the final spectator remain on the same carrier; only source-block degree
zero is required.
-/

import YMGap.Continuum.SU2QuaternionSelectedPairQuadraticHeat

namespace YMGap.Continuum.SU2QuaternionSelectedLinearHeatProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
  (coordinateMoment gramRow gram)
open YMGap.Continuum.SU2QuaternionSelectedPairQuadraticHeat
  (coordinatePair_selected_transmission)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

/-- A finite coordinate-linear form placed at an arbitrary quaternion block. -/
def linearAt (block : Nat) : List (Fin 4 × RatPoly) → RatPoly
  | [] => polyZero
  | (i,p)::xs => polyAdd (polyMul (polyVar (4*block+i.val)) p) (linearAt block xs)

private def pair (blocks : Nat) (p r : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul p r)

private def heatPair (blocks a b : Nat) (w : Q') (K : Nat) (p r : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul (polyMul (heatAt a b w K) p) r)

private theorem pair_congr (blocks : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) (r : RatPoly) : pair blocks p r ≈ pair blocks q r :=
  haar_of_coeff (h.mul_right r)

private theorem pair_add (blocks : Nat) (p q r : RatPoly) :
    pair blocks (polyAdd p q) r ≈ pair blocks p r + pair blocks q r := by
  unfold pair
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem pair_smul (blocks : Nat) (c : Q') (p r : RatPoly) :
    pair blocks (polySmul c p) r ≈ c * pair blocks p r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul blocks c (polyMul p r))

private theorem heat_congr (blocks a b : Nat) (w : Q') (K : Nat)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) (r : RatPoly) :
    heatPair blocks a b w K p r ≈ heatPair blocks a b w K q r :=
  haar_of_coeff ((h.mul_left (heatAt a b w K)).mul_right r)

private theorem heat_add (blocks a b : Nat) (w : Q') (K : Nat)
    (p q r : RatPoly) :
    heatPair blocks a b w K (polyAdd p q) r ≈
      heatPair blocks a b w K p r + heatPair blocks a b w K q r :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff
      ((RatPolyCoeffEqv.mul_add_right (heatAt a b w K) p q).mul_right r))
    (pair_add blocks _ _ r)

private theorem heat_zero (blocks a b : Nat) (w : Q') (K : Nat) (r : RatPoly) :
    heatPair blocks a b w K polyZero r ≈ 0 :=
  haar_of_coeff
    ((RatPolyCoeffEqv.mul_zero_right (heatAt a b w K)).mul_right r)

private theorem atom_input (k xi p xj q r : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul k (polyMul (polyMul xi p) (polyMul xj q))) r)
      (polyMul (polyMul k (polyMul xi xj)) (polyMul (polyMul p q) r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 2))
      (.mul (.var 3) (.var 4)))) (.var 5))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 3)))
      (.mul (.mul (.var 2) (.var 4)) (.var 5)))
    (by decide) (fun | 0 => k | 1 => xi | 2 => p | 3 => xj | 4 => q | _ => r)

private theorem atom_output (xi p xj q r : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (polyMul xi p) (polyMul xj q)) r)
      (polyMul (polyMul xi xj) (polyMul (polyMul p q) r)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.mul (.var 1) (.var 3)) (.var 4)))
    (by decide) (fun | 0 => xi | 1 => p | 2 => xj | 3 => q | _ => r)

private theorem mix_add (l m a b c d : Q') :
    (l*a+m*b)+(l*c+m*d) ≈ l*(a+c)+m*(b+d) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5))))
    (.add (.mul (.var 0) (.add (.var 2) (.var 4)))
      (.mul (.var 1) (.add (.var 3) (.var 5))))
    (by decide) (fun | 0 => l | 1 => m | 2 => a | 3 => b | 4 => c | _ => d)

private theorem zero_mix (l m : Q') : (0 : Q') ≈ l*0+m*0 :=
  Q'.eqv_symm (Q'.add_eqv_congr' (Q'.mul_zero_eqv l) (Q'.mul_zero_eqv m))

private theorem atom_transmission
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (i j : Fin 4) (p q r : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hq : SupportedQuaternionBlocks (tailBlocks+1) q)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdp : HasQuaternionBlockDegree a.val 0 p)
    (hdq : HasQuaternionBlockDegree a.val 0 q)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    heatPair (tailBlocks+1) a.val b.val w K
      (polyMul (polyMul (polyVar (4*a.val+i.val)) p)
        (polyMul (polyVar (4*a.val+j.val)) q)) r ≈
      qpow w 8 * pair (tailBlocks+1)
        (polyMul (polyMul (polyVar (4*b.val+i.val)) p)
          (polyMul (polyVar (4*b.val+j.val)) q)) r +
      (1 + -(qpow w 8)) * pair (tailBlocks+1)
        (polySmul (coordinateMoment i j) (polyMul p q)) r := by
  let s := polyMul (polyMul p q) r
  have hs : SupportedQuaternionBlocks (tailBlocks+1) s :=
    supported_polyMul (supported_polyMul hp hq) hr
  have hds : HasQuaternionBlockDegree a.val 0 s := (hdp.mul hdq).mul hdr
  have hi : heatPair (tailBlocks+1) a.val b.val w K
      (polyMul (polyMul (polyVar (4*a.val+i.val)) p)
        (polyMul (polyVar (4*a.val+j.val)) q)) r ≈
      quaternionHaar (tailBlocks+1) (polyMul
        (polyMul (heatAt a.val b.val w K)
          (polyMul (polyVar (4*a.val+i.val)) (polyVar (4*a.val+j.val)))) s) :=
    haar_of_coeff (atom_input _ _ _ _ _ _)
  have ho : pair (tailBlocks+1)
      (polyMul (polyMul (polyVar (4*b.val+i.val)) p)
        (polyMul (polyVar (4*b.val+j.val)) q)) r ≈
      quaternionHaar (tailBlocks+1) (polyMul
        (polyMul (polyVar (4*b.val+i.val)) (polyVar (4*b.val+j.val))) s) :=
    haar_of_coeff (atom_output _ _ _ _ _)
  have hg := pair_smul (tailBlocks+1) (coordinateMoment i j) (polyMul p q) r
  exact Q'.eqv_trans _ _ _ hi
    (Q'.eqv_trans _ _ _
      (coordinatePair_selected_transmission tailBlocks hb a b hab w K hK i j s hs hds)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg))))

private theorem atom_linear_transmission
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (i : Fin 4) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdp : HasQuaternionBlockDegree a.val 0 p)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    ∀ ys : List (Fin 4 × RatPoly),
      (∀ y, y ∈ ys → SupportedQuaternionBlocks (tailBlocks+1) y.2) →
      (∀ y, y ∈ ys → HasQuaternionBlockDegree a.val 0 y.2) →
      heatPair (tailBlocks+1) a.val b.val w K
        (polyMul (polyMul (polyVar (4*a.val+i.val)) p) (linearAt a.val ys)) r ≈
        qpow w 8 * pair (tailBlocks+1)
          (polyMul (polyMul (polyVar (4*b.val+i.val)) p) (linearAt b.val ys)) r +
        (1 + -(qpow w 8)) * pair (tailBlocks+1) (gramRow i p ys) r
  | [], _, _ => by
      have hz := pair_congr (tailBlocks+1)
        (RatPolyCoeffEqv.mul_zero_right (polyMul (polyVar (4*b.val+i.val)) p)) r
      exact Q'.eqv_trans _ _ _
        (heat_congr (tailBlocks+1) a.val b.val w K
          (RatPolyCoeffEqv.mul_zero_right (polyMul (polyVar (4*a.val+i.val)) p)) r)
        (Q'.eqv_trans _ _ _ (heat_zero (tailBlocks+1) a.val b.val w K r)
          (Q'.eqv_trans _ _ _ (zero_mix (qpow w 8) (1 + -(qpow w 8)))
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hz)) (Q'.eqv_refl _))))
  | (j,q)::ys, hys, hdys => by
      have hq := hys (j,q) List.mem_cons_self
      have hdq := hdys (j,q) List.mem_cons_self
      have htail := fun y hy => hys y (List.mem_cons_of_mem (j,q) hy)
      have hdtail := fun y hy => hdys y (List.mem_cons_of_mem (j,q) hy)
      have ho := Q'.eqv_trans _ _ _
        (pair_congr (tailBlocks+1)
          (RatPolyCoeffEqv.mul_add_right (polyMul (polyVar (4*b.val+i.val)) p)
            (polyMul (polyVar (4*b.val+j.val)) q) (linearAt b.val ys)) r)
        (pair_add (tailBlocks+1) _ _ r)
      have hg := pair_add (tailBlocks+1)
        (polySmul (coordinateMoment i j) (polyMul p q)) (gramRow i p ys) r
      exact Q'.eqv_trans _ _ _
        (heat_congr (tailBlocks+1) a.val b.val w K
          (RatPolyCoeffEqv.mul_add_right (polyMul (polyVar (4*a.val+i.val)) p)
            (polyMul (polyVar (4*a.val+j.val)) q) (linearAt a.val ys)) r)
        (Q'.eqv_trans _ _ _ (heat_add (tailBlocks+1) a.val b.val w K _ _ r)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (atom_transmission tailBlocks hb a b hab w K hK i j p q r
                hp hq hr hdp hdq hdr)
              (atom_linear_transmission tailBlocks hb a b hab w K hK i p r
                hp hr hdp hdr ys htail hdtail))
            (Q'.eqv_trans _ _ _
              (mix_add (qpow w 8) (1 + -(qpow w 8)) _ _ _ _)
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
                (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg))))))

private theorem linear_transmission
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    ∀ xs ys : List (Fin 4 × RatPoly),
      (∀ x, x ∈ xs → SupportedQuaternionBlocks (tailBlocks+1) x.2) →
      (∀ x, x ∈ xs → HasQuaternionBlockDegree a.val 0 x.2) →
      (∀ y, y ∈ ys → SupportedQuaternionBlocks (tailBlocks+1) y.2) →
      (∀ y, y ∈ ys → HasQuaternionBlockDegree a.val 0 y.2) →
      heatPair (tailBlocks+1) a.val b.val w K
        (polyMul (linearAt a.val xs) (linearAt a.val ys)) r ≈
        qpow w 8 * pair (tailBlocks+1)
          (polyMul (linearAt b.val xs) (linearAt b.val ys)) r +
        (1 + -(qpow w 8)) * pair (tailBlocks+1) (gram xs ys) r
  | [], _, _, _, _, _ => Q'.eqv_trans _ _ _
      (heat_zero (tailBlocks+1) a.val b.val w K r)
      (zero_mix (qpow w 8) (1 + -(qpow w 8)))
  | (i,p)::xs, ys, hxs, hdxs, hys, hdys => by
      have hp := hxs (i,p) List.mem_cons_self
      have hdp := hdxs (i,p) List.mem_cons_self
      have htail := fun x hx => hxs x (List.mem_cons_of_mem (i,p) hx)
      have hdtail := fun x hx => hdxs x (List.mem_cons_of_mem (i,p) hx)
      have ho := pair_add (tailBlocks+1)
        (polyMul (polyMul (polyVar (4*b.val+i.val)) p) (linearAt b.val ys))
        (polyMul (linearAt b.val xs) (linearAt b.val ys)) r
      have hg := pair_add (tailBlocks+1) (gramRow i p ys) (gram xs ys) r
      change heatPair (tailBlocks+1) a.val b.val w K
        (polyMul (polyAdd (polyMul (polyVar (4*a.val+i.val)) p)
          (linearAt a.val xs)) (linearAt a.val ys)) r ≈ _
      rw [polyMul_add_left_exact]
      have ht := Q'.eqv_trans _ _ _ (heat_add (tailBlocks+1) a.val b.val w K _ _ r)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (atom_linear_transmission tailBlocks hb a b hab w K hK i p r
              hp hr hdp hdr ys hys hdys)
            (linear_transmission tailBlocks hb a b hab w K hK r hr hdr xs ys
              htail hdtail hys hdys))
          (Q'.eqv_trans _ _ _
            (mix_add (qpow w 8) (1 + -(qpow w 8)) _ _ _ _)
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm ho))
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hg)))))
      simpa only [linearAt, gram, polyMul_add_left_exact] using ht

/-- Exact selected-block transmission for two finite coordinate-linear forms. -/
theorem linear_product_transmission
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (xs ys : List (Fin 4 × RatPoly)) (r : RatPoly)
    (hxs : ∀ x, x ∈ xs → SupportedQuaternionBlocks (tailBlocks+1) x.2)
    (hdxs : ∀ x, x ∈ xs → HasQuaternionBlockDegree a.val 0 x.2)
    (hys : ∀ y, y ∈ ys → SupportedQuaternionBlocks (tailBlocks+1) y.2)
    (hdys : ∀ y, y ∈ ys → HasQuaternionBlockDegree a.val 0 y.2)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (heatAt a.val b.val w K)
        (polyMul (linearAt a.val xs) (linearAt a.val ys))) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1)
        (polyMul (polyMul (linearAt b.val xs) (linearAt b.val ys)) r) +
      (1 + -(qpow w 8)) * quaternionHaar (tailBlocks+1)
        (polyMul (gram xs ys) r) :=
  linear_transmission tailBlocks hb a b hab w K hK r hr hdr xs ys
    hxs hdxs hys hdys

#print axioms linearAt
#print axioms linear_product_transmission

end YMGap.Continuum.SU2QuaternionSelectedLinearHeatProduct
