/-
# Exact quadratic cost of an ordered quaternion word

Four scalar finite-Cauchy certificates are added BEFORE charging the
one-link budget. Their diagonal sum is the full quaternion norm, so no
factor four is lost. The original positive Haar weight remains present.
-/

import YMGap.Continuum.QuaternionHaarWordComponents

namespace YMGap.Continuum.QuaternionHaarWordQuadratic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (polyQuaternionNorm_one)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarWordComponents

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private def sq (p : RatPoly) : RatPoly := polyMul p p
private def coordSum (ts : List PolyQuaternion) (i : Nat) : RatPoly :=
  polySum (ts.map (component i))
private def coordDiag (ts : List PolyQuaternion) (i : Nat) : RatPoly :=
  polySum (ts.map (fun t => sq (component i t)))
private def vectorSum (ts : List PolyQuaternion) : PolyQuaternion :=
  ⟨coordSum ts 0, coordSum ts 1, coordSum ts 2, coordSum ts 3⟩
private def normSum (ts : List PolyQuaternion) : RatPoly :=
  polySum (ts.map polyQuaternionNorm)

private theorem component_supported {n : Nat} (t : PolyQuaternion)
    (ht : Supported n t) (i : Nat) :
    SupportedQuaternionBlocks n (component i t) := by
  match i with
  | 0 => exact ht.scalar
  | 1 => exact ht.iPart
  | 2 => exact ht.jPart
  | _+3 => exact ht.kPart

/-- Reindex the exact sum of term norms by the four real coordinates. -/
private theorem normSum_coordinates (ts : List PolyQuaternion) :
    RatPolyCoeffEqv (normSum ts)
      (polyAdd (coordDiag ts 0)
        (polyAdd (coordDiag ts 1)
          (polyAdd (coordDiag ts 2) (coordDiag ts 3)))) := by
  induction ts with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons t ts ih =>
      have h := (RatPolyCoeffEqv.refl (polyQuaternionNorm t)).add ih
      change RatPolyCoeffEqv
        (polyAdd (polyQuaternionNorm t) (normSum ts))
        (polyAdd (coordDiag (t::ts) 0)
          (polyAdd (coordDiag (t::ts) 1)
            (polyAdd (coordDiag (t::ts) 2) (coordDiag (t::ts) 3))))
      exact h.trans (coeffEvalExpr_eqv_of_normalize_eq
        (.add
          (.add (.mul (.var 0) (.var 0))
            (.add (.mul (.var 1) (.var 1))
              (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
          (.add (.var 4) (.add (.var 5) (.add (.var 6) (.var 7)))))
        (.add (.add (.mul (.var 0) (.var 0)) (.var 4))
          (.add (.add (.mul (.var 1) (.var 1)) (.var 5))
            (.add (.add (.mul (.var 2) (.var 2)) (.var 6))
              (.add (.mul (.var 3) (.var 3)) (.var 7)))))
        (by decide) (fun
          | 0 => t.scalar | 1 => t.iPart | 2 => t.jPart | 3 => t.kPart
          | 4 => coordDiag ts 0 | 5 => coordDiag ts 1
          | 6 => coordDiag ts 2 | _ => coordDiag ts 3))

/-- One vector finite-Cauchy certificate: its diagonal is the complete
quaternion norm, not four separately bounded coordinate diagonals. -/
private def vector_square_certificate {n : Nat} (ts : List PolyQuaternion)
    (hs : ∀ t, t ∈ ts → Supported n t) :
    Certificate n
      (polyAdd (polySmul (Q'.ofNat ts.length) (normSum ts))
        (polyNeg (polyQuaternionNorm (vectorSum ts)))) := by
  let m := Q'.ofNat ts.length
  let P := cap m
  let d0 := coordDiag ts 0
  let d1 := coordDiag ts 1
  let d2 := coordDiag ts 2
  let d3 := coordDiag ts 3
  let s0 := coordSum ts 0
  let s1 := coordSum ts 1
  let s2 := coordSum ts 2
  let s3 := coordSum ts 3
  have hsupport (i : Nat) : ∀ p, p ∈ ts.map (component i) →
      SupportedQuaternionBlocks n p := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    exact component_supported t (hs t ht) i
  have hcert (i : Nat) : Certificate n
      (polyAdd (polyMul P (coordDiag ts i))
        (polyNeg (sq (coordSum ts i)))) := by
    have C := sum_square_certificate (ts.map (component i)) (hsupport i)
    simp only [List.length_map, List.map_map, Function.comp_def] at C
    change Certificate n
      (polyAdd (polySmul m (coordDiag ts i))
        (polyNeg (sq (coordSum ts i)))) at C
    exact Certificate.ofCoeff
      ((cap_mul_left m (coordDiag ts i)).add (RatPolyCoeffEqv.refl _)) C
  have C : Certificate n
      (polyAdd (polyAdd (polyMul P d0) (polyNeg (sq s0)))
        (polyAdd (polyAdd (polyMul P d1) (polyNeg (sq s1)))
          (polyAdd (polyAdd (polyMul P d2) (polyNeg (sq s2)))
            (polyAdd (polyMul P d3) (polyNeg (sq s3)))))) :=
    (hcert 0).add ((hcert 1).add ((hcert 2).add (hcert 3)))
  have hdiag := normSum_coordinates ts
  have htarget : RatPolyCoeffEqv
      (polyAdd (polySmul m (normSum ts))
        (polyNeg (polyQuaternionNorm (vectorSum ts))))
      (polyAdd (polyAdd (polyMul P d0) (polyNeg (sq s0)))
        (polyAdd (polyAdd (polyMul P d1) (polyNeg (sq s1)))
          (polyAdd (polyAdd (polyMul P d2) (polyNeg (sq s2)))
            (polyAdd (polyMul P d3) (polyNeg (sq s3)))))) := by
    have hfirst := (cap_mul_left m (normSum ts)).symm
    have hsecond := ((RatPolyCoeffEqv.refl P).mul hdiag).add
      (RatPolyCoeffEqv.refl (polyNeg (polyQuaternionNorm (vectorSum ts))))
    exact (hfirst.add (RatPolyCoeffEqv.refl _)).trans
      (hsecond.trans (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0)
          (.add (.var 1) (.add (.var 2) (.add (.var 3) (.var 4)))))
          (.neg (.add (.mul (.var 5) (.var 5))
            (.add (.mul (.var 6) (.var 6))
              (.add (.mul (.var 7) (.var 7)) (.mul (.var 8) (.var 8)))))))
        (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 5) (.var 5))))
          (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 6) (.var 6))))
            (.add (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 7) (.var 7))))
              (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 8) (.var 8)))))))
        (by decide) (fun
          | 0 => P | 1 => d0 | 2 => d1 | 3 => d2 | 4 => d3
          | 5 => s0 | 6 => s1 | 7 => s2 | _ => s3)))
  exact Certificate.ofCoeff htarget C

private theorem sum_bound (B : Q') : ∀ xs : List Q',
    (∀ x, x ∈ xs → x ≤ B) → qListSum xs ≤ Q'.ofNat xs.length * B
  | [], _ => Q'.ge_of_eqv (Q'.zero_mul_eqv B)
  | x::xs, h => by
      have hs := Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (h x List.mem_cons_self))
        (Q'.add_le_add_left _ _ _
          (sum_bound B xs (fun y hy => h y (List.mem_cons_of_mem x hy))))
      have he : Q'.ofNat (xs.length+1)*B ≈ B+Q'.ofNat xs.length*B :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv _ _))
          (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
            (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv B))
              (Q'.add_comm_eqv _ _)))
      exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv he)

/-- Finite quaternion-vector Cauchy with the sharp list-length-squared
factor under the SAME square-certified Haar weight. -/
theorem vector_square_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (ts : List PolyQuaternion) (hs : ∀ t, t ∈ ts → Supported n t)
    (B : Q') (hb : ∀ t, t ∈ ts →
      quaternionHaar n (polyMul W (polyQuaternionNorm t)) ≤ B) :
    quaternionHaar n (polyMul W (polyQuaternionNorm (vectorSum ts))) ≤
      (Q'.ofNat ts.length * Q'.ofNat ts.length)*B := by
  let m := Q'.ofNat ts.length
  have horder := weighted_order R (vector_square_certificate ts hs)
  have hscale := weighted_scale n W (normSum ts) m
  have hsum : quaternionHaar n (polyMul W (normSum ts)) ≤ m*B := by
    have he := haar_weighted_sum_indexed n W polyQuaternionNorm ts
    have hl := sum_bound B
      (ts.map (fun t => quaternionHaar n (polyMul W (polyQuaternionNorm t))))
      (by intro x hx; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact hb t ht)
    simp only [List.length_map] at hl
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hl
  have hfactor : m*(m*B) ≈ (m*m)*B :=
    Q'.eqv_symm (Q'.mul_assoc_eqv m m B)
  exact Q'.le_trans' _ _ _ horder
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (Q'.ofNat_nonneg _))
        (Q'.le_of_eqv hfactor)))

private theorem difference_congr {p p' q q' : PolyQuaternion}
    (hp : PolyQuaternionCoeffEqv p p') (hq : PolyQuaternionCoeffEqv q q') :
    PolyQuaternionCoeffEqv (difference p q) (difference p' q') :=
  ⟨hp.scalar.add (RatPolyCoeffEqv.neg hq.scalar),
   hp.iPart.add (RatPolyCoeffEqv.neg hq.iPart),
   hp.jPart.add (RatPolyCoeffEqv.neg hq.jPart),
   hp.kPart.add (RatPolyCoeffEqv.neg hq.kPart)⟩

private theorem norm_congr {p q : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv p q) :
    RatPolyCoeffEqv (polyQuaternionNorm p) (polyQuaternionNorm q) :=
  (h.scalar.mul h.scalar).add ((h.iPart.mul h.iPart).add
    ((h.jPart.mul h.jPart).add (h.kPart.mul h.kPart)))

/-- Original noncommuting word chordal second moment, no component-factor
loss and no independence or source-factorization premise. -/
theorem word_norm_quadratic_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link)
    (hl : ∀ e, e ∈ es → Supported n (left e))
    (hr : ∀ e, e ∈ es → Supported n (right e))
    (hlu : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne)
    (hru : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne)
    (B : Q') (hb : ∀ e, e ∈ es →
      quaternionHaar n (polyMul W
        (polyQuaternionNorm (difference (left e) (right e)))) ≤ B) :
    quaternionHaar n (polyMul W
      (polyQuaternionNorm (difference (wordWith left es) (wordWith right es)))) ≤
      (Q'.ofNat es.length * Q'.ofNat es.length)*B := by
  let ts := terms left right PolyQuaternion.one es
  have hs := terms_supported left right PolyQuaternion.one es (Supported.one n) hl hr
  have ht := terms_norm_bound W B left right PolyQuaternion.one es
    (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one) hlu hru hb
  have h := vector_square_bound R ts hs B ht
  have he : PolyQuaternionCoeffEqv (vectorSum ts)
      (difference (wordWith left es) (wordWith right es)) :=
    (terms_components left right PolyQuaternion.one es).trans
      (difference_congr (PolyQuaternionCoeffEqv.one_mul _)
        (PolyQuaternionCoeffEqv.one_mul _))
  rw [terms_length] at h
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (haar_of_coeff ((norm_congr he).mul_left W))) h

#print axioms vector_square_certificate
#print axioms vector_square_bound
#print axioms word_norm_quadratic_bound

end YMGap.Continuum.QuaternionHaarWordQuadratic
