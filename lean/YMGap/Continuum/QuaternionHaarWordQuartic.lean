/-
# Fourth-moment bound for an ordered quaternion word difference

This module keeps the original common positive Haar insertion. The finite
constant is polynomial in word length; there is no independence or change of
measure. It does not assert an interacting variance or a continuum gap.
-/

import YMGap.Continuum.QuaternionHaarWordComponents

namespace YMGap.Continuum.QuaternionHaarWordQuartic

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
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul)
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarWordComponents

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

private def sq (p : RatPoly) : RatPoly := polyMul p p

private theorem supported_sum {n : Nat} : ∀ ps : List RatPoly,
    (∀ p, p ∈ ps → SupportedQuaternionBlocks n p) →
    SupportedQuaternionBlocks n (polySum ps)
  | [], _ => by
      intro t ht
      exact False.elim (List.not_mem_nil ht)
  | p::ps, h =>
      supported_add (h p List.mem_cons_self)
        (supported_sum ps (fun q hq => h q (List.mem_cons_of_mem p hq)))

private def squares_certificate {n : Nat} : (ps : List RatPoly) →
    (∀ p, p ∈ ps → SupportedQuaternionBlocks n p) →
    Certificate n (polySum (ps.map sq))
  | [], _ => by
      exact Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
        (Certificate.smul 0 (by decide) (Certificate.one n))
  | p::ps, h =>
      Certificate.add (Certificate.square p (h p List.mem_cons_self))
        (squares_certificate ps (fun q hq => h q (List.mem_cons_of_mem p hq)))

/-- Scalar fourth-power finite Cauchy certificate. The two exact gaps are
`m*sum p²-(sum p)²` and `m*sum p⁴-(sum p²)²`; their product/sum yields the
quartic gap without a positivity assumption on the signed inputs. -/
def scalar_fourth_certificate {n : Nat} (ps : List RatPoly)
    (hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p) :
    Certificate n
      (polyAdd
        (polyMul (polyMul (polyMul (cap (Q'.ofNat ps.length))
          (cap (Q'.ofNat ps.length))) (cap (Q'.ofNat ps.length)))
          (polySum ((ps.map sq).map sq)))
        (polyNeg (sq (sq (polySum ps))))) := by
  let m : Q' := Q'.ofNat ps.length
  let P : RatPoly := cap m
  let S : RatPoly := polySum ps
  let T : RatPoly := polySum (ps.map sq)
  let U : RatPoly := polySum ((ps.map sq).map sq)
  have hm : (0 : Q') ≤ m := Q'.ofNat_nonneg _
  let CP : Certificate n P := Certificate.constant n m hm
  have hps : ∀ q, q ∈ ps.map sq → SupportedQuaternionBlocks n q := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact supported_polyMul (hs p hp) (hs p hp)
  let CT : Certificate n T := squares_certificate ps hs
  have hS : SupportedQuaternionBlocks n S := supported_sum ps hs
  have C1 : Certificate n (polyAdd (polyMul P T) (polyNeg (sq S))) :=
    Certificate.ofCoeff
      ((cap_mul_left m T).add (RatPolyCoeffEqv.refl _))
      (sum_square_certificate ps hs)
  have C2 : Certificate n (polyAdd (polyMul P U) (polyNeg (sq T))) := by
    have h := sum_square_certificate (ps.map sq) hps
    simp only [List.length_map] at h
    change Certificate n (polyAdd (polySmul m U) (polyNeg (sq T))) at h
    exact Certificate.ofCoeff
      ((cap_mul_left m U).add (RatPolyCoeffEqv.refl _)) h
  let Cplus : Certificate n (polyAdd (polyMul P T) (sq S)) :=
    Certificate.add (Certificate.mul CP CT) (Certificate.square S hS)
  let Cgap : Certificate n
      (polyAdd
        (polyMul (polyAdd (polyMul P T) (polyNeg (sq S)))
          (polyAdd (polyMul P T) (sq S)))
        (polyMul (polyAdd (polyMul P U) (polyNeg (sq T)))
          (polyMul P P))) :=
    Certificate.add (Certificate.mul C1 Cplus)
      (Certificate.mul C2 (Certificate.mul CP CP))
  exact Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 3))
        (.neg (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))))
      (.add
        (.mul (.add (.mul (.var 0) (.var 2))
          (.neg (.mul (.var 1) (.var 1))))
          (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1))))
        (.mul (.add (.mul (.var 0) (.var 3))
          (.neg (.mul (.var 2) (.var 2))))
          (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => P | 1 => S | 2 => T | _ => U)) Cgap

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

/-- Same-weight finite scalar fourth moment, with polynomial list-length
factor. Its input is an actual fourth-moment estimate for every occurrence. -/
theorem scalar_fourth_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (ps : List RatPoly) (hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p)
    (B : Q') (hb : ∀ p, p ∈ ps →
      quaternionHaar n (polyMul W (sq (sq p))) ≤ B) :
    quaternionHaar n (polyMul W (sq (sq (polySum ps)))) ≤
      ((Q'.ofNat ps.length * Q'.ofNat ps.length) *
        (Q'.ofNat ps.length * Q'.ofNat ps.length)) * B := by
  let m : Q' := Q'.ofNat ps.length
  let P : RatPoly := cap m
  let U : RatPoly := polySum ((ps.map sq).map sq)
  have horder : quaternionHaar n (polyMul W (sq (sq (polySum ps)))) ≤
      quaternionHaar n (polyMul W (polyMul (polyMul (polyMul P P) P) U)) :=
    weighted_order R (scalar_fourth_certificate ps hs)
  have hcap : RatPolyCoeffEqv (polyMul (polyMul (polyMul P P) P) U)
      (polySmul ((m*m)*m) U) :=
    ((((cap_mul m m).mul_right P).trans (cap_mul (m*m) m)).mul_right U).trans
      (cap_mul_left ((m*m)*m) U)
  have hscale : quaternionHaar n (polyMul W (polyMul (polyMul (polyMul P P) P) U)) ≈
      ((m*m)*m) * quaternionHaar n (polyMul W U) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hcap.mul_left W))
      (weighted_scale n W U ((m*m)*m))
  have hsum : quaternionHaar n (polyMul W U) ≤ m*B := by
    have he := haar_weighted_sum n W ((ps.map sq).map sq)
    have hl := sum_bound B
      (((ps.map sq).map sq).map (fun p => quaternionHaar n (polyMul W p)))
      (by
        intro x hx
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
        exact hb p hp)
    simp only [List.length_map] at hl
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hl
  have hm : (0 : Q') ≤ (m*m)*m :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))
      (Q'.ofNat_nonneg _)
  have hlast : ((m*m)*m)*(m*B) ≈ ((m*m)*(m*m))*B :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0))
        (.mul (.var 0) (.var 1)))
      (.mul (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 0) (.var 0))) (.var 1))
      (by decide) (fun | 0 => m | _ => B)
  exact Q'.le_trans' _ _ _ horder
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum hm)
        (Q'.le_of_eqv hlast)))

private def norm_certificate {n : Nat} (p : PolyQuaternion) (hp : Supported n p) :
    Certificate n (polyQuaternionNorm p) :=
  Certificate.add (Certificate.square p.scalar hp.scalar)
    (Certificate.add (Certificate.square p.iPart hp.iPart)
      (Certificate.add (Certificate.square p.jPart hp.jPart)
        (Certificate.square p.kPart hp.kPart)))

private theorem component_supported {n : Nat} (p : PolyQuaternion)
    (hp : Supported n p) (i : Nat) :
    SupportedQuaternionBlocks n (component i p) := by
  match i with
  | 0 => exact hp.scalar
  | 1 => exact hp.iPart
  | 2 => exact hp.jPart
  | _+3 => exact hp.kPart

private def otherSquares (p : PolyQuaternion) : Nat → RatPoly
  | 0 => polyAdd (sq p.iPart) (polyAdd (sq p.jPart) (sq p.kPart))
  | 1 => polyAdd (sq p.scalar) (polyAdd (sq p.jPart) (sq p.kPart))
  | 2 => polyAdd (sq p.scalar) (polyAdd (sq p.iPart) (sq p.kPart))
  | _+3 => polyAdd (sq p.scalar) (polyAdd (sq p.iPart) (sq p.jPart))

private def other_certificate {n : Nat} (p : PolyQuaternion)
    (hp : Supported n p) : (i : Nat) → Certificate n (otherSquares p i)
  | 0 => Certificate.add (Certificate.square p.iPart hp.iPart)
      (Certificate.add (Certificate.square p.jPart hp.jPart)
        (Certificate.square p.kPart hp.kPart))
  | 1 => Certificate.add (Certificate.square p.scalar hp.scalar)
      (Certificate.add (Certificate.square p.jPart hp.jPart)
        (Certificate.square p.kPart hp.kPart))
  | 2 => Certificate.add (Certificate.square p.scalar hp.scalar)
      (Certificate.add (Certificate.square p.iPart hp.iPart)
        (Certificate.square p.kPart hp.kPart))
  | _+3 => Certificate.add (Certificate.square p.scalar hp.scalar)
      (Certificate.add (Certificate.square p.iPart hp.iPart)
        (Certificate.square p.jPart hp.jPart))

private def sqExpr (e : PolyExpr) : PolyExpr := .mul e e
private def normExpr : PolyExpr := .add (sqExpr (.var 0))
  (.add (sqExpr (.var 1)) (.add (sqExpr (.var 2)) (sqExpr (.var 3))))
private def selectedExpr : Nat → PolyExpr
  | 0 => .var 0 | 1 => .var 1 | 2 => .var 2 | _+3 => .var 3
private def otherExpr : Nat → PolyExpr
  | 0 => .add (sqExpr (.var 1)) (.add (sqExpr (.var 2)) (sqExpr (.var 3)))
  | 1 => .add (sqExpr (.var 0)) (.add (sqExpr (.var 2)) (sqExpr (.var 3)))
  | 2 => .add (sqExpr (.var 0)) (.add (sqExpr (.var 1)) (sqExpr (.var 3)))
  | _+3 => .add (sqExpr (.var 0)) (.add (sqExpr (.var 1)) (sqExpr (.var 2)))

private def env (p : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | _ => p.kPart

private def component_gap_certificate {n : Nat} (p : PolyQuaternion)
    (hp : Supported n p) (i : Nat) :
    Certificate n (polyAdd (polyQuaternionNorm p) (polyNeg (sq (component i p)))) := by
  have he : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm p) (polyNeg (sq (component i p))))
      (otherSquares p i) := by
    match i with
    | 0 =>
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add normExpr (.neg (sqExpr (selectedExpr 0)))) (otherExpr 0)
          (by decide) (env p)
    | 1 =>
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add normExpr (.neg (sqExpr (selectedExpr 1)))) (otherExpr 1)
          (by decide) (env p)
    | 2 =>
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add normExpr (.neg (sqExpr (selectedExpr 2)))) (otherExpr 2)
          (by decide) (env p)
    | k+3 =>
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add normExpr (.neg (sqExpr (.var 3))))
          (.add (sqExpr (.var 0)) (.add (sqExpr (.var 1)) (sqExpr (.var 2))))
          (by decide) (env p)
  exact Certificate.ofCoeff he (other_certificate p hp i)

/-- Every coordinate fourth power is bounded by the squared quaternion
norm under the SAME original positive weight. -/
theorem component_fourth_le_norm_square {n : Nat} {W : RatPoly}
    (R : Certificate n W) (p : PolyQuaternion) (hp : Supported n p) (i : Nat) :
    quaternionHaar n (polyMul W (sq (sq (component i p)))) ≤
      quaternionHaar n (polyMul W (sq (polyQuaternionNorm p))) := by
  let N := polyQuaternionNorm p
  let c := component i p
  let Q := sq c
  let Cplus : Certificate n (polyAdd N Q) :=
    Certificate.add (norm_certificate p hp)
      (Certificate.square c (component_supported p hp i))
  have Cgap : Certificate n (polyAdd N (polyNeg Q)) :=
    component_gap_certificate p hp i
  have C : Certificate n (polyAdd (sq N) (polyNeg (sq Q))) :=
    Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 0))
          (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 0) (.neg (.var 1)))
          (.add (.var 0) (.var 1)))
        (by decide) (fun | 0 => N | _ => Q))
      (Certificate.mul Cgap Cplus)
  exact weighted_order R C

private def coordinateSquares (p : PolyQuaternion) : List RatPoly :=
  [sq p.scalar, sq p.iPart, sq p.jPart, sq p.kPart]

private theorem coordinateSquares_supported {n : Nat} (p : PolyQuaternion)
    (hp : Supported n p) :
    ∀ q, q ∈ coordinateSquares p → SupportedQuaternionBlocks n q := by
  intro q hq
  change q ∈ [sq p.scalar, sq p.iPart, sq p.jPart, sq p.kPart] at hq
  rcases List.mem_cons.mp hq with h | hq
  · subst q; exact supported_polyMul hp.scalar hp.scalar
  rcases List.mem_cons.mp hq with h | hq
  · subst q; exact supported_polyMul hp.iPart hp.iPart
  rcases List.mem_cons.mp hq with h | hq
  · subst q; exact supported_polyMul hp.jPart hp.jPart
  have h := List.mem_singleton.mp hq
  subst q
  exact supported_polyMul hp.kPart hp.kPart

private theorem coordinateSquares_sum (p : PolyQuaternion) :
    RatPolyCoeffEqv (polySum (coordinateSquares p)) (polyQuaternionNorm p) :=
  (RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))

/-- Four-coordinate Cauchy: the squared quaternion norm is bounded by four
times the sum of coordinate fourth powers under the same positive weight. -/
theorem norm_fourth_le_coordinate_fourths {n : Nat} {W : RatPoly}
    (R : Certificate n W) (p : PolyQuaternion) (hp : Supported n p) :
    quaternionHaar n (polyMul W (sq (polyQuaternionNorm p))) ≤
      4 * qListSum ((coordinateSquares p).map
        (fun q => quaternionHaar n (polyMul W (sq q)))) := by
  let ps := coordinateSquares p
  have hcs := sum_square_certificate ps (coordinateSquares_supported p hp)
  have h := weighted_order R hcs
  have hl : quaternionHaar n (polyMul W (sq (polyQuaternionNorm p))) ≈
      quaternionHaar n (polyMul W (sq (polySum ps))) :=
    haar_of_coeff (((coordinateSquares_sum p).symm.mul
      (coordinateSquares_sum p).symm).mul_left W)
  have hr : quaternionHaar n (polyMul W
      (polySmul 4 (polySum (ps.map sq)))) ≈
      4 * qListSum (ps.map (fun q => quaternionHaar n (polyMul W (sq q)))) :=
    Q'.eqv_trans _ _ _ (weighted_scale n W _ 4)
      (Q'.mul_eqv_congr_left _ _ _ (haar_weighted_sum_indexed n W sq ps))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- Every full quaternion telescope term has exactly its one-link squared
displacement norm, even after squaring the norm again. -/
private theorem terms_norm_quartic_bound {n : Nat} (W : RatPoly) (B : Q')
    (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link),
      HaarCarrierEqv n (polyQuaternionNorm p) polyOne →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne) →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne) →
      (∀ e, e ∈ es → quaternionHaar n
        (polyMul W (sq (polyQuaternionNorm (difference (left e) (right e))))) ≤ B) →
      ∀ q, q ∈ terms left right p es →
        quaternionHaar n (polyMul W (sq (polyQuaternionNorm q))) ≤ B
  | _, [], _, _, _, _, _, h => False.elim (List.not_mem_nil h)
  | p, e::es, hp, hl, hr, hb, q, hq => by
      rcases List.mem_cons.mp hq with h | h
      · subst q
        have hnorm := unit_sandwich_norm hp
          (word_unit right es (fun f hf => hr f (List.mem_cons_of_mem e hf)))
          (difference (left e) (right e))
        have hsq : HaarCarrierEqv n
            (sq (polyQuaternionNorm ((p ⋄ difference (left e) (right e)) ⋄ wordWith right es)))
            (sq (polyQuaternionNorm (difference (left e) (right e)))) :=
          HaarCarrierEqv.mul hnorm hnorm
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (hsq W))
          (hb e List.mem_cons_self)
      · exact terms_norm_quartic_bound W B left right (p ⋄ left e) es
          (haarNorm_mul hp (hl e List.mem_cons_self))
          (fun f hf => hl f (List.mem_cons_of_mem e hf))
          (fun f hf => hr f (List.mem_cons_of_mem e hf))
          (fun f hf => hb f (List.mem_cons_of_mem e hf)) q h

/-- Explicit polynomial fourth-moment cost of a word with `m` occurrences. -/
def wordFourthFactor (m : Nat) : Q' :=
  16 * ((Q'.ofNat m * Q'.ofNat m) * (Q'.ofNat m * Q'.ofNat m))

private theorem word_component_fourth_bound {n : Nat} {W : RatPoly}
    (R : Certificate n W)
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link)
    (hl : ∀ e, e ∈ es → Supported n (left e))
    (hr : ∀ e, e ∈ es → Supported n (right e))
    (hlu : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne)
    (hru : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne)
    (B : Q') (hb : ∀ e, e ∈ es → quaternionHaar n
      (polyMul W (sq (polyQuaternionNorm (difference (left e) (right e))))) ≤ B)
    (i : Nat) :
    quaternionHaar n (polyMul W
      (sq (sq (component i (difference (wordWith left es) (wordWith right es)))))) ≤
      ((Q'.ofNat es.length * Q'.ofNat es.length) *
        (Q'.ofNat es.length * Q'.ofNat es.length)) * B := by
  let ts := terms left right PolyQuaternion.one es
  have hs := terms_supported left right PolyQuaternion.one es (Supported.one n) hl hr
  have ht := terms_norm_quartic_bound W B left right PolyQuaternion.one es
    (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one) hlu hru hb
  have hsc := scalar_fourth_bound R (ts.map (component i))
    (by
      intro c hc
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      exact component_supported q (hs q hq) i) B
    (by
      intro c hc
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      exact Q'.le_trans' _ _ _
        (component_fourth_le_norm_square R q (hs q hq) i)
        (ht q hq))
  have hend : RatPolyCoeffEqv
      (component i (difference (PolyQuaternion.one ⋄ wordWith left es)
        (PolyQuaternion.one ⋄ wordWith right es)))
      (component i (difference (wordWith left es) (wordWith right es))) := by
    simp only [component_difference]
    exact (component_congr i (PolyQuaternionCoeffEqv.one_mul _)).add
      (RatPolyCoeffEqv.neg
        (component_congr i (PolyQuaternionCoeffEqv.one_mul _)))
  have he := (terms_component i left right PolyQuaternion.one es).trans hend
  have hfourth := (((he.mul he).mul (he.mul he)).mul_left W)
  rw [List.length_map, terms_length] at hsc
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff hfourth.symm)) hsc

/-- Fourth moment of the FULL ordered quaternion word difference under the
original certified weight. The factor `16*m⁴` is polynomial, valid with
repeated links and overlapping variables; no independence is used. -/
theorem word_norm_quartic_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link)
    (hl : ∀ e, e ∈ es → Supported n (left e))
    (hr : ∀ e, e ∈ es → Supported n (right e))
    (hlu : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne)
    (hru : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne)
    (B : Q') (hb : ∀ e, e ∈ es → quaternionHaar n
      (polyMul W (sq (polyQuaternionNorm (difference (left e) (right e))))) ≤ B) :
    quaternionHaar n (polyMul W
      (sq (polyQuaternionNorm (difference (wordWith left es) (wordWith right es))))) ≤
      wordFourthFactor es.length * B := by
  let D := difference (wordWith left es) (wordWith right es)
  let m : Q' := Q'.ofNat es.length
  let C : Q' := ((m*m)*(m*m))*B
  have hD : Supported n D :=
    difference_supported (word_supported left es hl) (word_supported right es hr)
  have h0 := word_component_fourth_bound R left right es hl hr hlu hru B hb 0
  have h1 := word_component_fourth_bound R left right es hl hr hlu hru B hb 1
  have h2 := word_component_fourth_bound R left right es hl hr hlu hru B hb 2
  have h3 := word_component_fourth_bound R left right es hl hr hlu hru B hb 3
  have hsum : qListSum ((coordinateSquares D).map
      (fun q => quaternionHaar n (polyMul W (sq q)))) ≤ 4*C := by
    have h := sum_bound C ((coordinateSquares D).map
      (fun q => quaternionHaar n (polyMul W (sq q)))) (by
      intro x hx
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
      change q ∈ [sq D.scalar, sq D.iPart, sq D.jPart, sq D.kPart] at hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact h0
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact h1
      rcases List.mem_cons.mp hq with he | hq
      · subst q; exact h2
      have he := List.mem_singleton.mp hq
      subst q
      exact h3)
    simpa only [List.length_map, coordinateSquares, List.length_cons,
      List.length_nil, Nat.reduceAdd, C, m] using h
  have hfactor : 4*(4*C) ≈ wordFourthFactor es.length * B :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.const 4) (.mul (.var 0) (.var 1))))
      (.mul (.mul (.const 16) (.var 0)) (.var 1))
      (by decide) (fun | 0 => (m*m)*(m*m) | _ => B)
  have hn := norm_fourth_le_coordinate_fourths R D hD
  exact Q'.le_trans' _ _ _ hn
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (by decide))
      (Q'.le_of_eqv hfactor))

#print axioms scalar_fourth_certificate
#print axioms scalar_fourth_bound
#print axioms component_fourth_le_norm_square
#print axioms norm_fourth_le_coordinate_fourths
#print axioms terms_norm_quartic_bound
#print axioms wordFourthFactor
#print axioms word_component_fourth_bound
#print axioms word_norm_quartic_bound

end YMGap.Continuum.QuaternionHaarWordQuartic
