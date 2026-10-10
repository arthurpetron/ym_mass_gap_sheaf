/-
# Connected coercivity on the existing weighted Haar channels

First angular IBP pins the mixed moment of the complete square. Weighted
Cauchy--Schwarz then removes its raw mean contribution without dividing by
a channel mass or a source norm. Signed sources, zero mass and every rational
a,t are retained. The connected determinant is not the original interacting
OWN variance. Cubic/pair payment, omitted cutoff and scaling remain separate.
-/

import YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
import YMGap.Continuum.RationalQuadraticDiscriminant

namespace YMGap.Continuum.SU2QuaternionChannelConnectedCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.OSReconstructionProgress (le_of_le_eqv le_of_eqv_le)
open YMGap.Continuum.RationalQuadraticDiscriminant

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

private theorem sum_linear (cs : List GramChannel) (p q : RatPoly → Q') (a d : Q') :
    channelSum cs (fun z => a*p z+d*q z) ≈
      a*channelSum cs p+d*channelSum cs q :=
  Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
    (Q'.add_eqv_congr' (channelSum_smul p a cs) (channelSum_smul q d cs))

private theorem sum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

/-- The literal passive weights paired with functions of the channel polynomial. -/
def channelHaarPair (n : Nat) (cs : List GramChannel) (p q : RatPoly → RatPoly) : Q' :=
  channelSum cs (fun z => H n (polyMul (p z) (q z)))

/-- Only polynomials actually occurring in the channel list need support. -/
theorem channelHaarPair_self_nonnegative (n : Nat) (cs : List GramChannel)
    (hw : ∀ c, c ∈ cs → (0 : Q') ≤ c.1) (p : RatPoly → RatPoly)
    (hp : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (p c.2)) :
    (0 : Q') ≤ channelHaarPair n cs p p :=
  sum_nonnegative _ cs hw (fun c hc => quaternionHaar_square_nonnegative n _ (hp c hc))

private theorem haar_two_square (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (a d : Q') :
    let s := polyAdd (polySmul a p) (polySmul d q)
    H n (polyMul s s) ≈ a*a*H n (polyMul p p) +
      2*a*d*H n (polyMul p q) + d*d*H n (polyMul q q) := by
  dsimp only
  let D := weightedGNSData n polyOne (Certificate.one n)
  have h := D.diag_expand a d ⟨p, hp⟩ ⟨q, hq⟩
  have hb (r s : RatPoly) : weightedPair n polyOne r s ≈ H n (polyMul r s) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one _)
  have ht := Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl a) (qmul (Q'.eqv_refl a) (hb p p)))
      (qmul (Q'.eqv_refl a) (qmul (Q'.eqv_refl d) (hb p q))))
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl d) (qmul (Q'.eqv_refl a) (hb p q)))
      (qmul (Q'.eqv_refl d) (qmul (Q'.eqv_refl d) (hb q q)))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hb _ _)) (Q'.eqv_trans _ _ _ ht
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 1) (.mul (.var 0) (.var 3)))
          (.mul (.var 1) (.mul (.var 1) (.var 4)))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
      (fun
        | 0 => a
        | 1 => d
        | 2 => H n (polyMul p p)
        | 3 => H n (polyMul p q)
        | _ => H n (polyMul q q))))

/-- Weighted squares u*p-v*q produce the discriminant, including zero diagonals.
No channel GNS wrapper or positivity premise on p/q is introduced. -/
theorem channelHaarPair_cauchySchwarz (n : Nat) (cs : List GramChannel)
    (hw : ∀ c, c ∈ cs → (0 : Q') ≤ c.1) (p q : RatPoly → RatPoly)
    (hp : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (p c.2))
    (hq : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (q c.2)) :
    channelHaarPair n cs p q * channelHaarPair n cs p q ≤
      channelHaarPair n cs p p * channelHaarPair n cs q q := by
  apply nonnegative_quadratic_discriminant
  intro u v
  let s : RatPoly → RatPoly := fun z => polyAdd (polySmul u (p z)) (polySmul (-v) (q z))
  let pp : RatPoly → Q' := fun z => H n (polyMul (p z) (p z))
  let pq : RatPoly → Q' := fun z => H n (polyMul (p z) (q z))
  let qq : RatPoly → Q' := fun z => H n (polyMul (q z) (q z))
  have hz := channelHaarPair_self_nonnegative n cs hw s (fun c hc =>
    supported_add (polySmul_supported (hp c hc) u) (polySmul_supported (hq c hc) (-v)))
  have he := channelSum_congr (fun z => H n (polyMul (s z) (s z)))
    (fun z => u*u*pp z+2*u*(-v)*pq z+(-v)*(-v)*qq z) cs (fun c hc =>
    haar_two_square n (p c.2) (q c.2) (hp c hc) (hq c hc) u (-v))
  have ht := Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (channelSum_add (fun z => u*u*pp z+2*u*(-v)*pq z)
      (fun z => (-v)*(-v)*qq z) cs)
    (Q'.add_eqv_congr'
      (sum_linear cs pp pq (u*u) (2*u*(-v)))
      (channelSum_smul qq ((-v)*(-v)) cs)))
  exact le_of_le_eqv hz (Q'.eqv_trans _ _ _ ht
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.neg (.var 1))) (.var 3)))
        (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.var 4)))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.neg (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3))))
        (.mul (.mul (.var 1) (.var 1)) (.var 4))) (by decide)
      (fun
        | 0 => u
        | 1 => v
        | 2 => channelHaarPair n cs p p
        | 3 => channelHaarPair n cs p q
        | _ => channelHaarPair n cs q q)))

/-- The actual Casimir-twelve pin tested against b squared gives first IBP. -/
theorem casimir12_first_ibp (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (b f : RatPoly)
    (_hb : SupportedQuaternionBlocks n b) (_hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) :
    H n (polyMul b (activeGamma active b f)) ≈
      6*H n (polyMul (polyMul b b) f) := by
  let x := activeGamma active b f
  let J := H n (polyMul b x)
  let M := H n (polyMul (polyMul b b) f)
  have hs := activeGamma_symm active f b
  have hprod := (activeGamma_symm active (polyMul b b) f).trans
    ((activeGamma_mul_right active f b b).trans
      ((hs.mul_right b).add (hs.mul_left b)))
  have hr : RatPolyCoeffEqv (polyAdd (polyMul x b) (polyMul b x))
      (polySmul 2 (polyMul b x)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => b | _ => x)).trans
      (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left 2 _)
  have hright := Q'.eqv_trans _ _ _ (haar_of_coeff (hprod.trans hr))
    (quaternionHaar_polySmul n 2 _)
  have hleft := Q'.eqv_trans _ _ _ (hCf (polyMul b b))
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right 12 (polyMul b b) f))
      (quaternionHaar_polySmul n 12 _))
  have h2 : 2*J ≈ 12*M := Q'.eqv_trans _ _ _ (Q'.eqv_symm hright)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (casimir_pair_gamma n active hactive (polyMul b b) f)) hleft)
  have hJ : HalfPow.half*(2*J) ≈ J :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 2 J))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 J (by decide)) (Q'.one_mul_eqv J))
  have hM : HalfPow.half*(12*M) ≈ 6*M :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 12 M))
      (Q'.mul_eqv_congr_right _ 6 M (by decide))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hJ)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _ h2) hM)

private theorem haar_pair_linear (n : Nat) (p q r : RatPoly) (a d : Q') :
    H n (polyMul p (polyAdd (polySmul a q) (polySmul d r))) ≈
      a*H n (polyMul p q)+d*H n (polyMul p r) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_add_right p _ _).trans
      ((RatPolyCoeffEqv.polyMul_smul_right a p q).add
        (RatPolyCoeffEqv.polyMul_smul_right d p r))))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (quaternionHaar_polySmul n a _)
        (quaternionHaar_polySmul n d _)))

/-- The complete square's mixed channel moment retains the exact mean. -/
theorem channel_coercivity_mixed (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (cs : List GramChannel)
    (b : RatPoly → RatPoly)
    (hb : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (b c.2))
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f))
    (a t : Q') :
    channelHaarPair n cs b (fun z => coercivitySquare active (b z) f a t) ≈
      (a+12*t)*channelHaarPair n cs b (fun z => polyMul (b z) f) := by
  let moment : RatPoly → Q' := fun z => H n (polyMul (b z) (polyMul (b z) f))
  have he := channelSum_congr
    (fun z => H n (polyMul (b z) (coercivitySquare active (b z) f a t)))
    (fun z => (a+12*t)*moment z) cs (by
    intro c hc
    have hi := casimir12_first_ibp n active hactive (b c.2) f (hb c hc) hf hCf
    have hm : H n (polyMul (b c.2) (polyMul (b c.2) f)) ≈
        H n (polyMul (polyMul (b c.2) (b c.2)) f) :=
      haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
    exact Q'.eqv_trans _ _ _
      (haar_pair_linear n (b c.2) (polyMul (b c.2) f)
        (activeGamma active (b c.2) f) (a-24*t) (6*t))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_refl ((a-24*t)*moment c.2))
        (Q'.mul_eqv_congr_left (6*t) _ _
          (Q'.eqv_trans _ _ _ hi (Q'.mul_eqv_congr_left 6 _ _ (Q'.eqv_symm hm)))))
        (poly_identity_of_normal_eq
          (.add (.mul (.add (.var 0) (.neg (.mul (.const 24) (.var 1)))) (.var 2))
            (.mul (.mul (.const 6) (.var 1)) (.mul (.const 6) (.var 2))))
          (.mul (.add (.var 0) (.mul (.const 12) (.var 1))) (.var 2))
          (by decide) (fun
            | 0 => a
            | 1 => t
            | _ => H n (polyMul (b c.2) (polyMul (b c.2) f))))))
  exact Q'.eqv_trans _ _ _ he (channelSum_smul moment (a+12*t) cs)

private theorem channel_residual (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (cs : List GramChannel)
    (b : RatPoly → RatPoly)
    (hb : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (b c.2))
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f))
    (a t : Q') :
    let Q := channelHaarPair n cs (fun z => polyMul (b z) f) (fun z => polyMul (b z) f)
    let G := channelSum cs (fun z => H n (polyMul (polyMul (b z) (b z)) (activeGamma active f f)))
    let B := channelSum cs (fun z => retainedSlackValue n active (b z) f)
    let s := fun z => coercivitySquare active (b z) f a t
    (a*a+24*a*t)*Q-6*t*(a*G-t*B) ≈
      channelHaarPair n cs s s+12*t*t*channelSum cs (fun z => H n (coercivityGram active (b z) f)) := by
  dsimp only
  let q : RatPoly → Q' := fun z => H n (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let g : RatPoly → Q' := fun z => H n (polyMul (polyMul (b z) (b z)) (activeGamma active f f))
  let r : RatPoly → Q' := fun z => retainedSlackValue n active (b z) f
  let e : RatPoly → Q' := fun z => H n (polyMul
    (coercivitySquare active (b z) f a t) (coercivitySquare active (b z) f a t))
  let y : RatPoly → Q' := fun z => H n (coercivityGram active (b z) f)
  let left : RatPoly → Q' := fun z => (a*a+24*a*t)*q z-6*t*(a*g z-t*r z)
  let expanded : RatPoly → Q' := fun z =>
    (a*a+24*a*t)*q z+(-(6*t))*(a*g z+(-t)*r z)
  have hlocal := channelSum_congr left (fun z => e z+12*t*t*y z) cs (fun c hc =>
    retained_coercivity_identity n active hactive (b c.2) f (hb c hc) hf hCf a t)
  have hshape := channelSum_congr left expanded cs (fun c _ =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 5) (.var 6)))))))
      (.add (.mul (.var 0) (.var 2))
        (.mul (.neg (.var 1)) (.add (.mul (.var 3) (.var 4)) (.mul (.neg (.var 5)) (.var 6)))))
      (by decide) (fun
        | 0 => a*a+24*a*t
        | 1 => 6*t
        | 2 => q c.2
        | 3 => a
        | 4 => g c.2
        | 5 => t
        | _ => r c.2))
  have hfold := Q'.eqv_trans _ _ _ hshape
    (Q'.eqv_trans _ _ _ (sum_linear cs q (fun z => a*g z+(-t)*r z) (a*a+24*a*t) (-(6*t)))
      (Q'.add_eqv_congr' (Q'.eqv_refl ((a*a+24*a*t)*channelSum cs q))
        (Q'.mul_eqv_congr_left (-(6*t)) _ _ (sum_linear cs g r a (-t)))))
  have hleft := Q'.eqv_trans _ _ _ hfold
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.neg (.var 2)) (.add (.mul (.var 3) (.var 4)) (.mul (.neg (.var 5)) (.var 6)))))
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 5) (.var 6)))))))
      (by decide) (fun
        | 0 => a*a+24*a*t
        | 1 => channelSum cs q
        | 2 => 6*t
        | 3 => a
        | 4 => channelSum cs g
        | 5 => t
        | _ => channelSum cs r))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hlocal
      (Q'.eqv_trans _ _ _ (channelSum_add e (fun z => 12*t*t*y z) cs)
        (Q'.add_eqv_congr' (Q'.eqv_refl (channelSum cs e))
          (channelSum_smul y (12*t*t) cs))))

/-- Connected channel coercivity with the SAME literal retained slack.
All rational a,t, signed sources, an empty list and zero mass are covered. -/
theorem connected_channel_coercivity (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (cs : List GramChannel)
    (hweights : ∀ c, c ∈ cs → (0 : Q') ≤ c.1) (b : RatPoly → RatPoly)
    (hb : ∀ c, c ∈ cs → SupportedQuaternionBlocks n (b c.2))
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f))
    (a t : Q') :
    let S := channelHaarPair n cs b b
    let M := channelHaarPair n cs b (fun z => polyMul (b z) f)
    let Q := channelHaarPair n cs (fun z => polyMul (b z) f) (fun z => polyMul (b z) f)
    let G := channelSum cs (fun z => H n (polyMul (polyMul (b z) (b z)) (activeGamma active f f)))
    let B := channelSum cs (fun z => retainedSlackValue n active (b z) f)
    6*t*S*(a*G-t*B)+144*t*t*M*M ≤ (a*a+24*a*t)*(S*Q-M*M) := by
  dsimp only
  let S := channelHaarPair n cs b b
  let M := channelHaarPair n cs b (fun z => polyMul (b z) f)
  let Q := channelHaarPair n cs (fun z => polyMul (b z) f) (fun z => polyMul (b z) f)
  let G := channelSum cs (fun z => H n (polyMul (polyMul (b z) (b z)) (activeGamma active f f)))
  let B := channelSum cs (fun z => retainedSlackValue n active (b z) f)
  let s := fun z => coercivitySquare active (b z) f a t
  let E := channelHaarPair n cs s s
  let Y := channelSum cs (fun z => H n (coercivityGram active (b z) f))
  have hS := channelHaarPair_self_nonnegative n cs hweights b hb
  have hY : (0 : Q') ≤ Y := sum_nonnegative _ cs hweights (fun c hc =>
    coercivityGram_nonnegative n active hactive (b c.2) f (hb c hc) hf)
  have hc : (0 : Q') ≤ 12*t*t := le_of_le_eqv
    (Q'.mul_nonneg 12 (t*t) (by decide) (SumOfSquares.q_mul_self_nonneg t))
    (Q'.eqv_symm (Q'.mul_assoc_eqv 12 t t))
  have hED : E ≤ E+12*t*t*Y := le_of_eqv_le
    (Q'.eqv_symm (QPoly.q_add_zero_eqv E))
    (Q'.add_le_add_left E 0 _ (Q'.mul_nonneg _ _ hc hY))
  have hcs := channelHaarPair_cauchySchwarz n cs hweights b s hb (fun c hmem =>
    supported_add (polySmul_supported (supported_polyMul (hb c hmem) hf) (a-24*t))
      (polySmul_supported (activeGamma_supported active hactive (hb c hmem) hf) (6*t)))
  have hm := channel_coercivity_mixed n active hactive cs b hb f hf hCf a t
  have hbound : ((a+12*t)*M)*((a+12*t)*M) ≤ S*((a*a+24*a*t)*Q-6*t*(a*G-t*B)) :=
    le_of_eqv_le (Q'.eqv_symm (qmul hm hm))
      (le_of_le_eqv (Q'.le_trans' _ _ _ hcs
        (Q'.mul_le_mul_of_nonneg_left _ _ S hED hS))
        (Q'.mul_eqv_congr_left S _ _
          (Q'.eqv_symm (channel_residual n active hactive cs b hb f hf hCf a t))))
  let c := 6*t*S*(a*G-t*B)-(a*a+24*a*t)*M*M
  have h := Q'.add_le_add_left c _ _ hbound
  let A : PolyExpr := .var 0
  let T : PolyExpr := .var 1
  let Se : PolyExpr := .var 2
  let Me : PolyExpr := .var 3
  let Qe : PolyExpr := .var 4
  let Ge : PolyExpr := .var 5
  let Be : PolyExpr := .var 6
  let K : PolyExpr := .add (.mul A A) (.mul (.mul (.const 24) A) T)
  let L : PolyExpr := .mul (.mul (.mul (.const 6) T) Se)
    (.add (.mul A Ge) (.neg (.mul T Be)))
  let Ce : PolyExpr := .add L (.neg (.mul (.mul K Me) Me))
  let V : PolyExpr := .mul (.add A (.mul (.const 12) T)) Me
  let env := fun | 0 => a | 1 => t | 2 => S | 3 => M | 4 => Q | 5 => G | _ => B
  have hl := poly_identity_of_normal_eq
    (.add Ce (.mul V V))
    (.add L (.mul (.mul (.mul (.mul (.const 144) T) T) Me) Me)) (by decide) env
  have hr := poly_identity_of_normal_eq
    (.add Ce (.mul Se (.add (.mul K Qe)
      (.neg (.mul (.mul (.const 6) T) (.add (.mul A Ge) (.neg (.mul T Be))))))))
    (.mul K (.add (.mul Se Qe) (.neg (.mul Me Me)))) (by decide) env
  exact le_of_eqv_le (Q'.eqv_symm hl) (le_of_le_eqv h hr)

#print axioms channelHaarPair
#print axioms channelHaarPair_self_nonnegative
#print axioms channelHaarPair_cauchySchwarz
#print axioms casimir12_first_ibp
#print axioms channel_coercivity_mixed
#print axioms connected_channel_coercivity

end YMGap.Continuum.SU2QuaternionChannelConnectedCoercivity
