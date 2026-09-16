/-
# Supported certificates on a larger quaternion-Haar carrier

A supported one-slice message may be used on the head of a pair carrier.
The support guard is essential: arbitrary-insertion Haar equality on a
smaller carrier can otherwise discard genuine off-carrier exponents.

The explicit tail marginal retains the full Haar moment of the discarded
exponents, including its out-of-carrier zero branch. Finite Fubini therefore
extends carrier equality between supported polynomials. Certificate recursion
first constructs a supported square representative, so no support of an
intermediate transport node is assumed. No analytic positivity premise,
stationary law or OS identification is introduced.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionHaarHeadFubini
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionHaarCertificateExtension

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem exponent_take (m : List Nat) : ∀ n i, i < n →
    exponentAt (m.take n) i = exponentAt m i
  | 0, _, h => by omega
  | n+1, 0, _ => by cases m <;> rfl
  | n+1, i+1, h => by
      cases m with
      | nil => rfl
      | cons a m => exact exponent_take m n i (by omega)

private theorem headMoment_take (keep : Nat) (m : List Nat) :
    headQuaternionMoment (m.take (keep+4)) = headQuaternionMoment m := by
  unfold headQuaternionMoment
  rw [exponent_take m _ 0 (by omega), exponent_take m _ 1 (by omega),
    exponent_take m _ 2 (by omega), exponent_take m _ 3 (by omega)]

private theorem take_drop_n : ∀ (count keep : Nat) (m : List Nat),
    (m.take (keep+count)).drop count = (m.drop count).take keep
  | 0, _, _ => rfl
  | _+1, _, [] => by simp only [List.take_nil, List.drop_nil]
  | count+1, keep, _::m => take_drop_n count keep m

/-- Raw monomial Fubini preserves the entire tail beyond both carriers. -/
theorem haarMono_split (blocks extra : Nat) (m : List Nat) :
    quaternionHaarMono blocks (m.take (4*blocks)) *
        quaternionHaarMono extra (m.drop (4*blocks)) ≈
      quaternionHaarMono (blocks+extra) m := by
  induction blocks generalizing m with
  | zero =>
      simp only [Nat.mul_zero, List.take_zero, List.drop_zero, Nat.zero_add]
      change (1 : Q') * quaternionHaarMono extra m ≈ quaternionHaarMono extra m
      exact Q'.one_mul_eqv _
  | succ blocks ih =>
      have hs := headMoment_mul_tailHaarMono blocks (m.take (4*(blocks+1)))
      have hfour : 4*(blocks+1) = 4*blocks+4 := by omega
      rw [hfour, headMoment_take, take_drop_n] at hs
      have hd : (m.drop 4).drop (4*blocks) = m.drop (4*(blocks+1)) := by
        rw [List.drop_drop]
        congr 1
        omega
      have hn : blocks+1+extra = (blocks+extra)+1 := by omega
      rw [hn, ← hd]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hs))
        (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ih (m.drop 4)))
            (headMoment_mul_tailHaarMono (blocks+extra) m)))

/-- Integrate the appended blocks, also killing any exponent beyond them.
This is Haar marginalization, not truncation or evaluation at a point. -/
def tailMarginal (blocks extra : Nat) (p : RatPoly) : RatPoly :=
  p.map fun t => (t.1.take (4*blocks),
    t.2 * quaternionHaarMono extra (t.1.drop (4*blocks)))

theorem tailMarginal_supported (blocks extra : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (tailMarginal blocks extra p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  exact List.length_take_le _ _

/-- Exact total Haar pin, without a support hypothesis on the input. -/
theorem haar_tailMarginal (blocks extra : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (tailMarginal blocks extra p) ≈
      quaternionHaar (blocks+extra) p
  | [] => Q'.eqv_refl _
  | t::p => by
      change (t.2 * quaternionHaarMono extra (t.1.drop (4*blocks))) *
          quaternionHaarMono blocks (t.1.take (4*blocks)) +
          quaternionHaar blocks (tailMarginal blocks extra p) ≈
        t.2 * quaternionHaarMono (blocks+extra) t.1 +
          quaternionHaar (blocks+extra) p
      refine Q'.add_eqv_congr' ?_ (haar_tailMarginal blocks extra p)
      exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (haarMono_split blocks extra t.1)))

private theorem mono_nil : ∀ m : List Nat, monoMul m [] = m
  | [] => rfl
  | _::_ => rfl

private theorem mono_take : ∀ (n : Nat) (a b : List Nat),
    (monoMul a b).take n = monoMul (a.take n) (b.take n)
  | 0, _, _ => rfl
  | n+1, [], b => by simp [monoMul]
  | n+1, a, [] => by rw [mono_nil, List.take_nil, mono_nil]
  | n+1, _::a, _::b => by simp only [monoMul, List.take_succ_cons, mono_take n a b]

private theorem map_coeff_mem {A : Type} (f g : A → RatTerm) :
    ∀ xs : List A,
    (∀ a, a ∈ xs → (f a).1 = (g a).1 ∧ (f a).2 ≈ (g a).2) →
      RatPolyCoeffEqv (xs.map f) (xs.map g)
  | [], _ => RatPolyCoeffEqv.refl _
  | a::xs, h => by
      intro weight
      change (f a).2 * weight (f a).1 + ratWeightedSum weight (xs.map f) ≈
        (g a).2 * weight (g a).1 + ratWeightedSum weight (xs.map g)
      rw [(h a List.mem_cons_self).1]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (h a List.mem_cons_self).2)
        (map_coeff_mem f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)) weight)

private theorem mul_swap (a b c : Q') : (a*b)*c ≈ (a*c)*b :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

/-- A supported head factor pulls out of the appended-block marginal. -/
theorem tailMarginal_mul (blocks extra : Nat) : ∀ (r p : RatPoly),
    SupportedQuaternionBlocks blocks p →
    RatPolyCoeffEqv (tailMarginal blocks extra (polyMul r p))
      (polyMul (tailMarginal blocks extra r) p)
  | [], _, _ => RatPolyCoeffEqv.refl _
  | a::r, p, hp => by
      simp only [tailMarginal, polyMul, List.flatMap_cons, List.map_append,
        List.map_cons, List.map_map]
      refine (map_coeff_mem _ _ p ?_).add ?_
      · intro b hb
        have hs := hp b hb
        constructor
        · change (monoMul a.1 b.1).take (4*blocks) =
            monoMul (a.1.take (4*blocks)) b.1
          rw [mono_take, List.take_of_length_le hs]
        · change (a.2*b.2) * quaternionHaarMono extra
              ((monoMul a.1 b.1).drop (4*blocks)) ≈
            (a.2 * quaternionHaarMono extra (a.1.drop (4*blocks))) * b.2
          rw [monoMul_drop_of_right_length_le a.1 b.1 (4*blocks) hs]
          exact mul_swap _ _ _
      · simpa only [tailMarginal, polyMul, List.map_map] using
          tailMarginal_mul blocks extra r p hp

/-- Arbitrary insertions are contracted, while the supported message is fixed. -/
theorem tail_pairing (blocks extra : Nat) (insertion p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    quaternionHaar (blocks+extra) (polyMul insertion p) ≈
      quaternionHaar blocks (polyMul (tailMarginal blocks extra insertion) p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_tailMarginal blocks extra _))
    (haar_of_coeff (tailMarginal_mul blocks extra insertion p hp))

/-- Support of BOTH sides permits extension of arbitrary-insertion equality. -/
theorem carrier_extend {blocks : Nat} (extra : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) : HaarCarrierEqv (blocks+extra) p q := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (tail_pairing blocks extra insertion p hp)
    (Q'.eqv_trans _ _ _ (h (tailMarginal blocks extra insertion))
      (Q'.eqv_symm (tail_pairing blocks extra insertion q hq)))

private theorem support_extend {blocks : Nat} (extra : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks (blocks+extra) p := by
  intro t ht
  have h := hp t ht
  omega

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private structure ExtensionRepresentative (blocks extra : Nat) (p : RatPoly) where
  polynomial : RatPoly
  supported : SupportedQuaternionBlocks blocks polynomial
  certificate : Certificate (blocks+extra) polynomial
  pin : HaarCarrierEqv blocks p polynomial

/-- Recursion retains supported square data even across unsupported transport nodes. -/
private def representative (blocks extra : Nat) :
    {p : RatPoly} → Certificate blocks p → ExtensionRepresentative blocks extra p
  | _, .square p hp =>
      ⟨polyMul p p, supported_polyMul hp hp,
        .square p (support_extend extra hp), .refl _ _⟩
  | _, .add P Q =>
      let r := representative blocks extra P
      let s := representative blocks extra Q
      ⟨polyAdd r.polynomial s.polynomial, supported_add r.supported s.supported,
        .add r.certificate s.certificate, HaarCarrierEqv.add r.pin s.pin⟩
  | _, .smul c hc P =>
      let r := representative blocks extra P
      ⟨polySmul c r.polynomial, support_smul r.supported c,
        .smul c hc r.certificate, HaarCarrierEqv.smul c r.pin⟩
  | _, .transport h P =>
      let r := representative blocks extra P
      ⟨r.polynomial, r.supported, r.certificate, h.trans r.pin⟩

/-- Extend a genuinely supported certified message to a larger head carrier.
Only the final polynomial needs support; intermediate certificate transports
are handled by the explicit supported representative above. -/
def certificate_extend {blocks : Nat} (extra : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (P : Certificate blocks p) :
    Certificate (blocks+extra) p :=
  let r := representative blocks extra P
  .transport (carrier_extend extra hp r.supported r.pin) r.certificate

end YMGap.Continuum.SU2QuaternionHaarCertificateExtension

#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.haarMono_split
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tailMarginal
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tailMarginal_supported
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.haar_tailMarginal
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tailMarginal_mul
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.tail_pairing
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.carrier_extend
#print axioms YMGap.Continuum.SU2QuaternionHaarCertificateExtension.certificate_extend
