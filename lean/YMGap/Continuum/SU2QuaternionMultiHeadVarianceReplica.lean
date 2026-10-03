/-
# Conditional variance after any finite number of original Haar heads

Two complete head slices are copied while all surviving coordinates are
shared.  Their weighted difference square integrates to twice the literal
unnormalized conditional variance determinant.  The actual square cone
certificate is integrated and transported, retaining EVERY surviving Haar
insertion.  Zero heads and zero surviving blocks are included.

This is a rank-one weighted Gram producer, not a rule inferring matrix
positivity from pointwise positivity or a supplied determinant inequality.
It gives no relative norm estimate, stationary normalization or scaling law.
-/

import YMGap.Continuum.SU2QuaternionConditionalVarianceReplica

namespace YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Insert unused blocks AFTER the specified heads, not after the tail.
The head padding is explicit, including for short monomial representatives. -/
private def insertMonomial : Nat → Nat → List Nat → List Nat
  | 0, extra, m => List.replicate (4*extra) 0 ++ m
  | heads+1, extra, m =>
      [exponentAt m 0, exponentAt m 1, exponentAt m 2, exponentAt m 3] ++
        insertMonomial heads extra (m.drop 4)

private def insertPolynomial (heads extra : Nat) (p : RatPoly) : RatPoly :=
  p.map fun t => (insertMonomial heads extra t.1, t.2)

/-- On `(x,y,z)`, this is the original `p(x,z)`, with only `y` unused. -/
def copy (heads : Nat) (p : RatPoly) : RatPoly :=
  insertPolynomial heads heads p

private theorem lift_map : ∀ (extra : Nat) (p : RatPoly),
    liftBoundary extra p =
      p.map (fun t => (List.replicate (4*extra) 0 ++ t.1, t.2))
  | 0, p => by
      simpa only [liftBoundary, Nat.mul_zero, List.replicate_zero,
        List.nil_append] using (List.map_id p).symm
  | extra+1, p => by
      rw [liftBoundary, lift_map]
      simp only [liftHead, List.map_map]
      apply List.map_congr_left
      intro t _
      rw [show 4*(extra+1) = 4*extra+1+1+1+1 by omega]
      rfl

private theorem mul_nil : ∀ a : List Nat, monoMul a [] = a
  | [] => rfl
  | _::_ => rfl

private theorem drop_mul : ∀ (count : Nat) (a b : List Nat),
    (monoMul a b).drop count = monoMul (a.drop count) (b.drop count)
  | 0, _, _ => rfl
  | count+1, [], b => rfl
  | count+1, a, [] => by
      rw [mul_nil, List.drop_nil, mul_nil]
  | count+1, _::a, _::b => drop_mul count a b

private theorem zeros_mul : ∀ (count : Nat) (a b : List Nat),
    monoMul (List.replicate count 0 ++ a) (List.replicate count 0 ++ b) =
      List.replicate count 0 ++ monoMul a b
  | 0, _, _ => rfl
  | count+1, a, b => by
      simp only [List.replicate_succ, List.cons_append, monoMul, Nat.add_zero]
      exact congrArg (List.cons 0) (zeros_mul count a b)

private theorem insert_mul : ∀ (heads extra : Nat) (a b : List Nat),
    insertMonomial heads extra (monoMul a b) =
      monoMul (insertMonomial heads extra a) (insertMonomial heads extra b)
  | 0, extra, a, b => (zeros_mul (4*extra) a b).symm
  | heads+1, extra, a, b => by
      simp only [insertMonomial, SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
        drop_mul, monoMul,
        List.cons_append, List.nil_append]
      exact congrArg (fun m =>
        (exponentAt a 0+exponentAt b 0)::
        (exponentAt a 1+exponentAt b 1)::
        (exponentAt a 2+exponentAt b 2)::
        (exponentAt a 3+exponentAt b 3)::m)
          (insert_mul heads extra (a.drop 4) (b.drop 4))

private theorem copy_mul (heads : Nat) (p q : RatPoly) :
    copy heads (polyMul p q) = polyMul (copy heads p) (copy heads q) := by
  simp only [copy, insertPolynomial, polyMul, List.map_flatMap,
    List.flatMap_map, List.map_map]
  apply congrArg (fun f : RatTerm → RatPoly => p.flatMap f)
  funext s
  apply congrArg (fun f : RatTerm → RatTerm => q.map f)
  funext t
  exact congrArg (fun m => (m,s.2*t.2)) (insert_mul heads heads s.1 t.1)

private theorem partial_insert (heads extra : Nat) (p : RatPoly) :
    partialHaarHead (insertPolynomial (heads+1) extra p) =
      insertPolynomial heads extra (partialHaarHead p) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      change partialHaarHeadTerm (insertMonomial (heads+1) extra t.1,t.2) :: _ =
        (insertMonomial heads extra (partialHaarHeadTerm t).1,
          (partialHaarHeadTerm t).2) :: _
      exact congrArg (List.cons _) ih

private theorem heads_insert : ∀ (heads extra : Nat) (p : RatPoly),
    partialHaarHeads heads (insertPolynomial heads extra p) =
      liftBoundary extra (partialHaarHeads heads p)
  | 0, extra, p => (lift_map extra p).symm
  | heads+1, extra, p => by
      simp only [partialHaarHeads, partial_insert]
      exact heads_insert heads extra (partialHaarHead p)

/-- The copied heads are integrated, while the second slice and all common
survivors are retained as literal polynomial variables. -/
theorem partial_copy (heads : Nat) (p : RatPoly) :
    partialHaarHeads heads (copy heads p) =
      liftBoundary heads (partialHaarHeads heads p) :=
  heads_insert heads heads p

private theorem heads_compose : ∀ (first second : Nat) (p : RatPoly),
    partialHaarHeads (first+second) p =
      partialHaarHeads second (partialHaarHeads first p)
  | 0, second, p => by simp only [Nat.zero_add, partialHaarHeads]
  | first+1, second, p => by
      rw [show first+1+second = (first+second)+1 by omega]
      exact heads_compose first second (partialHaarHead p)

/-- Both head slices are independent only in their copied coordinates.
The retained tail may occur jointly in BOTH factors. -/
theorem replica_product (heads : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (heads+heads)
        (polyMul (copy heads p) (liftBoundary heads q)))
      (polyMul (partialHaarHeads heads p) (partialHaarHeads heads q)) := by
  rw [heads_compose]
  have h := partialHaarHeads_congr heads (partialHaarHeads_mul_lift heads (copy heads p) q)
  rw [partial_copy] at h
  exact h.trans ((partialHaarHeads_congr heads (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((partialHaarHeads_mul_lift heads q (partialHaarHeads heads p)).trans
      (RatPolyCoeffEqv.mul_comm _ _)))

private theorem insert_length : ∀ (heads extra : Nat) (m : List Nat),
    (insertMonomial heads extra m).length = 4*heads+4*extra+(m.length-4*heads)
  | 0, _, _ => by simp only [insertMonomial, List.length_append,
      List.length_replicate, Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
  | heads+1, extra, m => by
      simp only [insertMonomial, List.length_append, List.length_cons,
        List.length_nil, insert_length, List.length_drop]
      omega

private theorem copy_supported (tail heads : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+heads) p) :
    SupportedQuaternionBlocks (tail+(heads+heads)) (copy heads p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  have := hp s hs
  change (insertMonomial heads heads s.1).length ≤ _
  rw [insert_length]
  omega

private theorem exponent_zeros_append : ∀ (count c : Nat) (m : List Nat),
    exponentAt (List.replicate count 0 ++ m) c =
      if c < count then 0 else exponentAt m (c-count)
  | 0, c, m => by simp only [List.replicate_zero, List.nil_append,
      Nat.not_lt_zero, if_false, Nat.sub_zero]
  | count+1, 0, _ => rfl
  | count+1, c+1, m => by
      change exponentAt (List.replicate count 0 ++ m) c = _
      rw [exponent_zeros_append]
      simp only [Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub]

private theorem insert_exponent : ∀ (heads extra : Nat) (m : List Nat) (c : Nat),
    exponentAt (insertMonomial heads extra m) c =
      if c < 4*heads then exponentAt m c
      else if c < 4*(heads+extra) then 0 else exponentAt m (c-4*extra)
  | 0, extra, m, c => by
      simp only [insertMonomial, Nat.mul_zero, Nat.not_lt_zero, if_false,
        Nat.zero_add, exponent_zeros_append]
  | heads+1, extra, m, c => by
      by_cases hc : c < 4
      · have hcases : c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;>
          simp only [insertMonomial, List.cons_append, List.nil_append,
            exponentAt, List.getD_cons_zero, List.getD_cons_succ]
        · rw [if_pos (show 0 < 4*(heads+1) by omega)]
        · rw [if_pos (show 1 < 4*(heads+1) by omega)]
        · rw [if_pos (show 2 < 4*(heads+1) by omega)]
        · rw [if_pos (show 3 < 4*(heads+1) by omega)]
      · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hc)
        subst c
        rw [Nat.add_comm 4 k]
        change exponentAt (insertMonomial heads extra (m.drop 4)) k = _
        rw [insert_exponent]
        by_cases hh : k < 4*heads
        · rw [if_pos hh,
            if_pos (show k+4 < 4*(heads+1) by omega), exponentAt_drop]
          exact congrArg (exponentAt m) (by omega)
        · rw [if_neg hh,
            if_neg (show ¬ k+4 < 4*(heads+1) by omega)]
          by_cases he : k < 4*(heads+extra)
          · rw [if_pos he,
              if_pos (show k+4 < 4*(heads+1+extra) by omega)]
          · rw [if_neg he,
              if_neg (show ¬ k+4 < 4*(heads+1+extra) by omega), exponentAt_drop]
            exact congrArg (exponentAt m) (by omega)

private def headSwap (tail heads : Nat) :
    QuaternionBlockInvolution (tail+(heads+heads)) where
  map i := if i < heads then heads+i else if i < heads+heads then i-heads else i
  map_lt := by
    intro i hi
    by_cases hfirst : i < heads
    · simp only [if_pos hfirst]
      omega
    · by_cases hsecond : i < heads+heads
      · simp only [if_neg hfirst, if_pos hsecond]
        omega
      · simp only [if_neg hfirst, if_neg hsecond]
        exact hi
  involutive := by
    intro i hi
    by_cases hfirst : i < heads
    · simp only [if_pos hfirst, if_neg (show ¬ heads+i < heads by omega),
        if_pos (show heads+i < heads+heads by omega)]
      omega
    · by_cases hsecond : i < heads+heads
      · simp only [if_neg hfirst, if_pos hsecond,
          if_pos (show i-heads < heads by omega)]
        omega
      · simp only [if_neg hfirst, if_neg hsecond]

private theorem copy_reindex_prefix (tail heads : Nat) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv (tail+(heads+heads))
      (reindexQuaternionPolynomial (headSwap tail heads) (liftBoundary heads p))
      (copy heads p)
  | [] => by
      simp only [lift_map, copy, insertPolynomial, reindexQuaternionPolynomial,
        List.map_nil]
      exact .nil
  | t::ts => by
      rw [lift_map]
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro c hc
        change exponentAt (reindexQuaternionExponents (headSwap tail heads)
          (List.replicate (4*heads) 0 ++ t.1)) c =
            exponentAt (insertMonomial heads heads t.1) c
        rw [exponentAt_reindexQuaternionExponents _ _ hc, insert_exponent,
          exponent_zeros_append]
        by_cases hfirst : c/4 < heads
        · have hm : (headSwap tail heads).map (c/4) = heads+c/4 := if_pos hfirst
          rw [hm, if_neg (by omega), if_pos (by omega)]
          exact congrArg (exponentAt t.1) (by omega)
        · by_cases hsecond : c/4 < heads+heads
          · have hm : (headSwap tail heads).map (c/4) = c/4-heads := by
              simp only [headSwap, if_neg hfirst, if_pos hsecond]
            rw [hm, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
          · have hm : (headSwap tail heads).map (c/4) = c/4 := by
              simp only [headSwap, if_neg hfirst, if_neg hsecond]
            rw [hm, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact congrArg (exponentAt t.1) (by omega)
      · simpa only [lift_map] using copy_reindex_prefix tail heads ts

private def copy_certificate (tail heads : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (P : Certificate (tail+heads) W) :
    Certificate (tail+(heads+heads)) (copy heads W) := by
  have hl : SupportedQuaternionBlocks (tail+(heads+heads)) (liftBoundary heads W) := by
    simpa only [Nat.add_assoc] using lift_supported hW heads
  have PL : Certificate (tail+(heads+heads)) (liftBoundary heads W) := by
    simpa only [Nat.add_assoc] using lift_certificate heads P
  exact .transport
    (carrierOfPrefix (reindex_supported (headSwap tail heads) _) (copy_supported tail heads hW)
      (copy_reindex_prefix tail heads W)).symm
    (reindex_certificate (headSwap tail heads) hl PL)

/-- The polynomial normalizer is retained without any reciprocal. -/
def determinant (heads : Nat) (W f : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (partialHaarHeads heads W)
      (partialHaarHeads heads (polyMul W (polyMul f f))))
    (polyNeg (polyMul (partialHaarHeads heads (polyMul W f))
      (partialHaarHeads heads (polyMul W f))))

def replicaDifference (heads : Nat) (f : RatPoly) : RatPoly :=
  polyAdd (copy heads f) (polyNeg (liftBoundary heads f))

def replicaEnergy (heads : Nat) (W f : RatPoly) : RatPoly :=
  polyMul (polyMul (copy heads W) (liftBoundary heads W))
    (polyMul (replicaDifference heads f) (replicaDifference heads f))

private theorem heads_add : ∀ (heads : Nat) (p q : RatPoly),
    partialHaarHeads heads (polyAdd p q) =
      polyAdd (partialHaarHeads heads p) (partialHaarHeads heads q)
  | 0, _, _ => rfl
  | heads+1, p, q => by simp only [partialHaarHeads, partialHaarHead_add, heads_add]

private theorem head_neg (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyNeg p)) (polyNeg (partialHaarHead p)) := by
  have ht : RatPolyTermwiseEqv
      (partialHaarHead (polyNeg p)) (polyNeg (partialHaarHead p)) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih => exact ⟨rfl,Q'.neg_mul_eqv _ _,ih⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

private theorem heads_neg : ∀ (heads : Nat) (p : RatPoly),
    RatPolyCoeffEqv (partialHaarHeads heads (polyNeg p))
      (polyNeg (partialHaarHeads heads p))
  | 0, _ => .refl _
  | heads+1, p =>
      (partialHaarHeads_congr heads (head_neg p)).trans
        (heads_neg heads (partialHaarHead p))

private def expansion (heads : Nat) (W f : RatPoly) : RatPoly :=
  let diagonal := polyMul W (polyMul f f)
  let cross := polyMul (copy heads (polyMul W f)) (liftBoundary heads (polyMul W f))
  polyAdd
    (polyAdd (polyMul (copy heads diagonal) (liftBoundary heads W))
      (polyMul (copy heads W) (liftBoundary heads diagonal)))
    (polyAdd (polyNeg cross) (polyNeg cross))

private theorem energy_expansion (heads : Nat) (W f : RatPoly) :
    RatPolyCoeffEqv (replicaEnergy heads W f) (expansion heads W f) := by
  dsimp only [replicaEnergy, replicaDifference, expansion]
  simp only [copy_mul, lift_product]
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 2) (.neg (.var 3)))))
    (.add
      (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3)))))
      (.add (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
        (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))))
    (by decide)
    (fun
      | 0 => copy heads W
      | 1 => liftBoundary heads W
      | 2 => copy heads f
      | _ => liftBoundary heads f)

/-- Exact multi-head replica identity, stronger than equality of the bare
integrals: every surviving polynomial insertion is retained. -/
theorem replica_identity (tail heads : Nat) (W f : RatPoly) :
    HaarCarrierEqv tail (partialHaarHeads (heads+heads) (replicaEnergy heads W f))
      (polyAdd (determinant heads W f) (determinant heads W f)) := by
  apply RatPolyCoeffEqv.haarCarrier
  refine (partialHaarHeads_congr (heads+heads) (energy_expansion heads W f)).trans ?_
  dsimp only [expansion]
  simp only [heads_add]
  have hc := (heads_neg (heads+heads) _).trans
    (RatPolyCoeffEqv.neg (replica_product heads (polyMul W f) (polyMul W f)))
  refine (RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.add (replica_product heads (polyMul W (polyMul f f)) W)
      (replica_product heads W (polyMul W (polyMul f f))))
    (RatPolyCoeffEqv.add hc hc)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
      (.add (.neg (.mul (.var 2) (.var 2))) (.neg (.mul (.var 2) (.var 2)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 2)))))
    (by decide)
    (fun
      | 0 => partialHaarHeads heads W
      | 1 => partialHaarHeads heads (polyMul W (polyMul f f))
      | _ => partialHaarHeads heads (polyMul W f))

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Computed original two-copy square certificate with the common tail
shared, not copied or independently averaged. -/
def replica_certificate (tail heads : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : Certificate (tail+heads) W) :
    Certificate (tail+(heads+heads)) (replicaEnergy heads W f) := by
  have PL : Certificate (tail+(heads+heads)) (liftBoundary heads W) := by
    simpa only [Nat.add_assoc] using lift_certificate heads P
  have hl : SupportedQuaternionBlocks (tail+(heads+heads)) (liftBoundary heads f) := by
    simpa only [Nat.add_assoc] using lift_supported hf heads
  exact .mul (.mul (copy_certificate tail heads W hW P) PL)
    (.square (replicaDifference heads f)
      (supported_add (copy_supported tail heads hf) (supported_neg hl)))

private theorem half_double (p : RatPoly) :
    RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_add weight p p))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves _)))

/-- Actual certificate for the unnormalized multi-head conditional variance.
There is no positive-normalizer inverse or output inequality premise. -/
def determinant_certificate (tail heads : Nat) (W f : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : Certificate (tail+heads) W) :
    Certificate tail (determinant heads W f) :=
  .ofCoeff (half_double _).symm
    (.smul HalfPow.half (by decide)
      (.transport (replica_identity tail heads W f).symm
        (partialHaarHeads_certificate tail (heads+heads)
          (replica_certificate tail heads W f hW hf P))))

/-- Any actual positive surrounding tail action can be inserted, without
an independence premise on surviving variables. -/
theorem spectator_nonnegative (tail heads : Nat) (W f R : RatPoly)
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : Certificate (tail+heads) W) (PR : Certificate tail R) :
    (0 : Q') ≤ quaternionHaar tail (polyMul R (determinant heads W f)) :=
  (PR.mul (determinant_certificate tail heads W f hW hf P)).haar_nonnegative

#print axioms partial_copy
#print axioms replica_product
#print axioms replica_identity
#print axioms replica_certificate
#print axioms determinant_certificate
#print axioms spectator_nonnegative

end YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
