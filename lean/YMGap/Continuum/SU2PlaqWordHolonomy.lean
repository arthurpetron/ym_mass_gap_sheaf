/-
# The evaluated polynomial plaquette word is the torus holonomy

Companion to `SU2TorusMultiLinkPolyGibbs` (YM Group Realizer).  For a gauge
configuration `U : GaugeConfig SU2` and a finite link list `links`, the
environment `envOf links U` places `U ℓ` in block `links.idxOf ℓ`.  Then for
every plaquette whose four boundary links lie in `links`,

  `evalPolyQuaternion (envOf links U) (plaqWord links N p)`
    ≈ `(TorusWilsonAction.holonomy SU2 N U p).val`     (all four components),

hence `χ_s` of the word evaluates to `chi s (holonomy …)` (`eval_plaqCharacter_holonomy`).
-/

import YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

namespace YMGap.Continuum.SU2PlaqWordHolonomy

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg] <;>
             ac_rfl))

/-- Rational quaternion as an evaluated polynomial-quaternion value. -/
def toQV (x : RationalQuaternion) : QuaternionValue := ⟨x.r, x.i, x.j, x.k⟩

theorem qvEqv_trans {a b c : QuaternionValue} (h1 : QuaternionValue.Eqv a b)
    (h2 : QuaternionValue.Eqv b c) : QuaternionValue.Eqv a c :=
  ⟨Q'.eqv_trans _ _ _ h1.1 h2.1, Q'.eqv_trans _ _ _ h1.2 h2.2,
   Q'.eqv_trans _ _ _ h1.3 h2.3, Q'.eqv_trans _ _ _ h1.4 h2.4⟩

private theorem qmul {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha) (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem qadd {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.add_eqv_congr' ha hb

private theorem qneg {a a' : Q'} (ha : a ≈ a') : -a ≈ -a' := Q'.neg_eqv_congr _ _ ha

theorem qv_mul_congr {q q' r r' : QuaternionValue} (hq : QuaternionValue.Eqv q q')
    (hr : QuaternionValue.Eqv r r') :
    QuaternionValue.Eqv (QuaternionValue.mul q r) (QuaternionValue.mul q' r') :=
  ⟨qadd (qmul hq.1 hr.1) (qneg (qadd (qmul hq.2 hr.2) (qadd (qmul hq.3 hr.3) (qmul hq.4 hr.4)))),
   qadd (qmul hq.1 hr.2) (qadd (qmul hq.2 hr.1) (qadd (qmul hq.3 hr.4) (qneg (qmul hq.4 hr.3)))),
   qadd (qmul hq.1 hr.3) (qadd (qmul hq.3 hr.1) (qadd (qmul hq.4 hr.2) (qneg (qmul hq.2 hr.4)))),
   qadd (qmul hq.1 hr.4) (qadd (qmul hq.4 hr.1) (qadd (qmul hq.2 hr.3) (qneg (qmul hq.3 hr.2))))⟩

theorem qv_conj_congr {q q' : QuaternionValue} (hq : QuaternionValue.Eqv q q') :
    QuaternionValue.Eqv (QuaternionValue.conj q) (QuaternionValue.conj q') :=
  ⟨hq.1, qneg hq.2, qneg hq.3, qneg hq.4⟩

/-- Hamilton product agreement (association only). -/
theorem toQV_mul (x y : RationalQuaternion) :
    QuaternionValue.Eqv (QuaternionValue.mul (toQV x) (toQV y)) (toQV (RationalQuaternion.mul x y)) :=
  ⟨by simp only [QuaternionValue.mul, toQV, RationalQuaternion.mul]; ring_qeqv,
   by simp only [QuaternionValue.mul, toQV, RationalQuaternion.mul]; ring_qeqv,
   by simp only [QuaternionValue.mul, toQV, RationalQuaternion.mul]; ring_qeqv,
   by simp only [QuaternionValue.mul, toQV, RationalQuaternion.mul]; ring_qeqv⟩

theorem toQV_conj (x : RationalQuaternion) :
    QuaternionValue.conj (toQV x) = toQV (RationalQuaternion.conj x) := rfl

/-- Coordinate `c` of a rational quaternion. -/
def coord (c : Nat) (x : RationalQuaternion) : Q' :=
  if c = 0 then x.r else if c = 1 then x.i else if c = 2 then x.j else x.k

/-- Environment placing `U ℓ` in block `links.idxOf ℓ`. -/
def envOf (links : List Z4Link) (U : TorusWilsonAction.GaugeConfig SU2TorusWilsonGibbs.SU2)
    (i : Nat) : Q' :=
  match links[i / 4]? with
  | some ℓ => coord (i % 4) (U ℓ).val
  | none => 0

theorem getElem?_idxOf {ℓ : Z4Link} : ∀ {l : List Z4Link}, ℓ ∈ l → l[l.idxOf ℓ]? = some ℓ
  | [], h => absurd h (by simp)
  | b :: l, h => by
      rw [List.idxOf_cons]
      by_cases hb : b = ℓ
      · subst hb; simp
      · have hm : ℓ ∈ l := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hb
          · exact h
        have : (b == ℓ) = false := by simpa using hb
        rw [this]
        simpa using getElem?_idxOf hm

theorem eval_linkVar (links : List Z4Link) (U : TorusWilsonAction.GaugeConfig SU2TorusWilsonGibbs.SU2)
    {ℓ : Z4Link} (hℓ : ℓ ∈ links) :
    QuaternionValue.Eqv (evalPolyQuaternion (envOf links U) (linkVar links ℓ)) (toQV (U ℓ).val) := by
  have hk := getElem?_idxOf hℓ
  have e : ∀ c, c < 4 → envOf links U (4 * links.idxOf ℓ + c) = coord c (U ℓ).val := by
    intro c hc
    unfold envOf
    rw [show (4 * links.idxOf ℓ + c) / 4 = links.idxOf ℓ by omega,
      show (4 * links.idxOf ℓ + c) % 4 = c by omega, hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (by
      rw [show 4 * links.idxOf ℓ = 4 * links.idxOf ℓ + 0 by rfl, e 0 (by decide)]; exact Q'.eqv_refl _)
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (by rw [e 1 (by decide)]; exact Q'.eqv_refl _)
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (by rw [e 2 (by decide)]; exact Q'.eqv_refl _)
  · exact Q'.eqv_trans _ _ _ (evalRatPoly_var _ _) (by rw [e 3 (by decide)]; exact Q'.eqv_refl _)

/-- The four boundary links of `p` are in `links`. -/
def LinksCover (links : List Z4Link) (N : Nat) (p : Z4Plaq) : Prop :=
  (p.1, (dirsOf p.2).1) ∈ links ∧ (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2) ∈ links ∧
  (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1) ∈ links ∧ (p.1, (dirsOf p.2).2) ∈ links

/-- **Evaluated plaquette word = holonomy** (all four components). -/
theorem eval_plaqWord (links : List Z4Link) (N : Nat)
    (U : TorusWilsonAction.GaugeConfig SU2TorusWilsonGibbs.SU2) (p : Z4Plaq)
    (hc : LinksCover links N p) :
    QuaternionValue.Eqv (evalPolyQuaternion (envOf links U) (plaqWord links N p))
      (toQV (TorusWilsonAction.holonomy SU2TorusWilsonGibbs.SU2 N U p).val) := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold plaqWord
  refine qvEqv_trans (evalPolyQuaternion_mul _ _ _) ?_
  refine qvEqv_trans (qv_mul_congr (evalPolyQuaternion_mul _ _ _)
    (evalPolyQuaternion_mul _ _ _)) ?_
  refine qvEqv_trans (qv_mul_congr
    (qv_mul_congr (eval_linkVar links U h1) (eval_linkVar links U h2))
    (qv_mul_congr
      (qvEqv_trans (evalPolyQuaternion_conj _ _)
        (qv_conj_congr (eval_linkVar links U h3)))
      (qvEqv_trans (evalPolyQuaternion_conj _ _)
        (qv_conj_congr (eval_linkVar links U h4))))) ?_
  rw [toQV_conj, toQV_conj]
  refine qvEqv_trans (qv_mul_congr (toQV_mul _ _) (toQV_mul _ _)) ?_
  exact toQV_mul _ _

/-- Characters of the evaluated word are the Gibbs file's `chi` of the holonomy. -/
theorem eval_plaqCharacter_holonomy (links : List Z4Link) (N : Nat)
    (U : TorusWilsonAction.GaugeConfig SU2TorusWilsonGibbs.SU2) (p : Z4Plaq)
    (hc : LinksCover links N p) (s : Nat) :
    (evalRatPoly (envOf links U) (plaqCharacter links N p s)) ≈
      SU2TorusWilsonGibbs.chi s (TorusWilsonAction.holonomy SU2TorusWilsonGibbs.SU2 N U p) :=
  Q'.eqv_trans _ _ _ (eval_plaqCharacter _ links N p s)
    (SU2TorusWilsonGibbs.chebU_congr (eval_plaqWord links N U p hc).1 s)

end YMGap.Continuum.SU2PlaqWordHolonomy

#print axioms YMGap.Continuum.SU2PlaqWordHolonomy.eval_plaqWord
#print axioms YMGap.Continuum.SU2PlaqWordHolonomy.eval_plaqCharacter_holonomy
