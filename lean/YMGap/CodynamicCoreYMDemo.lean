/-
# Codynamic core — a YM-flavored instantiation over the constructive rationals

Where `CodynamicCoreTest.lean` exercises the fold on a toy `Nat` order,
this file instantiates the SAME tools over the repo's *real* constructive
cost `Q'` (via `qCosts`), with:

* a genuine `Q'`-valued metric model (`qM`), and
* a genuine **linear RG damping modulus** `scale Z = μ·Z` (μ ≥ 0) as the
  `Lipschitz` control — the multiplicative `L·(−)` contraction the paper's
  metric layer prices, discharged by the repo's `Q'.mul_le_mul_of_nonneg_*`.

`nstep_d` then produces a *real `Q'`-order* Grönwall certificate, showing
the tools apply to the constructive-analysis substrate the YM proof uses,
not only to a toy.

The final `example` records that the RG η-model monotonicity
(`RG.etaModel_mono`, the block-spin `Z_t ↦ η_max` packaging) has *exactly*
the shape of the codynamic monotone-modulus law `Lipschitz.scale_mono` on
the physical cone `[0,1)` — i.e. a real YM RG modulus is an instance of the
abstraction these tools consume.  (It cannot fill `scale_mono`
unconditionally because η is monotone only on `[0,1)`; the linear modulus
above is the total instance actually plugged into the pipeline.)
-/
import YMGap.CodynamicCore
import YMGap.RG.EtaPackaging

namespace YMGap.CodynamicCore.YMDemo

open YMGap.CodynamicCore
open YMGap.Constructive

/-- A one-symbol, one-color signature (a unary block map). -/
abbrev cc : Fin 1 := ⟨0, by decide⟩
abbrev bOp : Fin 1 := ⟨0, by decide⟩

abbrev SgB : Signature 1 := ⟨1, fun _ => ⟨[cc], cc⟩⟩
abbrev DB : TypedSet 1 := ⟨1, fun _ => cc⟩

/-- Extract the single argument of a unary tuple (free length index). -/
def qHead : {w : List (Color 1)} → All (fun _ : Color 1 => Q') w → Q'
  | [], .nil => 0
  | _ :: _, .cons x _ => x

/-- A `Q'`-valued metric model over `qCosts`: the block map halves the
state; the metric is the trivial (zero) pseudometric, whose four laws are
concrete `Q'` order facts. -/
abbrev qM : MetricVal SgB DB qCosts where
  Val := fun _ => Q'
  point := fun _ => 0
  interp := fun _ args => Q'.mkPos 1 2 (by decide) * qHead args
  d := fun _ _ => 0
  d_refl := fun _ => by decide
  d_sym := fun _ _ => by decide
  triangle := fun _ _ _ => by decide
  nonneg := fun _ _ => by decide

/-- The RG damping factor `μ = 3/4` (a κ_{SU(2)}-flavored contraction). -/
abbrev muDamp : Q' := Q'.mkPos 3 4 (by decide)

theorem muDamp_nonneg : (0 : Q') ≤ muDamp := by decide

/-- The **linear RG modulus** `scale Z = μ·Z` as a codynamic `Lipschitz`
control: monotone (by `mul_le_mul_of_nonneg_left`), total on all of `Q'`. -/
abbrev qL : Lipschitz qM where
  scale := fun _ Z => muDamp * Z
  scale_mono := by
    intro _ a b h
    exact Q'.mul_le_mul_of_nonneg_left a b muDamp h muDamp_nonneg
  scale_zero := fun _ => Q'.mul_nonneg muDamp 0 muDamp_nonneg (by decide)
  lip := fun _ xs ys =>
    Q'.mul_nonneg muDamp (dAll qM xs ys) muDamp_nonneg (dAll_nonneg qM xs ys)

/-- A two-step block-map trajectory. -/
def bStep : Step qM cc :=
  { rule := bOp, pos := Pos.phere, sides := All.cons (0 : Q') All.nil }

def bTraj : Traj qM cc cc :=
  Traj.tcons { step := bStep, recVal := (0 : Q') }
    (Traj.tcons { step := bStep, recVal := (0 : Q') } Traj.tnil)

/-- **The tools apply over the real constructive cost `Q'`**: `nstep_d`
yields a `Q'`-order Grönwall certificate for the block-map trajectory. -/
example :
    qCosts.le (qM.d (run qM (0 : Q') bTraj) (endRec qM (0 : Q') bTraj))
      (nBound qM qL (0 : Q') (0 : Q') bTraj) :=
  nstep_d qM qL (0 : Q') (0 : Q') (0 : Q') (by decide) bTraj

/-- The block-map defect certificate (`deriv_d` shape) also instantiates
over `Q'` through the priced-completion layer is available; here we record
the trajectory `nBound_mono` over `Q'`. -/
example {b b' : Q'} (h : qCosts.le b b') :
    qCosts.le (nBound qM qL b (0 : Q') bTraj) (nBound qM qL b' (0 : Q') bTraj) :=
  nBound_mono qM qL (0 : Q') bTraj h

/-- **A real YM RG modulus fits the codynamic monotone-modulus law.**  The
block-spin η-model `RG.etaModel μ` is monotone in `Z` on the convergence
cone `1 − Z' > 0` — precisely the `Lipschitz.scale_mono` obligation
(`qCosts.le` = `Q'.le`) that the tools consume, witnessed here by the
proven `RG.etaModel_mono`. -/
example {μ Z Z' : Q'} (hμ : (0 : Q') ≤ μ) (hZ : (0 : Q') ≤ Z)
    (hZZ' : Z ≤ Z') (hpos' : (0 : Q') < (1 : Q') - Z') :
    qCosts.le (RG.etaModel μ Z) (RG.etaModel μ Z') :=
  RG.etaModel_mono hμ hZ hZZ' hpos'

#print axioms qM
#print axioms qL

end YMGap.CodynamicCore.YMDemo
