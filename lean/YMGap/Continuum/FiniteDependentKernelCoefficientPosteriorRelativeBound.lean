/-
# Sum relative receiver-column bounds without a carrier-cardinality loss

The posterior-column `l1` budget is a finite sum over realized target
columns.  A uniform absolute bound per column would pay for the number of
columns, which grows with the slab.  The volume-safe input is instead
relative to the physical target weight of that column.

This module proves generic pointwise-to-aggregate compilers.  A
source-relative estimate on the unretained coefficient controls the signed
row defect by the total source weight.  A target-relative estimate on each
posterior column controls the posterior `l1` budget by the total target
weight.  Its preferred two-sector theorem also accepts those three aggregate
bounds directly.  Thus later Yang--Mills specializations can use exact finite
mass identities instead of carrier cardinality without requiring pointwise
control when only a sector total is needed.

No relative estimate is inhabited here.  This is exact finite rational
summation, not stochastic mixing, an asymptotic estimate, a continuum limit,
or a mass-gap theorem.

Constructive contract: exact finite rational inequalities only; no choice,
`Classical`, `native_decide`, proof hole, noncomputable declaration, or new
axiom.
-/

import YMGap.Continuum.FiniteDependentKernelCoefficientPosterior
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.FiniteDependentKernelCoefficientTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem abs_mul_nonnegative_left_eqv_local
    (weight value : Q') (hweight : (0 : Q') ≤ weight) :
    Q'.abs (weight * value) ≈ weight * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * weight)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv weight value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * weight) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hweight) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) weight

namespace FiniteDependentCoefficientTransport

variable {Source Target : Type} [DecidableEq Target]

/-- A pointwise bound on the coefficient carried by the unretained part of
each row sums against total source weight, with no source-cardinality factor. -/
theorem rowCoefficientDefect_abs_le_relativeSourceWeight
    (data : FiniteDependentCoefficientTransport Source Target)
    (relative : Q')
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hrelative : ∀ source, source ∈ data.sources →
      Q'.abs
          (data.sourceCoefficient source *
            ((1 : Q') + -data.rowMass source)) ≤ relative) :
    Q'.abs data.rowCoefficientDefect ≤
      relative * listQSum data.sourceWeight data.sources := by
  let residual := fun source =>
    data.sourceCoefficient source * ((1 : Q') + -data.rowMass source)
  have htriangle :
      Q'.abs data.rowCoefficientDefect ≤
        listQSum
          (fun source => Q'.abs (data.sourceWeight source * residual source))
          data.sources := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr data.rowCoefficientDefect_eqv_unretained))
      (abs_listQSum_le_sum_abs_local _ _)
  have htermwise :
      listQSum
          (fun source => Q'.abs (data.sourceWeight source * residual source))
          data.sources ≤
        listQSum
          (fun source => data.sourceWeight source * relative)
          data.sources := by
    apply listQSum_le_termwise_local
    intro source hsource
    refine Q'.le_trans'
      (Q'.abs (data.sourceWeight source * residual source))
      (data.sourceWeight source * Q'.abs (residual source))
      (data.sourceWeight source * relative)
      (Q'.le_of_eqv
        (abs_mul_nonnegative_left_eqv_local
          (data.sourceWeight source) (residual source)
          (hsourceWeight source hsource))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ (data.sourceWeight source)
      (by simpa only [residual] using hrelative source hsource)
      (hsourceWeight source hsource)
  have hfactor :
      listQSum
          (fun source => data.sourceWeight source * relative)
          data.sources ≈
        relative * listQSum data.sourceWeight data.sources := by
    refine Q'.eqv_trans _
      (listQSum
        (fun source => relative * data.sourceWeight source)
        data.sources) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact Q'.mul_comm_eqv (data.sourceWeight source) relative
    · exact listQSum_mul_left relative data.sourceWeight data.sources
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ htermwise (Q'.le_of_eqv hfactor))

/-- Target-weight-relative posterior errors sum against total target mass,
not the number of target columns. -/
theorem posteriorColumnCoefficientL1_le_relativeTargetWeight
    (data : FiniteDependentCoefficientTransport Source Target)
    (relative : Q')
    (hrelative : ∀ target, target ∈ data.targets →
      Q'.abs
          (data.transportedSourceCoefficientColumnMass target -
            data.targetWeight target * data.targetCoefficient target) ≤
        relative * data.targetWeight target) :
    data.posteriorColumnCoefficientL1 ≤
      relative * listQSum data.targetWeight data.targets := by
  unfold posteriorColumnCoefficientL1
  have hsum :
      listQSum
          (fun target =>
            Q'.abs
              (data.transportedSourceCoefficientColumnMass target -
                data.targetWeight target * data.targetCoefficient target))
          data.targets ≤
        listQSum
          (fun target => relative * data.targetWeight target)
          data.targets := by
    apply listQSum_le_termwise_local
    exact hrelative
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (listQSum_mul_left relative data.targetWeight data.targets))

/-- The row and posterior-column compilers combine without changing either
relative constant. -/
theorem rowAbs_add_posteriorColumnL1_le_relativeWeights
    (data : FiniteDependentCoefficientTransport Source Target)
    (rowRelative columnRelative : Q')
    (hsourceWeight : ∀ source, source ∈ data.sources →
      (0 : Q') ≤ data.sourceWeight source)
    (hrow : ∀ source, source ∈ data.sources →
      Q'.abs
          (data.sourceCoefficient source *
            ((1 : Q') + -data.rowMass source)) ≤ rowRelative)
    (hcolumn : ∀ target, target ∈ data.targets →
      Q'.abs
          (data.transportedSourceCoefficientColumnMass target -
            data.targetWeight target * data.targetCoefficient target) ≤
        columnRelative * data.targetWeight target) :
    Q'.abs data.rowCoefficientDefect + data.posteriorColumnCoefficientL1 ≤
      rowRelative * listQSum data.sourceWeight data.sources +
        columnRelative * listQSum data.targetWeight data.targets :=
  Q'.add_le_add
    (data.rowCoefficientDefect_abs_le_relativeSourceWeight
      rowRelative hsourceWeight hrow)
    (data.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hcolumn)

/-- Aggregate row and posterior-sector estimates pay their relative ceilings
against a common mass cap.  The two posterior sectors share one column
ceiling because only their combined target mass is charged. -/
theorem rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
    {ConnectedSource ConnectedTarget DisconnectedSource DisconnectedTarget : Type}
    [DecidableEq ConnectedTarget] [DecidableEq DisconnectedTarget]
    (connected :
      FiniteDependentCoefficientTransport ConnectedSource ConnectedTarget)
    (disconnected :
      FiniteDependentCoefficientTransport DisconnectedSource DisconnectedTarget)
    (rowRelative columnRelative massCap : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hrowBound :
      Q'.abs connected.rowCoefficientDefect ≤
        rowRelative * listQSum connected.sourceWeight connected.sources)
    (hconnectedBound :
      connected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum connected.targetWeight connected.targets)
    (hdisconnectedBound :
      disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative *
          listQSum disconnected.targetWeight disconnected.targets)
    (hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ massCap)
    (htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤ massCap) :
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        (rowRelative + columnRelative) * massCap := by
  have hrowScaled :
      rowRelative * listQSum connected.sourceWeight connected.sources ≤
        rowRelative * massCap :=
    Q'.mul_le_mul_of_nonneg_left _ _ rowRelative hsourceMass hrowRelative
  have hcolumns :
      connected.posteriorColumnCoefficientL1 +
          disconnected.posteriorColumnCoefficientL1 ≤
        columnRelative * massCap := by
    refine Q'.le_trans' _
      (columnRelative * listQSum connected.targetWeight connected.targets +
        columnRelative * listQSum disconnected.targetWeight
          disconnected.targets) _
      (Q'.add_le_add hconnectedBound hdisconnectedBound) ?_
    refine Q'.le_trans' _
      (columnRelative *
        (listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets)) _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_add_eqv columnRelative
            (listQSum connected.targetWeight connected.targets)
            (listQSum disconnected.targetWeight disconnected.targets)))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ columnRelative
      htargetMass hcolumnRelative
  refine Q'.le_trans' _
    (Q'.abs connected.rowCoefficientDefect +
      (connected.posteriorColumnCoefficientL1 +
        disconnected.posteriorColumnCoefficientL1)) _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        (Q'.abs connected.rowCoefficientDefect)
        connected.posteriorColumnCoefficientL1
        disconnected.posteriorColumnCoefficientL1)) ?_
  refine Q'.le_trans' _
    (rowRelative * massCap + columnRelative * massCap) _
    (Q'.add_le_add
      (Q'.le_trans' _ _ _ hrowBound hrowScaled) hcolumns) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.add_mul_eqv rowRelative columnRelative massCap))

/-- Pointwise source- and target-relative estimates compile to the weaker
aggregate interface, then pay the same common mass cap without a carrier
cardinality factor. -/
theorem rowAbs_add_twoPosteriorColumnL1_le_commonMassCap
    {ConnectedSource ConnectedTarget DisconnectedSource DisconnectedTarget : Type}
    [DecidableEq ConnectedTarget] [DecidableEq DisconnectedTarget]
    (connected :
      FiniteDependentCoefficientTransport ConnectedSource ConnectedTarget)
    (disconnected :
      FiniteDependentCoefficientTransport DisconnectedSource DisconnectedTarget)
    (rowRelative columnRelative massCap : Q')
    (hrowRelative : (0 : Q') ≤ rowRelative)
    (hcolumnRelative : (0 : Q') ≤ columnRelative)
    (hsourceWeight : ∀ source, source ∈ connected.sources →
      (0 : Q') ≤ connected.sourceWeight source)
    (hrow : ∀ source, source ∈ connected.sources →
      Q'.abs
          (connected.sourceCoefficient source *
            ((1 : Q') + -connected.rowMass source)) ≤ rowRelative)
    (hconnectedColumn : ∀ target, target ∈ connected.targets →
      Q'.abs
          (connected.transportedSourceCoefficientColumnMass target -
            connected.targetWeight target *
              connected.targetCoefficient target) ≤
        columnRelative * connected.targetWeight target)
    (hdisconnectedColumn : ∀ target, target ∈ disconnected.targets →
      Q'.abs
          (disconnected.transportedSourceCoefficientColumnMass target -
            disconnected.targetWeight target *
              disconnected.targetCoefficient target) ≤
        columnRelative * disconnected.targetWeight target)
    (hsourceMass :
      listQSum connected.sourceWeight connected.sources ≤ massCap)
    (htargetMass :
      listQSum connected.targetWeight connected.targets +
          listQSum disconnected.targetWeight disconnected.targets ≤ massCap) :
    (Q'.abs connected.rowCoefficientDefect +
        connected.posteriorColumnCoefficientL1) +
      disconnected.posteriorColumnCoefficientL1 ≤
        (rowRelative + columnRelative) * massCap := by
  have hrowBound :=
    connected.rowCoefficientDefect_abs_le_relativeSourceWeight
      rowRelative hsourceWeight hrow
  have hconnectedBound :=
    connected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hconnectedColumn
  have hdisconnectedBound :=
    disconnected.posteriorColumnCoefficientL1_le_relativeTargetWeight
      columnRelative hdisconnectedColumn
  exact connected.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
    disconnected rowRelative columnRelative massCap
    hrowRelative hcolumnRelative hrowBound hconnectedBound hdisconnectedBound
    hsourceMass htargetMass

end FiniteDependentCoefficientTransport

#print axioms FiniteDependentCoefficientTransport.rowCoefficientDefect_abs_le_relativeSourceWeight
#print axioms FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_le_relativeTargetWeight
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_posteriorColumnL1_le_relativeWeights
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap_of_aggregate
#print axioms FiniteDependentCoefficientTransport.rowAbs_add_twoPosteriorColumnL1_le_commonMassCap

end YMGap.Continuum.FiniteDependentKernelCoefficientTransport
