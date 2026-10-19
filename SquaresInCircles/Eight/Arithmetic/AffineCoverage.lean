module

public import SquaresInCircles.Eight.Arithmetic.StateCoverage
public import SquaresInCircles.Eight.Candidate.GeometricCoreQuarter

/-!
# Eight squares: the charged bound of an affine table

`AffineCover.chargedBoundOf` turns an affine table, whose quarters and charges are those of the
candidate, into the charged bound `Candidate.ChargedBound` of every boundary cycle at its level
whose signed tangents lie in the cuts, whose frame differences lie in the ranges and whose
separating forward axes are allowed by the table. The state chains give each square one arc, and
so one label for both of its edges, before any axis is chosen (`StateChains.covers`). For every
forward axis that separates the two squares of an edge, a row of the two arcs, the axis and the
half of the edge whose angle interval contains `u = |δ|` gives the charged inequality of the edge
(`pairBound`), and two facts provide such a row. First, `u` lies in the required interval of the
two arcs (`AffineCover.required_mem`): the gap between the centre directions lies in
`(19/25, 710/113 - 114/25)`, the arctangents of the signed tangents lie in the intervals of the
arcs (`EndpointsValid`), and `u < 7/10`. Second, the rows cover every required interval
(`AngleCovers`), as `RowCover.lean` checks.

No row is needed for an arc pair and an axis that never separates two squares on these arcs
(`ExcludedArcs`, `feasible_not_excluded`): on an edge of quarter zero the axis two with a core
target and the axis four with a core source, on any edge the axis one with a core target and a
source of sign `-1` and the axis three with a core source and a target of sign `+1`, and on an
edge of quarter one every axis from a core source of sign `+1` to a core target of sign `-1`. With
`core` no row is needed for two core arcs either, whose costs are bounded otherwise
(`CorePairBound`): by the markers of `Candidate/GeometricCoreMarker.lean`, or vacuously when no
edge joins two core squares (`NoAdjacentCore.corePairBound`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Arithmetic

instance : Inhabited QInterval := ⟨⟨0,0⟩⟩

/-- The intersection of two intervals. -/
def QInterval.inter (I J : QInterval) : QInterval := ⟨max I.lo J.lo,min I.hi J.hi⟩
theorem QInterval.mem_inter {I J : QInterval} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) :
    (I.inter J).Mem x := by
  constructor
  · rcases le_total I.lo J.lo with h | h
    · simpa [QInterval.inter,max_eq_right h] using hJ.1
    · simpa [QInterval.inter,max_eq_left h] using hI.1
  · rcases le_total I.hi J.hi with h | h
    · simpa [QInterval.inter,min_eq_left h] using hI.2
    · simpa [QInterval.inter,min_eq_right h] using hJ.2

/-- The forward axis of number `i` in `forwardAxis`, from zero. -/
def ForwardAxis.ofIndex (i : Fin 4) : ForwardAxis := ![.one,.two,.three,.four] i
@[simp] theorem ForwardAxis.index_ofIndex (i : Fin 4) : (ForwardAxis.ofIndex i).index=i := by
  fin_cases i <;> rfl

/-- The margins depend on the signs only through the products `σ b` and `τ B`. -/
theorem forwardMargin_congr_products (axis : ForwardAxis) {σ τ σ' τ' a b A B φ : ℝ}
    (hs : σ*b=σ'*b) (ht : τ*B=τ'*B) :
    forwardMargin axis σ τ a b A B φ=forwardMargin axis σ' τ' a b A B φ := by
  cases axis <;> simp only [forwardMargin,hs,ht]

/-- An arc pair and a forward axis that never separates two squares on these arcs
(`feasible_not_excluded`): on an edge of quarter zero, the axis two with a core target or the axis
four with a core source; on any edge, the axis one with a core target and a source of sign `-1`,
or the axis three with a core source and a target of sign `+1`; on an edge of quarter one, every
axis from a core source of sign `+1` to a core target of sign `-1`. -/
def ExcludedArcs (aS aT : ArcData) (axis : ForwardAxis) : Prop :=
  (aS.role ∈ Candidate.zeroEdges ∧
    ((axis = .two ∧ aT.outer = false) ∨ (axis = .four ∧ aS.outer = false))) ∨
  (axis = .one ∧ aS.positive = false ∧ aT.outer = false) ∨
  (axis = .three ∧ aT.positive = true ∧ aS.outer = false) ∨
  (Candidate.word aS.role = 1 ∧ aS.outer = false ∧ aT.outer = false ∧ aS.positive = true ∧
    aT.positive = false)

/-- A core arc has primary coordinate at most `7/12`. -/
theorem arc_core_primary_upper {s : ArcData} {Q a b : ℝ}
    (hs : s.Contains Q a b) (hcore : s.outer = false) : a ≤ 7/12 := by
  have hc := hs.2.2.2.2
  by_cases hside : s.tangent.hi ≤ 6/7
  · simp [ArcData.OnCurve, hcore, hside] at hc
    exact hc.1.le
  · simp [ArcData.OnCurve, hcore, hside] at hc
    by_contra! ha
    nlinarith [sq_nonneg (a-7/12), sq_nonneg (b-1/2)]

/-- A forward axis that separates two consecutive squares of a cycle is not excluded for arcs
that contain their states with the same products `σ b`. -/
theorem feasible_not_excluded {M : AffineTableMeta}
    (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C)
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role = i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i = C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i) = C.sigma (next i)*C.b (next i))
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ¬ ExcludedArcs (arcAt M s) (arcAt M t) (ForwardAxis.ofIndex j) := by
  intro hexcluded
  rcases hexcluded with hprimary | ⟨haxis,hnegative,hcore⟩ | ⟨haxis,hpositive,hcore⟩ |
    ⟨hk, hsc, htc, hsp, htn⟩
  · rcases hprimary with ⟨hi, ⟨haxis,hcore⟩ | ⟨haxis,hcore⟩⟩
    · have hi' : i ∈ Candidate.zeroEdges := by simpa [hsi] using hi
      have hji : j = 1 := by fin_cases j <;> simp_all [ForwardAxis.ofIndex]
      subst j
      have hlarge := (Candidate.Geometric.zero_target_primary_requires_outer F hi' hj).2
      have hsmall := arc_core_primary_upper ht hcore
      linarith
    · have hi' : i ∈ Candidate.zeroEdges := by simpa [hsi] using hi
      have hji : j = 3 := by fin_cases j <;> simp_all [ForwardAxis.ofIndex]
      subst j
      have hlarge := (Candidate.Geometric.zero_source_primary_requires_outer F hi' hj).2
      have hsmall := arc_core_primary_upper hs hcore
      linarith
  · have hji : j = 0 := by fin_cases j <;> simp_all [ForwardAxis.ofIndex]
    subst j
    have hsign : C.sigma i*C.b i ≤ 0 := by
      rw [← hσ]
      simpa [ArcData.sign,hnegative] using neg_nonpos.mpr (C.b_nonneg i)
    exact Candidate.Geometric.source_secondary_excluded_of_target_core F
      (arc_core_primary_upper ht hcore) hsign hj
  · have hji : j = 2 := by fin_cases j <;> simp_all [ForwardAxis.ofIndex]
    subst j
    have hsign : 0 ≤ C.sigma (next i)*C.b (next i) := by
      rw [← hτ]
      simpa [ArcData.sign,hpositive] using C.b_nonneg (next i)
    exact Candidate.Geometric.target_secondary_excluded_of_source_core F
      (arc_core_primary_upper hs hcore) hsign hj
  · rw [hsi] at hk
    refine Candidate.Geometric.quarter_core_opposite_excluded F hk (arc_core_primary_upper hs hsc)
      (arc_core_primary_upper ht htc) ?_ ?_ j hj
    · rw [← hσ]
      simp [ArcData.sign, hsp]
    · rw [← hτ]
      simp [ArcData.sign, htn]

/-- No edge of the cycle joins two squares with primary coordinate at most `7/12`, in
particular two core squares. -/
def NoAdjacentCore {q : ℝ} (C : BoundaryCycle q) : Prop :=
  ∀ i, ¬ (C.a i ≤ 7/12 ∧ C.a (next i) ≤ 7/12)

/-- The cover data of a table: for each arc the intervals of the arctangents of its two tangent
endpoints, and the state chains. -/
structure AffineCover where
  endpoints : List (QInterval × QInterval)
  states : StateChains

namespace AffineCover

/-- The intervals of the arctangents of the two endpoints of the arc `k`. -/
def endpointAt (K : AffineCover) (k : ℕ) : QInterval × QInterval :=
  K.endpoints.getD k default
/-- An interval of the arctangent `arctan (σ b / a)` of the signed tangent on the arc `k`. -/
def alphaBox (K : AffineCover) (M : AffineTableMeta) (k : ℕ) : QInterval :=
  if (arcAt M k).positive then ⟨(K.endpointAt k).1.lo,(K.endpointAt k).2.hi⟩
  else ⟨-(K.endpointAt k).2.hi,-(K.endpointAt k).1.lo⟩
/-- `π` to eighteen decimals. -/
def piBox : QInterval :=
  ⟨3141592653589793238/1000000000000000000,3141592653589793239/1000000000000000000⟩
/-- An interval of the angle `φ = g - α_s + α_t` between the frames on an edge with the arcs `s`
and `t`, for a gap `g` between the centre directions in `[19/25, 710/113 - 114/25]`. -/
def phaseBox (K : AffineCover) (M : AffineTableMeta) (s t : ℕ) : QInterval :=
  (⟨19/25,710/113-114/25⟩ : QInterval).sub (K.alphaBox M s) |>.add (K.alphaBox M t)
/-- An interval of the base angle `w π / 2` of the edge `i`, with its quarter `w`. -/
def baseBox (M : AffineTableMeta) (i : Vertex) : QInterval :=
  (QInterval.point ((M.word i : ℚ)/2)).mul piBox
/-- The required interval of `u` for the arcs `s` and `t` and a half: `φ - w π / 2` on the
positive half and its negative on the other, within the range of the frame difference (or its
negative) and within `[0, 7/10]`. -/
def required (K : AffineCover) (M : AffineTableMeta) (s t : ℕ) (positiveHalf : Bool) : QInterval :=
  let i := (arcAt M s).role
  let phase := K.phaseBox M s t
  let base := baseBox M i
  let raw := if positiveHalf then phase.sub base else base.sub phase
  let difference := if positiveHalf then M.differenceRange i else (M.differenceRange i).neg
  (raw.inter difference).inter ⟨0,7/10⟩

/-- The endpoint intervals contain the arctangents of the tangent endpoints of the arcs. -/
def EndpointsValid (K : AffineCover) (M : AffineTableMeta) : Prop :=
  ∀ k : Fin M.arcs.length,
    (K.endpointAt k).1.Mem (Real.arctan (arcAt M k).tangent.lo) ∧
    (K.endpointAt k).2.Mem (Real.arctan (arcAt M k).tangent.hi)

/-- With valid endpoint intervals, the arctangent of the signed tangent of a state of an arc lies
in `alphaBox`. -/
theorem alpha_mem {K : AffineCover} {M : AffineTableMeta} (hK : K.EndpointsValid M)
    (k : Fin M.arcs.length) {a b : ℝ} (hab : (arcAt M k).Contains M.radius a b) :
    (K.alphaBox M k).Mem (Real.arctan ((arcAt M k).sign*b/a)) := by
  have hlo := (hK k).1
  have hhi := (hK k).2
  have hl := Real.arctan_mono hab.2.2.2.1.1
  have hu := Real.arctan_mono hab.2.2.2.1.2
  cases hs : (arcAt M k).positive with
  | true =>
      simpa [alphaBox,ArcData.sign,hs,QInterval.Mem] using
        And.intro (hlo.1.trans hl) (hu.trans hhi.2)
  | false =>
      have hx : -(1:ℝ)*b/a=-(b/a) := by ring
      simp only [alphaBox,hs,Bool.false_eq_true,↓reduceIte,ArcData.sign,hx,Real.arctan_neg,
        QInterval.Mem]
      push_cast
      exact ⟨by linarith [hu,hhi.2],by linarith [hl,hlo.1]⟩

/-- Each gap between consecutive centre directions is below `710/113 - 114/25`, since the seven
gaps sum to `2π` and each exceeds `19/25`. -/
theorem frame_gap_upper {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C) (i : Vertex) :
    angleGap C.beta i < (710/113-114/25 : ℝ) := by
  have hsum := angleGap_sum C.beta
  have h0 := F.gap_lower 0
  have h1 := F.gap_lower 1
  have h2 := F.gap_lower 2
  have h3 := F.gap_lower 3
  have h4 := F.gap_lower 4
  have h5 := F.gap_lower 5
  have h6 := F.gap_lower 6
  have hpi := two_pi_lt_710_over_113
  simp only [Fin.sum_univ_seven] at hsum
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by
    revert i; decide
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> linarith

/-- On an edge whose squares lie on the arcs `s` and `t`, `u = |δ|` lies in the required
interval of the half of the sign of the frame difference `δ`. -/
theorem required_mem {K : AffineCover} {M : AffineTableMeta}
    (hK : K.EndpointsValid M) (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role=i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i=C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i)=C.sigma (next i)*C.b (next i))
    {r : Bool} {u : ℝ} (hu : u=|Candidate.delta F.theta i|)
    (hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u) :
    (K.required M s t r).Mem u := by
  have hαs := K.alpha_mem hK s hs
  have hαt := K.alpha_mem hK t ht
  rw [hσ] at hαs
  rw [hτ] at hαt
  change (K.alphaBox M s).Mem (C.alpha i) at hαs
  change (K.alphaBox M t).Mem (C.alpha (next i)) at hαt
  have hgap : (⟨19/25,710/113-114/25⟩:QInterval).Mem (angleGap C.beta i) := by
    refine ⟨?_,?_⟩
    · show ((19/25 : ℚ) : ℝ) ≤ angleGap C.beta i
      push_cast
      exact (F.gap_lower i).le
    · show angleGap C.beta i ≤ ((710/113-114/25 : ℚ) : ℝ)
      push_cast
      exact (frame_gap_upper F i).le
  have hphase := QInterval.mem_add (QInterval.mem_sub hgap hαs) hαt
  have hφ : (K.phaseBox M s t).Mem (Candidate.phi F.theta i) := by
    have he : Candidate.phi F.theta i = angleGap C.beta i-C.alpha i+C.alpha (next i) := by
      rw [F.physical_angle]
      ring
    rw [he]
    exact hphase
  have hpi : piBox.Mem Real.pi := by
    refine ⟨?_,?_⟩
    · show ((3141592653589793238/1000000000000000000 : ℚ) : ℝ) ≤ Real.pi
      push_cast
      exact pi_hand_enclosure.1.le
    · show Real.pi ≤ ((3141592653589793239/1000000000000000000 : ℚ) : ℝ)
      push_cast
      exact pi_hand_enclosure.2.le
  -- `QInterval.mem_point` is applied to the rational `word i / 2`, which it casts to the reals.
  have hb := QInterval.mem_mul (QInterval.mem_point ((M.word i:ℚ)/2)) hpi
  have hbase : (baseBox M i).Mem ((M.word i:ℝ)*Real.pi/2) := by
    have he : ((((M.word i:ℚ)/2 : ℚ)) : ℝ)*Real.pi = (M.word i:ℝ)*Real.pi/2 := by
      push_cast
      ring
    rw [← he]
    exact hb
  have hph : Candidate.phi F.theta i=(M.word i:ℝ)*Real.pi/2+Candidate.delta F.theta i := by
    rw [hword]
    rfl
  have hsmall : (⟨0,7/10⟩:QInterval).Mem u := by
    rw [hu]
    refine ⟨?_,?_⟩
    · show ((0 : ℚ) : ℝ) ≤ |Candidate.delta F.theta i|
      push_cast
      exact abs_nonneg _
    · show |Candidate.delta F.theta i| ≤ ((7/10 : ℚ) : ℝ)
      push_cast
      exact (F.delta_small i).le
  cases hr : r with
  | true =>
      have hδ : Candidate.delta F.theta i=u := by simpa [hr,AnglePolynomial.signQ] using hdu
      have hraw := QInterval.mem_sub hφ hbase
      have hraw' : ((K.phaseBox M s t).sub (baseBox M i)).Mem u := by
        have he : Candidate.phi F.theta i-(M.word i:ℝ)*Real.pi/2 = u := by
          rw [hph,hδ]
          ring
        rw [he] at hraw
        exact hraw
      have hdiff' : (M.differenceRange i).Mem u := by simpa [hδ] using hdiff i
      have hfin := QInterval.mem_inter (QInterval.mem_inter hraw' hdiff') hsmall
      rw [← hsi] at hfin
      exact hfin
  | false =>
      have hδ : Candidate.delta F.theta i= -u := by simpa [hr,AnglePolynomial.signQ] using hdu
      have hraw := QInterval.mem_sub hbase hφ
      have hraw' : ((baseBox M i).sub (K.phaseBox M s t)).Mem u := by
        have he : (M.word i:ℝ)*Real.pi/2-Candidate.phi F.theta i = u := by
          rw [hph,hδ]
          ring
        rw [he] at hraw
        exact hraw
      have hdiff' : (M.differenceRange i).neg.Mem u := by
        have hn := QInterval.mem_neg (hdiff i)
        rw [hδ,neg_neg] at hn
        exact hn
      have hfin := QInterval.mem_inter (QInterval.mem_inter hraw' hdiff') hsmall
      rw [← hsi] at hfin
      exact hfin

/-- Every `u` in the required interval of an arc pair with consecutive roles, an allowed axis that
is not excluded and a half lies in the angle interval of a row of that pair, axis and half, on the
edge of the source role with its quarter and with a lower target at least the target of the edge;
with `core`, the pairs of two core arcs are left out, their costs being bounded otherwise
(`CorePairBound`). -/
def AngleCovers (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow)
    (core : Bool) : Prop :=
  ∀ s t : Fin M.arcs.length, (arcAt M t).role=(arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis∈M.allowedAxes (arcAt M s).role →
      ¬ ExcludedArcs (arcAt M s) (arcAt M t) axis →
      (core = true → (arcAt M s).outer = true ∨ (arcAt M t).outer = true) → ∀ r : Bool, ∀ u : ℝ,
      (K.required M s t r).Mem u →
      ∃ row ∈ rows,
        row.source=s.val ∧ row.target=t.val ∧ row.edge=(arcAt M s).role ∧
        row.axis=axis ∧ row.quarter=M.word (arcAt M s).role ∧
        row.positiveHalf=r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role≤row.lowerTarget

/-- The cost bound of the edges between two core arcs of a table, for a cycle. -/
def CorePairBound (M : AffineTableMeta) (C : BoundaryCycle (M.radius:ℝ))
    (F : Candidate.Frame C) : Prop :=
  ∀ {i : Vertex} {s t : Fin M.arcs.length}, (arcAt M s).role=i → (arcAt M t).role=next i →
    (arcAt M s).Contains M.radius (C.a i) (C.b i) →
    (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)) →
    (arcAt M s).sign*C.b i=C.sigma i*C.b i →
    (arcAt M t).sign*C.b (next i)=C.sigma (next i)*C.b (next i) →
    (arcAt M s).outer=false → (arcAt M t).outer=false →
    ∀ j : Fin 4, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      (M.target i:ℝ) < chargedCost (arcAt M s).label (arcAt M t).label (M.charge i)
        (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i)

/-- Without adjacent core squares the bound holds vacuously. -/
theorem _root_.SquaresInCircles.Eight.Arithmetic.NoAdjacentCore.corePairBound
    {M : AffineTableMeta} {C : BoundaryCycle (M.radius:ℝ)} (hC : NoAdjacentCore C)
    (F : Candidate.Frame C) : CorePairBound M C F :=
  fun _ _ hs ht _ _ hsc htc _ _ =>
    (hC _ ⟨arc_core_primary_upper hs hsc, arc_core_primary_upper ht htc⟩).elim

/-- The cost bound of an edge for two arcs of the table that contain the states of its vertices:
from the rows, or from `CorePairBound` for two core arcs when `core`. -/
theorem pairBound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    {core : Bool} (hE : K.EndpointsValid M) (hA : K.AngleCovers M rows core)
    (hrows : ∀ r∈rows, r.Claim M) (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i)
    (hcore : core = true → CorePairBound M C F)
    {i : Vertex} {s t : Fin M.arcs.length} (hsi : (arcAt M s).role=i)
    (hti : (arcAt M t).role=next i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i=C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i)=C.sigma (next i)*C.b (next i))
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (M.target i:ℝ) < chargedCost (arcAt M s).label (arcAt M t).label (M.charge i)
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
  by_cases hcc : core = true ∧ (arcAt M s).outer=false ∧ (arcAt M t).outer=false
  · exact hcore hcc.1 hsi hti hs ht hσ hτ hcc.2.1 hcc.2.2 j hj
  let axis := ForwardAxis.ofIndex j
  let d := Candidate.delta F.theta i
  let r : Bool := decide (0≤d)
  let u := |d|
  have hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u := by
    by_cases hd : 0≤Candidate.delta F.theta i
    · have hr : r = true := by simp [r,d,hd]
      rw [hr]
      simp [AnglePolynomial.signQ,u,d,abs_of_nonneg hd]
    · have hr : r = false := by simp [r,d,hd]
      rw [hr]
      simp [AnglePolynomial.signQ,u,d,abs_of_neg (lt_of_not_ge hd)]
  have hu := K.required_mem hE C F hword hdiff hsi hs ht hσ hτ (r:=r) (u:=u) rfl hdu
  have hallowed : axis∈M.allowedAxes (arcAt M s).role := by
    rw [hsi]
    exact haxes i j hj
  have hkeep : ¬ ExcludedArcs (arcAt M s) (arcAt M t) axis :=
    feasible_not_excluded C F hsi hs ht hσ hτ j hj
  have houter : core = true → (arcAt M s).outer = true ∨ (arcAt M t).outer = true := by
    intro hc
    cases hso : (arcAt M s).outer <;> cases hto : (arcAt M t).outer <;> simp_all
  obtain ⟨row,hrow,hrs,hrt,he,ha,hk,hr,hru,hγ⟩ := hA _ _
    (by rw [hsi,hti]; rfl) axis hallowed hkeep houter r u hu
  have hsdata : row.sourceArc M=arcAt M s := by
    simp [AffineTableRow.sourceArc,arcAt,hrs]
  have htdata : row.targetArc M=arcAt M t := by
    simp [AffineTableRow.targetArc,arcAt,hrt]
  have he' : row.edge=i := he.trans hsi
  have hphi : row.phi u=Candidate.phi F.theta i := by
    rw [AffineTableRow.phi,hk,hsi]
    rw [show row.sign=(AnglePolynomial.signQ r:ℝ) by
      cases hrr : r <;> simp [AffineTableRow.sign,hr,hrr,AnglePolynomial.signQ]]
    rw [← hdu,hword]
    rfl
  have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
    ⟨by rw [hsdata]; exact hs,by rw [htdata]; exact ht,hru⟩
  have hactual := (F.margin_nonneg_iff i j).mp hj
  have horiginal : 0≤forwardMargin axis (C.sigma i) (C.sigma (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
    rw [forwardMargin_actual,ForwardAxis.index_ofIndex]
    exact hactual
  have hselected : 0≤forwardMargin row.axis (row.sourceArc M).sign (row.targetArc M).sign
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
    rw [ha,hsdata,htdata,hphi,forwardMargin_congr_products axis hσ hτ]
    exact horiginal
  have hp := hrows row hrow _ _ _ _ _ hdom hselected
  have htarget : (M.target i:ℝ)≤row.lowerTarget := by
    have hγ' : (M.target (arcAt M s).role:ℝ)≤row.lowerTarget := by exact_mod_cast hγ
    rwa [hsi] at hγ'
  rw [hsdata,htdata,he',hphi] at hp
  exact htarget.trans_lt hp

/-- The charged bound from the endpoint, state and angle covers and the row claims. -/
noncomputable def chargedBoundOf {K : AffineCover} {M : AffineTableMeta}
    {rows : List AffineTableRow} {core : Bool} (hE : K.EndpointsValid M)
    (hS : K.states.NumericValid M) (hA : K.AngleCovers M rows core)
    (hrows : ∀ r∈rows, r.Claim M) (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C)
    (β : ℝ) (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i)
    (hcore : core = true → CorePairBound M C F) :
    Candidate.ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hS C hcuts i
  refine ⟨fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i), fun i j hj => ?_⟩
  have h := pairBound hE hA hrows C F hword hdiff haxes hcore (hrole i) (hrole (next i))
    (hcontains i) (hcontains (next i)) (hproducts i) (hproducts (next i)) j hj
  rw [hcharge] at h
  simp only [chargedCost,frameCharge] at h
  unfold Candidate.h
  linarith

end AffineCover
end SquaresInCircles.Eight.Arithmetic
