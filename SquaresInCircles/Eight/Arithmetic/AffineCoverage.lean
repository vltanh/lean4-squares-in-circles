module

public import SquaresInCircles.Eight.Arithmetic.StateCoverage
public import SquaresInCircles.Eight.Candidate.GeometricSecondaryExclusion
public import SquaresInCircles.Eight.Frames

/-!
# Complete affine-table coverage and the cyclic charged bound

The state cover chooses one label per vertex before any separating axis is
selected. For each pair of labels and each allowed original axis, the rows of
the table cover every required angle (`AngleCovers`), except on the pairs and
axes that no feasible separator can have (`Excluded`): an axis two or four
separator against a core square on a zero-quarter edge, and an axis one or
three separator against a core square with the inward transverse sign.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Arithmetic

instance : Inhabited QInterval := ⟨⟨0,0⟩⟩
instance : Inhabited AffineTableRow := ⟨⟨0,0,0,.one,0,true,⟨0,0⟩,0,.endpoints,1,0⟩⟩

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

def ForwardAxis.ofIndex (i : Fin 4) : ForwardAxis := ![.one,.two,.three,.four] i
@[simp] theorem ForwardAxis.index_ofIndex (i : Fin 4) : (ForwardAxis.ofIndex i).index=i := by
  fin_cases i <;> rfl

theorem forwardMargin_congr_products (axis : ForwardAxis) {σ τ σ' τ' a b A B φ : ℝ}
    (hs : σ*b=σ'*b) (ht : τ*B=τ'*B) :
    forwardMargin axis σ τ a b A B φ=forwardMargin axis σ' τ' a b A B φ := by
  cases axis <;> simp only [forwardMargin,hs,ht]

/-- An arc pair and an original axis that no feasible separator has (`feasible_not_excluded`):
on a zero-quarter edge, axis two against a core target or axis four against a core source; on
any edge, axis one with a core target and a source of sign `-1`, or axis three with a core
source and a target of sign `+1`. -/
def ExcludedArcs (aS aT : ArcData) (axis : ForwardAxis) : Prop :=
  (aS.role ∈ Candidate.zeroEdges ∧
    ((axis = .two ∧ aT.outer = false) ∨ (axis = .four ∧ aS.outer = false))) ∨
  (axis = .one ∧ aS.positive = false ∧ aT.outer = false) ∨
  (axis = .three ∧ aT.positive = true ∧ aS.outer = false)

instance (aS aT : ArcData) (axis : ForwardAxis) : Decidable (ExcludedArcs aS aT axis) := by
  unfold ExcludedArcs
  infer_instance

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

/-- A feasible original axis of the selected labels is not excluded. -/
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
  rcases hexcluded with hprimary | hsecondary
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
  · rcases hsecondary with ⟨haxis,hnegative,hcore⟩ | ⟨haxis,hpositive,hcore⟩
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

/-- The cover data of a table: for each arc the intervals of the arctangents of its two tangent
endpoints, and the state chains. -/
structure AffineCover where
  endpoints : List (QInterval × QInterval)
  states : StateChains

namespace AffineCover

def endpointAt (K : AffineCover) (k : ℕ) : QInterval × QInterval :=
  K.endpoints.getD k default
def alphaBox (K : AffineCover) (M : AffineTableMeta) (k : ℕ) : QInterval :=
  if (arcAt M k).positive then ⟨(K.endpointAt k).1.lo,(K.endpointAt k).2.hi⟩
  else ⟨-(K.endpointAt k).2.hi,-(K.endpointAt k).1.lo⟩
def piBox : QInterval :=
  ⟨3141592653589793238/1000000000000000000,3141592653589793239/1000000000000000000⟩
def phaseBox (K : AffineCover) (M : AffineTableMeta) (s t : ℕ) : QInterval :=
  (⟨19/25,710/113-114/25⟩ : QInterval).sub (K.alphaBox M s) |>.add (K.alphaBox M t)
def baseBox (M : AffineTableMeta) (i : Vertex) : QInterval :=
  (QInterval.point ((M.word i : ℚ)/2)).mul piBox
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
  -- The singleton constructor takes a rational; its membership theorem
  -- performs the coercion to the real coordinate. Do not coerce first.
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

/-- Every required angle of every arc pair with consecutive roles and every allowed axis that is
not excluded lies in the angle interval of a row of that pair, axis and half. -/
def AngleCovers (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  ∀ s t : Fin M.arcs.length, (arcAt M t).role=(arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis∈M.allowedAxes (arcAt M s).role →
      ¬ ExcludedArcs (arcAt M s) (arcAt M t) axis → ∀ r : Bool, ∀ u : ℝ,
      (K.required M s t r).Mem u →
      ∃ row ∈ rows,
        row.source=s.val ∧ row.target=t.val ∧ row.edge=(arcAt M s).role ∧
        row.axis=axis ∧ row.quarter=M.word (arcAt M s).role ∧
        row.positiveHalf=r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role≤row.lowerTarget

/-- The charged bound from the endpoint, state and angle covers and the row claims. -/
noncomputable def chargedBoundOf {K : AffineCover} {M : AffineTableMeta}
    {rows : List AffineTableRow} (hE : K.EndpointsValid M) (hS : K.states.NumericValid M)
    (hA : K.AngleCovers M rows) (hrows : ∀ r∈rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hS C hcuts i
  refine ⟨fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i), ?_⟩
  intro i j hj
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
  have hu := K.required_mem hE C F hword hdiff (hrole i) (hcontains i)
    (hcontains (next i)) (hproducts i) (hproducts (next i)) (r:=r) (u:=u) rfl hdu
  have hallowed : axis∈M.allowedAxes (arcAt M (selected i)).role := by
    rw [hrole]
    exact haxes i j hj
  have hkeep : ¬ ExcludedArcs (arcAt M (selected i)) (arcAt M (selected (next i))) axis :=
    feasible_not_excluded C F (hrole i) (hcontains i) (hcontains (next i)) (hproducts i)
      (hproducts (next i)) j hj
  obtain ⟨row,hrow,hs,ht,he,ha,hk,hr,hru,hγ⟩ := hA _ _
    (by rw [hrole,hrole]; rfl) axis hallowed hkeep r u hu
  have hsdata : row.sourceArc M=arcAt M (selected i) := by
    simp [AffineTableRow.sourceArc,arcAt,hs]
  have htdata : row.targetArc M=arcAt M (selected (next i)) := by
    simp [AffineTableRow.targetArc,arcAt,ht]
  have he' : row.edge=i := he.trans (hrole i)
  have hphi : row.phi u=Candidate.phi F.theta i := by
    rw [AffineTableRow.phi,hk,hrole]
    rw [show row.sign=(AnglePolynomial.signQ r:ℝ) by
      cases hrr : r <;> simp [AffineTableRow.sign,hr,hrr,AnglePolynomial.signQ]]
    rw [← hdu,hword]
    rfl
  have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
    ⟨by rw [hsdata]; exact hcontains i,by rw [htdata]; exact hcontains (next i),hru⟩
  have hactual := (F.margin_nonneg_iff i j).mp hj
  have horiginal : 0≤forwardMargin axis (C.sigma i) (C.sigma (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
    rw [forwardMargin_actual,ForwardAxis.index_ofIndex]
    exact hactual
  have hselected : 0≤forwardMargin row.axis (row.sourceArc M).sign (row.targetArc M).sign
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
    rw [ha,hsdata,htdata,hphi,
      forwardMargin_congr_products axis (hproducts i) (hproducts (next i))]
    exact horiginal
  have hp := hrows row hrow _ _ _ _ _ hdom hselected
  have htarget : (M.target i:ℝ)≤row.lowerTarget := by
    have hγ' : (M.target (arcAt M (selected i)).role:ℝ)≤row.lowerTarget := by
      exact_mod_cast hγ
    rwa [hrole] at hγ'
  have hh := htarget.trans_lt hp
  rw [hsdata,htdata,he',hphi,hcharge] at hh
  simp only [chargedCost,frameCharge] at hh
  show (M.target i:ℝ) < Candidate.phi F.theta i-Candidate.charge β i*
      Candidate.h (Candidate.phi F.theta i)+(arcAt M (selected i)).label.eval (C.a i) (C.b i)-
      (arcAt M (selected (next i))).label.eval (C.a (next i)) (C.b (next i))
  unfold Candidate.h
  linarith

end AffineCover
end SquaresInCircles.Eight.Arithmetic
