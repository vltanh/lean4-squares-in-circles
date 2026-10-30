module

public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Arithmetic.AffineCoverage

/-!
# Eight squares: core/core costs from the markers of the core arcs

On a core arc of an affine table with valid markers (`ArcValid`) the label is `c + q b`, constant
on the core corner, so the marker `± arctan x - c - (7/12) q x` of a state is a function of its
tangent `x`. Its second derivative lies in `[-1, 1]`, so on an arc `[l, u]` of the core side it is
within `(u - l)²/8` of the range of its two endpoint values (`chart_bounds`); on an arc of the
corner it is monotone. Rational bounds of the endpoint values (`MarkersValid`) therefore bound the
marker of every core vertex (`arc_marker_mem`). With the gap `4/3` between two consecutive core
centres (`Arithmetic/CorePairGeometry.lean`), the frame charge below `21/100` and seven edge
budgets (`BudgetsValid`) they bound the cost of every core/core edge (`pair_bound`): this is the
`CorePairBound` for the pairs of core arcs that the coverage of a table leaves out
(`Arithmetic/AffineCoverage.lean`).

Two squares with primary coordinate at most `7/12` lie on core arcs
(`arc_core_of_small_primary`). If an edge joined two such squares, the same argument would give it
a cost above `9/10`, and with the targets `89727/100000` of the coarse table on the six other edges
the bounds would add up to more than `2π`; so no edge joins them (`no_adjacent_core`). The bounds
are checked for the coarse table in `Generated/Affine/CandidateCoarseMismatch.lean`, and
`Generated/AffineBudgets.lean` passes the conclusion to the later tables.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Candidate.GeometricCoreMarker
open Arithmetic

/-- With second derivative at most `1` on `[l, u]`, a function is at least its smaller endpoint
value less `(u - l)²/8`. -/
theorem endpoint_lower {f d dd : ℝ → ℝ} {l u x L : ℝ} (hx : x ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y) (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hc : ∀ y ∈ Icc l u, dd y ≤ 1) (hl : L ≤ f l) (hu : L ≤ f u) : L-(u-l)^2/8 ≤ f x := by
  have hg : ConcaveOn ℝ (Icc l u) (fun y => f y-(y-l)*(y-u)/2) :=
    concave_of_deriv2
      (fun y hy => (hd y hy).sub ((((hasDerivAt_id' y).sub_const l).mul
        ((hasDerivAt_id' y).sub_const u)).div_const 2))
      (fun y hy => (hdd y hy).sub ((((hasDerivAt_const y (1:ℝ)).mul
        ((hasDerivAt_id' y).sub_const u)).add (((hasDerivAt_id' y).sub_const l).mul
        (hasDerivAt_const y (1:ℝ)))).div_const 2))
      (fun y hy => by norm_num; linarith [hc y hy])
  have hmin := hg.min_le_of_mem_Icc ⟨le_rfl, hx.1.trans hx.2⟩ ⟨hx.1.trans hx.2, le_rfl⟩ hx
  simp only [sub_self, zero_mul, mul_zero, zero_div, sub_zero] at hmin
  nlinarith [sq_nonneg (2*x-l-u), le_min hl hu]

/-- With second derivative in `[-1, 1]`, both bounds. -/
theorem endpoint_bounds {f d dd : ℝ → ℝ} {l u x L U : ℝ} (hx : x ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y) (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hc : ∀ y ∈ Icc l u, -1 ≤ dd y ∧ dd y ≤ 1)
    (hl : L ≤ f l ∧ f l ≤ U) (hu : L ≤ f u ∧ f u ≤ U) :
    L-(u-l)^2/8 ≤ f x ∧ f x ≤ U+(u-l)^2/8 := by
  refine ⟨endpoint_lower hx hd hdd (fun y hy => (hc y hy).2) hl.1 hu.1, ?_⟩
  have h := endpoint_lower (f := fun y => -f y) (d := fun y => -d y) (dd := fun y => -dd y)
    (L := -U) hx (fun y hy => (hd y hy).neg) (fun y hy => (hdd y hy).neg)
    (fun y hy => by linarith [(hc y hy).1]) (by linarith [hl.2]) (by linarith [hu.2])
  linarith

/-- The marker `± arctan x - c - (7/12) q x` of a core-side label `c + q b` at `b = (7/12) x`. -/
def chartMarker (positive : Bool) (c q x : ℝ) : ℝ :=
  (if positive then Real.arctan x else -Real.arctan x)-(c+(7/12)*q*x)

/-- On `[l, u] ⊆ [0, ∞)` the marker is within `(u - l)²/8` of the range of its endpoint values,
since `|arctan''| = 2x/(1+x²)² ≤ 1`. -/
theorem chart_bounds (positive : Bool) (c q : ℝ) {l u x L U : ℝ} (hl0 : 0 ≤ l)
    (hx : x ∈ Icc l u)
    (hl : L ≤ chartMarker positive c q l ∧ chartMarker positive c q l ≤ U)
    (hu : L ≤ chartMarker positive c q u ∧ chartMarker positive c q u ≤ U) :
    L-(u-l)^2/8 ≤ chartMarker positive c q x ∧ chartMarker positive c q x ≤ U+(u-l)^2/8 := by
  set s : ℝ := if positive then 1 else -1 with hs
  have hm : chartMarker positive c q = fun y => s*Real.arctan y-(c+(7/12)*q*y) := by
    funext y
    cases positive <;> simp [chartMarker, s]
  have hd (y : ℝ) : HasDerivAt (chartMarker positive c q) (s*(1/(1+y^2))-(7/12)*q*1) y := by
    rw [hm]
    exact ((Real.hasDerivAt_arctan y).const_mul s).sub
      (((hasDerivAt_id' y).const_mul ((7/12)*q)).const_add c)
  have hdd (y : ℝ) : HasDerivAt (fun y : ℝ => s*(1/(1+y^2))-(7/12)*q*1)
      (s*((0*(1+y^2)-1*(↑2*y^(2-1)))/(1+y^2)^2)) y :=
    (((hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_pow 2 y).const_add 1)
      (by positivity)).const_mul s).sub_const _
  refine endpoint_bounds hx (fun y _ => hd y) (fun y _ => hdd y) (fun y hy => ?_) hl hu
  have hy0 : 0 ≤ y := hl0.trans hy.1
  have hden : 0 < (1+y^2)^2 := by positivity
  have h1 : 2*y/(1+y^2)^2 ≤ 1 :=
    (div_le_one hden).mpr (by nlinarith [sq_nonneg (y-1), sq_nonneg y, sq_nonneg (y^2)])
  have h0 : 0 ≤ 2*y/(1+y^2)^2 := div_nonneg (by linarith) hden.le
  have he : s*((0*(1+y^2)-1*(↑2*y^(2-1)))/(1+y^2)^2)= -s*(2*y/(1+y^2)^2) := by
    norm_num
    ring
  rw [he]
  cases positive <;> simp only [s, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> nlinarith

/-- Lower bounds of the markers of the core states of the seven roles. -/
def markerLower (i : Vertex) : ℚ :=
  ![-383/1000,-323/1000,-368/1000,-329/1000,-88/1000,-319/1000,-342/1000] i

/-- Upper bounds of the markers of the core states of the seven roles, apart from a positive `D`
state. -/
def baseUpper (i : Vertex) : ℚ :=
  ![90/1000,-120/1000,100/1000,134/1000,96/1000,-12/1000,-111/1000] i

/-- The upper bound of the marker of a core state with the role `i` and the sign `positive`:
`baseUpper i`, and `643/1000` for a positive `D` state, whose core/core edge `D → E` has no
separating axis (`ExcludedArcs`), the core arcs of `E` having the sign `-1`. -/
def markerUpper (i : Vertex) (positive : Bool) : ℚ :=
  if i=5 ∧ positive=true then 643/1000 else baseUpper i

/-- `(u - l)²/8` on an arc of the core side, `0` on the corner. -/
def interpolationError (s : ArcData) : ℚ :=
  if s.tangent.hi ≤ 6/7 then (s.tangent.hi-s.tangent.lo)^2/8 else 0

/-- The marker at a tangent endpoint `x`, from an interval `e` of `arctan x`. -/
def endpointMarker (s : ArcData) (e : QInterval) (x : ℚ) : QInterval :=
  (if s.positive then e else e.neg).sub (QInterval.point (s.label.c+(7/12)*s.label.q*x))

/-- The endpoint bounds of a core arc: its label is `c + q b`, constant on the corner, its tangent
interval lies in `[0, ∞)`, a core arc of `E` has the sign `-1`, and the marker at both tangent
endpoints lies within the bounds of the role narrowed by the interpolation error. -/
def ArcValid (s : ArcData) (lo hi : QInterval) : Prop :=
  s.label.p=0 ∧ (6/7 < s.tangent.hi → s.label.q=0) ∧
    (0 ≤ s.tangent.lo ∧ s.tangent.lo ≤ s.tangent.hi) ∧ (s.role=6 → s.positive=false) ∧
    (markerLower s.role+interpolationError s ≤ (endpointMarker s lo s.tangent.lo).lo ∧
      (endpointMarker s lo s.tangent.lo).hi ≤ markerUpper s.role s.positive-interpolationError s) ∧
    (markerLower s.role+interpolationError s ≤ (endpointMarker s hi s.tangent.hi).lo ∧
      (endpointMarker s hi s.tangent.hi).hi ≤ markerUpper s.role s.positive-interpolationError s)

instance (s : ArcData) (lo hi : QInterval) : Decidable (ArcValid s lo hi) := by
  unfold ArcValid; infer_instance

/-- The endpoint bounds of every core arc of a table. -/
def MarkersValid (K : AffineCover) (M : AffineTableMeta) : Prop :=
  ∀ k : Fin M.arcs.length, (arcAt M k).outer=false →
    ArcValid (arcAt M k) (K.endpointAt k).1 (K.endpointAt k).2

instance (K : AffineCover) (M : AffineTableMeta) : Decidable (MarkersValid K M) := by
  unfold MarkersValid; infer_instance

/-- The edge budgets: `γᵢ ≤ 4/3 - baseUpper i + markerLower (i + 1) - (21/100) βᵢ`. -/
def BudgetsValid (M : AffineTableMeta) : Prop :=
  ∀ i, 0 ≤ M.charge i ∧ M.target i ≤ 4/3-baseUpper i+markerLower (next i)-M.charge i*(21/100)

instance (M : AffineTableMeta) : Decidable (BudgetsValid M) := by
  unfold BudgetsValid; infer_instance

theorem endpoint_marker_mem (s : ArcData) {e : QInterval} {x : ℚ} (he : e.Mem (Real.arctan x)) :
    (endpointMarker s e x).Mem (chartMarker s.positive s.label.c s.label.q x) := by
  have hp := QInterval.mem_point (s.label.c+(7/12)*s.label.q*x)
  cases hpos : s.positive
  · have h := QInterval.mem_sub (QInterval.mem_neg he) hp
    simpa [endpointMarker, chartMarker, hpos, sub_eq_add_neg] using h
  · have h := QInterval.mem_sub he hp
    simpa [endpointMarker, chartMarker, hpos, sub_eq_add_neg] using h

/-- The marker of a state of a core arc lies within the bounds of its role. -/
theorem arc_marker_mem {K : AffineCover} {M : AffineTableMeta} (hK : K.EndpointsValid M)
    (hv : MarkersValid K M) {k : Fin M.arcs.length} {a b : ℝ}
    (hs : (arcAt M k).Contains M.radius a b) (hcore : (arcAt M k).outer=false) :
    (markerLower (arcAt M k).role:ℝ) ≤
        Real.arctan ((arcAt M k).sign*b/a)-(arcAt M k).label.eval a b ∧
      Real.arctan ((arcAt M k).sign*b/a)-(arcAt M k).label.eval a b ≤
        markerUpper (arcAt M k).role (arcAt M k).positive := by
  obtain ⟨hp, hq, hrange, -, hlo, hhi⟩ := hv k hcore
  set s := arcAt M k
  have hl := endpoint_marker_mem s (hK k).1
  have hu := endpoint_marker_mem s (hK k).2
  have hcast (I : QInterval) (L U : ℚ) (hI : L ≤ I.lo ∧ I.hi ≤ U) {y : ℝ} (hy : I.Mem y) :
      (L:ℝ) ≤ y ∧ y ≤ U :=
    ⟨(Rat.cast_le.mpr hI.1).trans hy.1, hy.2.trans (Rat.cast_le.mpr hI.2)⟩
  have hL := hcast _ _ _ hlo hl
  have hU := hcast _ _ _ hhi hu
  push_cast at hL hU
  have hx : b/a ∈ Icc (s.tangent.lo:ℝ) s.tangent.hi := hs.2.2.2.1
  have hcurve := hs.2.2.2.2
  have hid : Real.arctan (s.sign*b/a)-s.label.eval a b=
      chartMarker s.positive s.label.c s.label.q (b/a)+(s.label.q*((7/12)*(b/a)-b)) := by
    cases hpos : s.positive <;>
      simp [ArcData.sign, hpos, AffineLabel.eval, hp, chartMarker, neg_div, Real.arctan_neg] <;>
      ring
  rw [hid]
  by_cases hside : s.tangent.hi ≤ 6/7
  · have ha : a=7/12 := by
      simp only [ArcData.OnCurve, hcore, hside, Bool.false_eq_true, ite_false, ite_true] at hcurve
      exact hcurve.1
    have hb : s.label.q*((7/12)*(b/a)-b)=0 := by rw [ha]; ring
    have hbound := chart_bounds s.positive s.label.c s.label.q
      (by exact_mod_cast hrange.1) hx hL hU
    simp only [interpolationError, hside, ite_true] at hbound
    push_cast at hbound
    rw [hb]
    constructor <;> linarith [hbound.1, hbound.2]
  · have hq0 : s.label.q=0 := hq (lt_of_not_ge hside)
    simp only [interpolationError, hside, ite_false, Rat.cast_zero, sub_zero, add_zero] at hL hU
    simp only [chartMarker, hq0, Rat.cast_zero, zero_mul, mul_zero, add_zero, zero_mul] at hL hU ⊢
    have h1 := Real.arctan_mono hx.1
    have h2 := Real.arctan_mono hx.2
    cases hpos : s.positive <;>
      simp only [hpos, ite_true, ite_false, Bool.false_eq_true] at hL hU ⊢ <;>
      constructor <;> linarith [hL.1, hL.2, hU.1, hU.2]

/-- A state of a core arc is a core state. -/
theorem arc_core_state {s : ArcData} {Q a b : ℝ} (hs : s.Contains Q a b) (hcore : s.outer=false) :
    CorePairGeometry.CoreState a b := by
  have hcurve := hs.2.2.2.2
  by_cases hside : s.tangent.hi ≤ 6/7
  · simp only [ArcData.OnCurve, hcore, hside, Bool.false_eq_true, ite_false, ite_true] at hcurve
    exact Or.inl ⟨hcurve.1, hs.2.1, hcurve.2⟩
  · simp only [ArcData.OnCurve, hcore, hside, Bool.false_eq_true, ite_false] at hcurve
    exact Or.inr ⟨hcurve.1, hs.2.2.1, hcurve.2⟩

/-- The cost of a core/core edge for the labels of its two arcs exceeds the edge budget. -/
theorem pair_bound {K : AffineCover} {M : AffineTableMeta} (hK : K.EndpointsValid M)
    (hmarkers : MarkersValid K M) (hbudgets : BudgetsValid M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) : AffineCover.CorePairBound M C F := by
  intro i s t hsi hti hs ht hσ hτ hsource htarget j hj
  have hkeep := feasible_not_excluded C F hsi hs ht hσ hτ j hj
  have hupper : markerUpper (arcAt M s).role (arcAt M s).positive=baseUpper i := by
    rw [hsi]
    unfold markerUpper
    split_ifs with hD
    · have hneg := (hmarkers t htarget).2.2.2.1 (by rw [hti, hD.1]; rfl)
      exact (hkeep (Or.inr (Or.inr (Or.inr
        ⟨by rw [hsi, hD.1]; rfl, hsource, htarget, hD.2, hneg⟩)))).elim
    · rfl
  have hms := arc_marker_mem hK hmarkers hs hsource
  have hmt := arc_marker_mem hK hmarkers ht htarget
  have hαs : Real.arctan ((arcAt M s).sign*C.b i/C.a i)=C.alpha i := by
    simp only [BoundaryCycle.alpha, BoundaryCycle.tangent, hσ]
  have hαt : Real.arctan ((arcAt M t).sign*C.b (next i)/C.a (next i))=C.alpha (next i) := by
    simp only [BoundaryCycle.alpha, BoundaryCycle.tangent, hτ]
  rw [hαs, hupper, hsi] at hms
  rw [hαt, hti] at hmt
  have hg := CorePairGeometry.core_gap C i (arc_core_state hs hsource) (arc_core_state ht htarget)
  have hw : frameCharge (phi F.theta i) < 21/100 := by
    simpa [frameCharge, periodicFrameCost, add_comm] using
      CorePairGeometry.charge_upper (phi F.theta i)
  have hβ : (0:ℝ) ≤ M.charge i := by exact_mod_cast (hbudgets i).1
  have hbudget := (Rat.cast_le (K := ℝ)).mpr (hbudgets i).2
  push_cast at hbudget
  have he := F.physical_angle i
  simp only [chargedCost]
  nlinarith [hms.2, hmt.1, mul_le_mul_of_nonneg_left hw.le hβ]

/-- At a radius above `169/72` a point with primary coordinate at most `7/12` is not on the outer
circle, so an arc containing it is a core arc. -/
theorem arc_core_of_small_primary {s : ArcData} {q a b : ℝ} (hs : s.Contains q a b)
    (hq : 169/72 < q) (ha : a ≤ 7/12) : s.outer=false := by
  cases ho : s.outer
  · rfl
  · have hc := hs.2.2.2.2
    simp [ArcData.OnCurve, ho] at hc
    have hb : b ≤ 7/12 := hs.2.2.1.trans ha
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (by linarith [hs.1] : (0:ℝ) ≤ a+19/12),
      mul_nonneg (sub_nonneg.mpr hb) (by linarith [hs.2.1] : (0:ℝ) ≤ b+19/12)]

/-- No edge of a cycle joins two core squares: on such an edge the coarse labels give a cost above
`9/10`, on the six other edges above `89727/100000`, and `9/10 + 6 · 89727/100000 > 2π`. -/
theorem no_adjacent_core {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hE : K.EndpointsValid M) (hS : K.states.NumericValid M) (hA : K.AngleCovers M rows true)
    (hrows : ∀ r∈rows, r.Claim M) (hmarkers : MarkersValid K M) (hbudgets : BudgetsValid M)
    (hstrong : BudgetsValid {M with target := fun _ => 9/10})
    (htarget : ∀ i, M.target i=89727/100000) (hq : 169/72 < M.radius)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (β : ℝ) (hβ : 0 ≤ β)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i) : NoAdjacentCore C := by
  rintro i ⟨hai, haj⟩
  choose selected hrole hcontains hproducts using fun k => K.states.covers hS C hcuts k
  have hq' := (Rat.cast_lt (K := ℝ)).mpr hq
  push_cast at hq'
  let γ : Vertex → ℝ := fun k => if k=i then 9/10 else 89727/100000
  have P : ChargedBound C F β γ := by
    refine ⟨fun k => (arcAt M (selected k)).label.eval (C.a k) (C.b k), fun k j hj => ?_⟩
    have h : γ k < chargedCost (arcAt M (selected k)).label (arcAt M (selected (next k))).label
        (M.charge k) (C.a k) (C.b k) (C.a (next k)) (C.b (next k)) (phi F.theta k) := by
      by_cases hk : k=i
      · subst hk
        have h := pair_bound (M := {M with target := fun _ => 9/10}) hE hmarkers hstrong C F
          (hrole k) (hrole (next k)) (hcontains k) (hcontains (next k)) (hproducts k)
          (hproducts (next k)) (arc_core_of_small_primary (hcontains k) hq' hai)
          (arc_core_of_small_primary (hcontains (next k)) hq' haj) j hj
        change ((9/10:ℚ):ℝ) < chargedCost (arcAt M (selected k)).label
          (arcAt M (selected (next k))).label (M.charge k) (C.a k) (C.b k) (C.a (next k))
          (C.b (next k)) (phi F.theta k) at h
        simpa [γ] using h
      · have h := AffineCover.pairBound hE hA hrows C F hword hdiff haxes
          (fun _ => pair_bound hE hmarkers hbudgets C F) (hrole k) (hrole (next k))
          (hcontains k) (hcontains (next k)) (hproducts k) (hproducts (next k)) j hj
        rw [htarget] at h
        simpa [γ, hk] using h
    rw [hcharge] at h
    simp only [chargedCost, frameCharge] at h
    unfold Candidate.h
    linarith
  have hsum : (∑ k, γ k)=9/10+6*(89727/100000) := by
    have hγ (k : Vertex) : γ k=89727/100000+(if k=i then 9/10-89727/100000 else 0) := by
      by_cases hk : k=i <;> simp [γ, hk]
    rw [Finset.sum_congr rfl (fun k _ => hγ k), Finset.sum_add_distrib]
    simp
    norm_num
  have hcost : (0:ℝ) ≤ hSum F.theta := Finset.sum_nonneg fun k _ => h_nonneg _
  have hcyc := P.cyclic
  rw [hsum] at hcyc
  linarith [two_pi_lt_710_over_113, mul_nonneg hβ hcost]

end SquaresInCircles.Eight.Candidate.GeometricCoreMarker
