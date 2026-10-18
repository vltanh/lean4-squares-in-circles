module

public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Candidate.GeometricAffineCoverage

/-!
# Whole core/core costs with the original coarse vertex labels

The labels are evaluated once at each vertex and are not changed here.
On a core side, their markers are signed arctangent minus an affine
function of the tangent coordinate. A second-derivative bound controls
the whole original label interval by its two endpoints. On every core
corner the original label is constant, so monotonicity suffices.

The finite obligations are explicit endpoint-label bounds on existing
arcs and seven rational edge budgets. No angle chain, fitted multiplier,
two-state partition, or replacement row table is introduced. Center
separation then supplies the whole core/core pair inequality.

This Lean source remains uncompiled.
-/

@[expose] public section
open Set

namespace SquaresInCircles.Eight.Candidate.GeometricCoreMarker
open Arithmetic

/-- Curvature at most one gives the usual endpoint interpolation error,
including a degenerate interval. -/
theorem endpoint_lower {f d dd : ℝ → ℝ} {l u x L : ℝ}
    (hx : x ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hc : ∀ y ∈ Icc l u, dd y ≤ 1)
    (hl : L ≤ f l) (hu : L ≤ f u) :
    L-(u-l)^2/8 ≤ f x := by
  let g : ℝ → ℝ := fun y => f y-(y-l)*(y-u)/2
  let g' : ℝ → ℝ := fun y => d y-(2*y-l-u)/2
  have hdg (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (g' y) y := by
    convert (hd y hy).sub
      ((((hasDerivAt_id y).sub_const l).mul ((hasDerivAt_id y).sub_const u)).div_const 2)
      using 1 <;> dsimp [g,g'] <;> ring
  have hddg (y : ℝ) (hy : y ∈ Icc l u) :
      HasDerivAt g' (dd y-1) y := by
    convert (hdd y hy).sub
      (((((hasDerivAt_id y).const_mul 2).sub_const l).sub_const u).div_const 2)
      using 1 <;> dsimp [g'] <;> ring
  have hconcave : ConcaveOn ℝ (Icc l u) g :=
    concave_of_deriv2 hdg hddg (fun y hy => by linarith [hc y hy])
  have hmin := hconcave.min_le_of_mem_Icc
    ⟨le_rfl,hx.1.trans hx.2⟩ ⟨hx.1.trans hx.2,le_rfl⟩ hx
  have hends : L ≤ min (g l) (g u) := by
    exact le_min (by simpa [g] using hl) (by simpa [g] using hu)
  have hbound := hends.trans hmin
  dsimp [g] at hbound
  nlinarith [sq_nonneg (2*x-l-u)]

/-- A bound on the absolute second derivative controls both sides. -/
theorem endpoint_bounds {f d dd : ℝ → ℝ} {l u x L U : ℝ}
    (hx : x ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hc : ∀ y ∈ Icc l u, -1 ≤ dd y ∧ dd y ≤ 1)
    (hl : L ≤ f l ∧ f l ≤ U) (hu : L ≤ f u ∧ f u ≤ U) :
    L-(u-l)^2/8 ≤ f x ∧ f x ≤ U+(u-l)^2/8 := by
  refine ⟨endpoint_lower hx hd hdd (fun y hy => (hc y hy).2) hl.1 hu.1,?_⟩
  have h := endpoint_lower (f := fun y => -f y)
    (d := fun y => -d y) (dd := fun y => -dd y) (L := -U) hx
    (fun y hy => (hd y hy).neg) (fun y hy => (hdd y hy).neg)
    (fun y hy => by linarith [(hc y hy).1])
    (by linarith [hl.2]) (by linarith [hu.2])
  linarith

noncomputable def chartMarker (positive : Bool) (c q x : ℝ) : ℝ :=
  (if positive then Real.arctan x else -Real.arctan x)-(c+(7/12)*q*x)

noncomputable def chartFirst (positive : Bool) (q x : ℝ) : ℝ :=
  (if positive then 1/(1+x^2) else -(1/(1+x^2)))-(7/12)*q

noncomputable def chartSecond (positive : Bool) (x : ℝ) : ℝ :=
  if positive then -2*x/(1+x^2)^2 else 2*x/(1+x^2)^2

theorem chart_deriv (positive : Bool) (c q x : ℝ) :
    HasDerivAt (chartMarker positive c q) (chartFirst positive q x) x := by
  have hlin := (hasDerivAt_const x c).add
    ((hasDerivAt_id x).const_mul ((7/12)*q))
  cases positive
  · convert (Real.hasDerivAt_arctan x).neg.sub hlin using 1 <;>
      dsimp [chartMarker,chartFirst] <;> ring
  · convert (Real.hasDerivAt_arctan x).sub hlin using 1 <;>
      dsimp [chartMarker,chartFirst] <;> ring

theorem chart_deriv2 (positive : Bool) (q x : ℝ) :
    HasDerivAt (chartFirst positive q) (chartSecond positive x) x := by
  have hd : HasDerivAt (fun y : ℝ => 1/(1+y^2)) (-2*x/(1+x^2)^2) x := by
    convert (hasDerivAt_const x (1:ℝ)).div
      ((hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_id x).pow 2))
      (by positivity : (1+x^2:ℝ) ≠ 0) using 1 <;> ring
  cases positive
  · convert hd.neg.sub_const ((7/12)*q) using 1 <;>
      dsimp [chartFirst,chartSecond] <;> ring
  · convert hd.sub_const ((7/12)*q) using 1 <;>
      dsimp [chartFirst,chartSecond] <;> ring

theorem chart_curvature (positive : Bool) {x : ℝ} (hx : 0 ≤ x) :
    -1 ≤ chartSecond positive x ∧ chartSecond positive x ≤ 1 := by
  have hd : 0<(1+x^2)^2 := by positivity
  have hnon : 0 ≤ 2*x/(1+x^2)^2 := div_nonneg (by linarith) hd.le
  have hupper : 2*x/(1+x^2)^2 ≤ 1 := by
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (x-1),sq_nonneg x,sq_nonneg (x^2)]
  cases positive <;> dsimp [chartSecond] <;> constructor <;> nlinarith

/-- The exact error applies to any affine side label, regardless of slope. -/
theorem chart_bounds (positive : Bool) (c q : ℝ) {l u x L U : ℝ}
    (hl0 : 0 ≤ l) (hx : x ∈ Icc l u)
    (hl : L ≤ chartMarker positive c q l ∧ chartMarker positive c q l ≤ U)
    (hu : L ≤ chartMarker positive c q u ∧ chartMarker positive c q u ≤ U) :
    L-(u-l)^2/8 ≤ chartMarker positive c q x ∧
      chartMarker positive c q x ≤ U+(u-l)^2/8 :=
  endpoint_bounds hx (fun y _ => chart_deriv positive c q y)
    (fun y _ => chart_deriv2 positive q y)
    (fun y hy => chart_curvature positive (hl0.trans hy.1)) hl hu

def markerLower (i : Vertex) : ℚ :=
  ![-383/1000,-323/1000,-368/1000,-329/1000,-88/1000,-319/1000,-342/1000] i

def baseUpper (i : Vertex) : ℚ :=
  ![90/1000,-120/1000,100/1000,134/1000,96/1000,-12/1000,-111/1000] i

/-- The positive D marker is allowed its actual larger range. Its outgoing
core/core quarter pair is excluded by geometry, rather than a false bound. -/
def markerUpper (i : Vertex) (positive : Bool) : ℚ :=
  if i=5 ∧ positive=true then 643/1000 else baseUpper i

def interpolationError (s : ArcData) : ℚ :=
  if s.tangent.hi ≤ 6/7 then (s.tangent.hi-s.tangent.lo)^2/8 else 0

def endpointMarker (s : ArcData) (e : ArctanEndpoint) : QInterval :=
  (if s.positive then e.output else e.output.neg).sub
    (QInterval.point (s.label.c+(7/12)*s.label.q*e.input))

/-- Four explicit rational endpoint inequalities per original core arc.
No additional state intervals or coefficient lists are supplied. -/
def ArcValid (s : ArcData) (lo hi : ArctanEndpoint) : Prop :=
  s.label.p=0 ∧ (6/7<s.tangent.hi → s.label.q=0) ∧
    (0 ≤ s.tangent.lo ∧ s.tangent.lo ≤ s.tangent.hi ∧ s.tangent.hi ≤ 1) ∧
    (s.role=6 → s.positive=false) ∧
    (markerLower s.role+interpolationError s ≤ (endpointMarker s lo).lo ∧
      (endpointMarker s lo).hi ≤ markerUpper s.role s.positive-interpolationError s) ∧
    (markerLower s.role+interpolationError s ≤ (endpointMarker s hi).lo ∧
      (endpointMarker s hi).hi ≤ markerUpper s.role s.positive-interpolationError s)

def MarkersValid (K : AffineCover) (M : AffineTableMeta) : Prop :=
  ∀ k : Fin M.arcs.length, (arcAt M k).outer=false →
    ArcValid (arcAt M k) (K.endpointAt k).1 (K.endpointAt k).2

def BudgetsValid (M : AffineTableMeta) : Prop :=
  ∀ i, 0 ≤ M.charge i ∧
    M.target i ≤ 4/3-baseUpper i+markerLower (next i)-(M.charge i)*(21/100)

instance (s : ArcData) (lo hi : ArctanEndpoint) : Decidable (ArcValid s lo hi) := by
  unfold ArcValid
  infer_instance

instance (K : AffineCover) (M : AffineTableMeta) : Decidable (MarkersValid K M) := by
  unfold MarkersValid
  infer_instance

instance (M : AffineTableMeta) : Decidable (BudgetsValid M) := by
  unfold BudgetsValid
  infer_instance

theorem endpoint_marker_mem (s : ArcData) (e : ArctanEndpoint) (he : e.NumericValid) :
    (endpointMarker s e).Mem (chartMarker s.positive s.label.c s.label.q e.input) := by
  have h := he.sound
  cases hp : s.positive <;>
    simp only [endpointMarker,hp,Bool.false_eq_true,if_false,if_true,
      QInterval.Mem,QInterval.sub,QInterval.add,QInterval.neg,QInterval.point,chartMarker] <;>
    push_cast <;> constructor <;> linarith [h.1,h.2]

/-- The same original label is controlled at every point of its closed
arc. In particular, both labels at a shared endpoint are individually valid. -/
theorem arc_marker_mem {K : AffineCover} {M : AffineTableMeta}
    (hK : K.EndpointsValid M) (hv : MarkersValid K M)
    {k : Fin M.arcs.length} {a b : ℝ}
    (hs : (arcAt M k).Contains M.radius a b) (hcore : (arcAt M k).outer=false) :
    (markerLower (arcAt M k).role:ℝ) ≤
        Real.arctan ((arcAt M k).sign*b/a)-(arcAt M k).label.eval a b ∧
      Real.arctan ((arcAt M k).sign*b/a)-(arcAt M k).label.eval a b ≤
        markerUpper (arcAt M k).role (arcAt M k).positive := by
  let s := arcAt M k
  rcases hv k hcore with ⟨hp,hq,hrange,hE,hlo,hhi⟩
  have hl := endpoint_marker_mem s (K.endpointAt k).1 (hK k).1
  have hu := endpoint_marker_mem s (K.endpointAt k).2 (hK k).2.1
  rw [(hK k).2.2.1] at hl
  rw [(hK k).2.2.2] at hu
  have hleft :
      ((markerLower s.role+interpolationError s:ℚ):ℝ) ≤
        chartMarker s.positive s.label.c s.label.q s.tangent.lo ∧
      chartMarker s.positive s.label.c s.label.q s.tangent.lo ≤
        ((markerUpper s.role s.positive-interpolationError s:ℚ):ℝ) := by
    constructor
    · have hq' : ((markerLower s.role+interpolationError s:ℚ):ℝ) ≤
          ((endpointMarker s (K.endpointAt k).1).lo:ℝ) := by exact_mod_cast hlo.1
      exact hq'.trans hl.1
    · have hq' : ((endpointMarker s (K.endpointAt k).1).hi:ℝ) ≤
          ((markerUpper s.role s.positive-interpolationError s:ℚ):ℝ) := by exact_mod_cast hlo.2
      exact hl.2.trans hq'
  have hright :
      ((markerLower s.role+interpolationError s:ℚ):ℝ) ≤
        chartMarker s.positive s.label.c s.label.q s.tangent.hi ∧
      chartMarker s.positive s.label.c s.label.q s.tangent.hi ≤
        ((markerUpper s.role s.positive-interpolationError s:ℚ):ℝ) := by
    constructor
    · have hq' : ((markerLower s.role+interpolationError s:ℚ):ℝ) ≤
          ((endpointMarker s (K.endpointAt k).2).lo:ℝ) := by exact_mod_cast hhi.1
      exact hq'.trans hu.1
    · have hq' : ((endpointMarker s (K.endpointAt k).2).hi:ℝ) ≤
          ((markerUpper s.role s.positive-interpolationError s:ℚ):ℝ) := by exact_mod_cast hhi.2
      exact hu.2.trans hq'
  have hx : (b/a) ∈ Icc (s.tangent.lo:ℝ) (s.tangent.hi:ℝ) := hs.2.2.2.1
  have hcurve := hs.2.2.2.2
  by_cases hside : s.tangent.hi ≤ 6/7
  · have ha : a=7/12 := by
      simp [ArcData.OnCurve,hcore,hside] at hcurve
      exact hcurve.1
    have hb : b=(7/12)*(b/a) := by rw [ha]; ring
    have hbound := chart_bounds s.positive s.label.c s.label.q
      (by exact_mod_cast hrange.1) hx hleft hright
    have hid : Real.arctan (s.sign*b/a)-s.label.eval a b=
        chartMarker s.positive s.label.c s.label.q (b/a) := by
      cases hpos : s.positive <;>
        simp [ArcData.sign,hpos,AffineLabel.eval,hp,chartMarker,neg_div,Real.arctan_neg] <;>
        linear_combination -(s.label.q:ℝ)*hb
    change (markerLower s.role:ℝ) ≤ _ ∧ _ ≤ markerUpper s.role s.positive
    rw [hid]
    simp only [interpolationError,hside,if_true] at hbound
    push_cast at hbound
    constructor <;> linarith [hbound.1,hbound.2]
  · have hq0 : s.label.q=0 := hq (lt_of_not_ge hside)
    have hloAngle := Real.arctan_mono hx.1
    have hhiAngle := Real.arctan_mono hx.2
    change (markerLower s.role:ℝ) ≤ _ ∧ _ ≤ markerUpper s.role s.positive
    cases hpos : s.positive <;>
      simp only [chartMarker,hpos,Bool.false_eq_true,if_false,if_true,
        interpolationError,hside,hq0,Rat.cast_zero,mul_zero,zero_mul,add_zero,
        sub_zero] at hleft hright <;>
      simp [ArcData.sign,hpos,AffineLabel.eval,hp,hq0,neg_div,Real.arctan_neg] <;>
      constructor <;> linarith [hleft.1,hleft.2,hright.1,hright.2]

/-- A selected core arc supplies the geometric core state even at a radial
chart junction; the actual cycle's radial tag need not be unique there. -/
theorem arc_core_state {s : ArcData} {Q a b : ℝ}
    (hs : s.Contains Q a b) (hcore : s.outer=false) :
    CorePairGeometry.CoreState a b := by
  have hcurve := hs.2.2.2.2
  by_cases hside : s.tangent.hi ≤ 6/7
  · simp [ArcData.OnCurve,hcore,hside] at hcurve
    exact Or.inl ⟨hcurve.1,hs.2.1,hcurve.2⟩
  · simp [ArcData.OnCurve,hcore,hside] at hcurve
    exact Or.inr ⟨hcurve.1,hs.2.2.1,hcurve.2⟩

/-- The core gap estimate depends on the two containing core charts, not
on a choice of radial tag at a point shared by boundary curves. -/
theorem selected_core_gap {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hs : CorePairGeometry.CoreState (C.a i) (C.b i))
    (ht : CorePairGeometry.CoreState (C.a (next i)) (C.b (next i))) :
    (4/3:ℝ)<angleGap C.beta i := by
  have hrsq := CorePairGeometry.core_radius_sq hs
  have hssq := CorePairGeometry.core_radius_sq ht
  have hr0 := C.radius_pos i
  have hs0 := C.radius_pos (next i)
  have hr : C.radius i<4/5 := by nlinarith [C.radius_sq i]
  have hs' : C.radius (next i)<4/5 := by nlinarith [C.radius_sq (next i)]
  have hd := centers_distance_sq_ge_one (C.square i) (C.square (next i))
    (C.feasible i).disjoint
  rw [polar_pair_distance (C.center_cos i) (C.center_sin i)
    (C.center_cos (next i)) (C.center_sin (next i))] at hd
  have hcos : Real.cos (angleGap C.beta i)=Real.cos (C.beta (next i)-C.beta i) := by
    by_cases hlast : i=6 <;> simp [angleGap,hlast,Real.cos_add_two_pi]
  rw [← hcos] at hd
  change 1 ≤ C.radius i^2+C.radius (next i)^2-
    2*C.radius i*C.radius (next i)*Real.cos (angleGap C.beta i) at hd
  have hmax := CorePairGeometry.chord_upper ⟨hr0.le,hr.le⟩ ⟨hs0.le,hs'.le⟩
  have hfour : (7/32:ℝ)<Real.cos (4/3:ℝ) := by
    have hh := cos_lower_six (x := (4/3:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  by_contra! hbad
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (C.gap_pos i).le
    (by linarith [Real.pi_gt_three] : (4/3:ℝ) ≤ Real.pi) hbad
  have hp := mul_pos (mul_pos hr0 hs0)
    (sub_pos.mpr (lt_of_lt_of_le hfour hm))
  nlinarith

/-- The full two-state core/core cost follows from the original shared
markers, center separation, and seven fixed rational edge budgets. -/
theorem pair_bound {K : AffineCover} {M : AffineTableMeta}
    (hK : K.EndpointsValid M) (hmarkers : MarkersValid K M) (hbudgets : BudgetsValid M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C)
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role=i) (hti : (arcAt M t).role=next i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i=C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i)=C.sigma (next i)*C.b (next i))
    (hsource : (arcAt M s).outer=false) (htarget : (arcAt M t).outer=false)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (M.target i:ℝ)<chargedCost (arcAt M s).label (arcAt M t).label
      (M.charge i) (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phi F.theta i) := by
  have hkeep := GeometricAffine.feasible_not_excluded C F hsi hs ht hσ hτ j hj
  have hupper : markerUpper (arcAt M s).role (arcAt M s).positive=baseUpper i := by
    rw [hsi]
    unfold markerUpper
    split_ifs with hD
    · have htargetRole : (arcAt M t).role=6 := by rw [hti,hD.1]; rfl
      have hnegative := (hmarkers t htarget).2.2.2.1 htargetRole
      exact (hkeep (Or.inr (Or.inr
        ⟨by rw [hsi,hD.1]; norm_num [word],hsource,htarget,hD.2,hnegative⟩))).elim
    · rfl
  have hms := arc_marker_mem hK hmarkers hs hsource
  have hmt := arc_marker_mem hK hmarkers ht htarget
  have hαs : Real.arctan ((arcAt M s).sign*C.b i/C.a i)=C.alpha i := by
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,hσ]
  have hαt : Real.arctan ((arcAt M t).sign*C.b (next i)/C.a (next i))=
      C.alpha (next i) := by
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,hτ]
  rw [hαs,hupper,hsi] at hms
  rw [hαt,hti] at hmt
  have hg := selected_core_gap C i (arc_core_state hs hsource) (arc_core_state ht htarget)
  have hw : frameCharge (phi F.theta i)<(21/100:ℝ) := by
    simpa [frameCharge,periodicFrameCost,add_comm] using
      CorePairGeometry.charge_upper (phi F.theta i)
  have hcharge : 0 ≤ (M.charge i:ℝ) := by exact_mod_cast (hbudgets i).1
  have hcharged := mul_le_mul_of_nonneg_left hw.le hcharge
  have hbudget : (M.target i:ℝ) ≤
      4/3-(baseUpper i:ℝ)+(markerLower (next i):ℝ)-(M.charge i:ℝ)*(21/100) := by
    exact_mod_cast (hbudgets i).2
  have he := F.physical_angle i
  dsimp [chargedCost]
  linarith [hms.2,hmt.1]

end SquaresInCircles.Eight.Candidate.GeometricCoreMarker
