module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Eight.Owners.Endpoint.Principles

/-!
# Eight squares: one-sided derivatives at a contact minimum

A differentiable function with a minimum at the right endpoint of an interval of feasible contacts
has a nonpositive derivative there (`right_endpoint`); reflection gives the left endpoint
(`left_endpoint`). At a minimum inside an open arc the second derivative is nonnegative
(`second_nonnegative`).
-/

section
/-!
## Minima on contact arcs

The compactness and local-curve argument that moves a feasible pair to an alignment, a sign
junction or a diagonal, with no discretization of the contact parameter. A cost that is strictly
concave along a feasible contact curve has no minimum inside the curve
(`not_minimum_on_strictly_concave_curve`). The region of nonnegative contact in a closed rectangle
is compact (`compact_contact_region`), so the cost has a minimum there (`contact_region_minimum`),
and at a minimum where the cost decreases in `y` the upper side or the contact is reached
(`upper_or_contact_at_minimum`). The curvature and feasibility of each curve come from the
formulas of the paired-primary modules.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

/-- An open real neighborhood contains a two-sided closed interval. -/
theorem exists_closed_interval_in_open {s : Set ℝ} (hs : IsOpen s)
    {x : ℝ} (hx : x∈s) :
    ∃ ε : ℝ, 0<ε ∧ Icc (x-ε) (x+ε)⊆s := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro y hy
  apply hsub
  change dist y x<δ
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith [hy.1,hy.2]

/-- A minimum of the cost over a set of states is not an interior point of a feasible contact
curve along which the cost is strongly concave. -/
theorem not_minimum_on_strictly_concave_curve
    {X : Type*} {s : Set X} {cost : X → ℝ} {p : X}
    (hp : ∀ z∈s, cost p≤cost z)
    {curve : ℝ → X} {value dvalue ddvalue : ℝ → ℝ}
    {O : Set ℝ} (hO : IsOpen O) {x k : ℝ}
    (hx : x∈O) (hk : 0<k)
    (he : curve x=p)
    (hfeasible : ∀ y∈O, curve y∈s)
    (hvalue : ∀ y∈O, cost (curve y)=value y)
    (hd : ∀ y∈O, HasDerivAt value (dvalue y) y)
    (hdd : ∀ y∈O, HasDerivAt dvalue (ddvalue y) y)
    (hcurv : ∀ y∈O, ddvalue y≤-k) : False := by
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hx
  have hmid : x∈Ioo (x-ε) (x+ε) := by constructor <;> linarith
  have hend := strict_endpoint_of_second_derivative hk hmid
    (fun y hy => hd y (hsub hy)) (fun y hy => hdd y (hsub hy))
    (fun y hy => hcurv y (hsub hy))
  have hlo : x-ε∈O := hsub ⟨le_rfl,by linarith⟩
  have hhi : x+ε∈O := hsub ⟨by linarith,le_rfl⟩
  have hl := hp (curve (x-ε)) (hfeasible _ hlo)
  have hu := hp (curve (x+ε)) (hfeasible _ hhi)
  rw [← he,hvalue x hx,hvalue _ hlo] at hl
  rw [← he,hvalue x hx,hvalue _ hhi] at hu
  rcases hend with h | h <;> linarith

/-- A continuous nonnegative-contact region of a closed rectangle is compact. -/
theorem compact_contact_region {l u a b : ℝ} {contact : ℝ × ℝ → ℝ}
    (hc : Continuous contact) :
    IsCompact {p : ℝ × ℝ | p.1∈Icc l u ∧ p.2∈Icc a b ∧ 0≤contact p} := by
  have hbox : IsCompact (Icc l u ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed {p : ℝ × ℝ | 0≤contact p} :=
    isClosed_le continuous_const hc
  convert hbox.inter_right hclosed using 1
  ext p
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]

theorem contact_region_minimum {l u a b : ℝ} {contact cost : ℝ × ℝ → ℝ}
    (hc : Continuous contact) (hf : Continuous cost)
    {p₀ : ℝ × ℝ} (hp₀ : p₀.1∈Icc l u ∧ p₀.2∈Icc a b ∧ 0≤contact p₀) :
    ∃ p : ℝ × ℝ,
      (p.1∈Icc l u ∧ p.2∈Icc a b ∧ 0≤contact p) ∧
      cost p≤cost p₀ ∧
      ∀ z : ℝ × ℝ, z.1∈Icc l u → z.2∈Icc a b → 0≤contact z → cost p≤cost z := by
  obtain ⟨p,hp,hm⟩ := (compact_contact_region hc).exists_isMinOn ⟨p₀,hp₀⟩
    hf.continuousOn
  exact ⟨p,hp,hm hp₀,fun z hz₁ hz₂ hz₃ => hm ⟨hz₁,hz₂,hz₃⟩⟩

/-- At a minimum whose cost strictly decreases as `y` increases, either `y` is the upper side `b`
or the contact vanishes. The proof uses the intermediate value theorem, which also covers a
nondifferentiable sign junction of the outer circle. -/
theorem upper_or_contact_at_minimum
    {l u a b x y : ℝ} {contact cost : ℝ × ℝ → ℝ}
    (hxy : x∈Icc l u ∧ y∈Icc a b ∧ 0≤contact (x,y))
    (hmin : ∀ z : ℝ × ℝ, z.1∈Icc l u → z.2∈Icc a b → 0≤contact z →
      cost (x,y)≤cost z)
    (hc : Continuous (fun z : ℝ => contact (x,z)))
    (hcost : StrictAntiOn (fun z : ℝ => cost (x,z)) (Icc a b)) :
    y=b ∨ contact (x,y)=0 := by
  by_cases hy : y=b
  · exact Or.inl hy
  right
  by_contra hnot
  have hyb : y<b := lt_of_le_of_ne hxy.2.1.2 hy
  have hpos : 0<contact (x,y) := lt_of_le_of_ne hxy.2.2 (Ne.symm hnot)
  by_cases hb : 0≤contact (x,b)
  · have hf := hmin (x,b) hxy.1 ⟨by linarith [hxy.2.1.1],le_rfl⟩ hb
    have hlt := hcost hxy.2.1 ⟨by linarith [hxy.2.1.1],le_rfl⟩ hyb
    exact (not_lt_of_ge hf) hlt
  · have hbneg : contact (x,b)<0 := lt_of_not_ge hb
    have himage : 0∈(fun z : ℝ => -contact (x,z)) '' Icc y b := by
      apply intermediate_value_Icc hyb.le hc.neg.continuousOn
      constructor <;> simp only [Pi.neg_apply] <;> linarith
    obtain ⟨z,hz,hzval⟩ := himage
    have hz0 : contact (x,z)=0 := by simp only at hzval; linarith
    have hyz : y<z := by
      by_contra! h
      have he : z=y := le_antisymm h hz.1
      rw [he] at hz0
      linarith
    have hzab : z∈Icc a b := ⟨hxy.2.1.1.trans hz.1,hz.2⟩
    have hf := hmin (x,z) hxy.1 hzab hz0.ge
    have hlt := hcost hxy.2.1 hzab hyz
    exact (not_lt_of_ge hf) hlt

end SquaresInCircles.Eight
end
end
end

section
/-!
## Feasible-contact continuation without an assumed feasible path

The first theorem handles a derivative estimate proved
only at feasible points. A maximum on a compact interval and its left
inward tangent rule out a first loss of feasibility. The second theorem
handles a derivative whose sign changes only from negative to positive;
no interior root or subdivision is chosen.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight

/-- At a maximum that is not the left endpoint, a negative derivative is
impossible. The derivative at the right endpoint is included. -/
theorem not_negative_at_rightward_maximum {f : ℝ → ℝ} {a b m d : ℝ}
    (hm : m∈Icc a b) (ham : a< m)
    (hmax : IsMaxOn f (Icc a b) m) (hd : HasDerivAt f d m) : 0≤d := by
  have ha : a∈Icc a b := ⟨le_rfl,hm.1.trans hm.2⟩
  have hsegment : segment ℝ m a ⊆ Icc a b :=
    (convex_Icc a b).segment_subset hm ha
  have hcone := sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hlocal : IsLocalMaxOn f (Icc a b) m := hmax.isLocalMaxOn
  have h := hlocal.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt hcone
  have hproduct : d*(a-m)≤0 := by simpa [mul_comm] using h
  by_contra! hn
  have hp := mul_pos_of_neg_of_neg hn (sub_neg.mpr ham)
  linarith

/-- Negative derivative at every feasible point forces strict improvement
when moving left from a feasible right endpoint. Feasibility on the path
is a conclusion, not a premise. -/
theorem feasible_left_continuation {f df : ℝ → ℝ} {l u b : ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Icc l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Icc l u, b≤f x → df x<0)
    (hu : b≤f u) :
    ∀x∈Ico l u, f u<f x := by
  intro x hx
  by_contra! hbad
  have hsub : Icc x u ⊆ Icc l u := Icc_subset_Icc hx.1 le_rfl
  have hcont := hc.mono hsub
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x u).Nonempty from ⟨u,⟨hx.2.le,le_rfl⟩⟩) hcont
  have hum : f u≤f m := hmax ⟨hx.2.le,le_rfl⟩
  by_cases hxm : x< m
  · have hnn := not_negative_at_rightward_maximum hm hxm hmax (hd m (hsub hm))
    have hn := hneg m (hsub hm) (hu.trans hum)
    linarith
  · have hmx : m=x := le_antisymm (le_of_not_gt hxm) hm.1
    have hmaxu : IsMaxOn f (Icc x u) u := by
      intro y hy
      have hymax := hmax hy
      rw [hmx] at hymax
      exact hymax.trans hbad
    have hnn := not_negative_at_rightward_maximum
      (show u∈Icc x u from ⟨hx.2.le,le_rfl⟩) hx.2 hmaxu
      (hd u ⟨hx.1.trans hx.2.le,le_rfl⟩)
    have hn := hneg u ⟨hx.1.trans hx.2.le,le_rfl⟩ hu
    linarith

/-- After continuation has established feasibility, the derivative reserve
integrates on the entire motion interval. -/
theorem feasible_left_reserve {f df : ℝ → ℝ} {l u b k : ℝ}
    (hlu : l≤u) (hk : 0<k)
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Icc l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Icc l u, b≤f x → df x≤ -k)
    (hu : b≤f u) :
    ∀x∈Icc l u, b≤f x ∧ k*(u-x)≤f x-f u := by
  have hstrict := feasible_left_continuation hc hd
    (fun x hx hfx => lt_of_le_of_lt (hneg x hx hfx) (by linarith)) hu
  have hfeas (x : ℝ) (hx : x∈Icc l u) : b≤f x := by
    rcases lt_or_eq_of_le hx.2 with hxlt | rfl
    · exact hu.trans (hstrict x ⟨hx.1,hxlt⟩).le
    · exact hu
  intro x hx
  refine ⟨hfeas x hx,?_⟩
  have hr := derivative_reserve (f := fun y => -f y)
    (df := fun y => -df y) (k := k) hc.neg
    (fun y hy => (hd y (Ioo_subset_Icc_self hy)).neg)
    (fun y hy => by
      have hh := hneg y (Ioo_subset_Icc_self hy)
        (hfeas y (Ioo_subset_Icc_self hy))
      linarith)
    hx (show u∈Icc l u from ⟨hlu,le_rfl⟩) hx.2
  linarith

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ContactMinimumDerivatives

lemma right_endpoint {f d : ℝ→ℝ} {l x : ℝ}
    (hlx : l<x) (hc : ContinuousAt d x)
    (hd : ∀u∈Icc l x, HasDerivAt f (d u) u)
    (hmin : ∀u∈Icc l x, f x≤f u) : d x≤0 := by
  by_contra! hpos
  have hN : {u : ℝ | l<u ∧ d x/2<d u}∈𝓝 x := by
    filter_upwards [lt_mem_nhds hlx,
      hc.tendsto.eventually (lt_mem_nhds (half_lt_self hpos))] with u hu hv
    exact ⟨hu,hv⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  let y := x-ε/2
  have hyx : y<x := by dsimp [y]; linarith
  have hball {u : ℝ} (hu : u∈Icc y x) : u∈Metric.ball x ε := by
    change dist u x<ε
    rw [Real.dist_eq]
    apply abs_lt.mpr
    dsimp [y] at hu
    constructor <;> linarith [hu.1,hu.2]
  have hy : l<y := (hsub (hball ⟨le_rfl,hyx.le⟩)).1
  have hdom {u : ℝ} (hu : u∈Icc y x) : u∈Icc l x :=
    ⟨hy.le.trans hu.1,hu.2⟩
  have hm : MonotoneOn (fun u => f u-(d x/2)*u) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => ((hd u (hdom hu)).fun_sub
        ((hasDerivAt_id' u).const_mul (d x/2))).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (hdom (Ioo_subset_Icc_self hu))).fun_sub
        ((hasDerivAt_id' u).const_mul (d x/2)))
      (fun u hu => by linarith [(hsub (hball (Ioo_subset_Icc_self hu))).2])
  have hh := hm ⟨le_rfl,hyx.le⟩ ⟨hyx.le,le_rfl⟩ hyx.le
  simp only at hh
  have hl := hmin y ⟨hy.le,hyx.le⟩
  nlinarith [mul_pos (half_pos hpos) (sub_pos.mpr hyx)]

lemma left_endpoint {f d : ℝ→ℝ} {x u : ℝ}
    (hxu : x<u) (hc : ContinuousAt d x)
    (hd : ∀y∈Icc x u, HasDerivAt f (d y) y)
    (hmin : ∀y∈Icc x u, f x≤f y) : 0≤d x := by
  have hc' : ContinuousAt (fun y => -d (-y)) (-x) := by
    have h1 : ContinuousAt (fun y : ℝ => -y) (-x) := continuousAt_neg
    have h2 : ContinuousAt d (-(-x)) := by simpa only [neg_neg] using hc
    exact (h2.comp h1).neg
  have hh := right_endpoint (f := fun y => f (-y)) (d := fun y => -d (-y))
    (l := -u) (x := -x) (by linarith) hc'
    (fun y hy => by
      have hdy := hd (-y) ⟨by linarith [hy.2],by linarith [hy.1]⟩
      have h : HasDerivAt (fun y => f (-y)) ((-1:ℝ)•d (-y)) y :=
        hdy.scomp y (hasDerivAt_neg' (x := y))
      simpa using h)
    (fun y hy => by
      simpa only [neg_neg] using hmin (-y) ⟨by linarith [hy.2],by linarith [hy.1]⟩)
  simpa only [neg_neg,neg_nonpos] using hh

/-- At a minimum on an open contact arc the second derivative is nonnegative. -/
lemma second_nonnegative {f d dd : ℝ→ℝ} {O : Set ℝ} {x : ℝ}
    (hO : IsOpen O) (hx : x∈O) (hmin : ∀y∈O, f x≤f y)
    (hd : ∀y∈O,HasDerivAt f (d y) y)
    (hdd : ∀y∈O,HasDerivAt d (dd y) y)
    (hc : ContinuousAt dd x) : 0≤dd x := by
  by_contra! hneg
  let k := -dd x/2
  have hk : 0<k := by dsimp [k]; linarith
  have hN : {y | y∈O ∧ dd y< -k}∈𝓝 x := by
    filter_upwards [hO.mem_nhds hx,
      hc.tendsto.eventually (gt_mem_nhds (show dd x< -k by dsimp [k]; linarith))] with y hy hz
    exact ⟨hy,hz⟩
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hN
  apply not_minimum_on_strictly_concave_curve
    (s := O) (cost := f) (p := x) hmin
    (curve := fun y : ℝ => y) (value := f) (dvalue := d) (ddvalue := dd)
    (O := Metric.ball x ε) Metric.isOpen_ball
    (show x∈Metric.ball x ε by simpa using hε) hk rfl
  · exact fun y hy => (hsub hy).1
  · exact fun _ _ => rfl
  · exact fun y hy => hd y (hsub hy).1
  · exact fun y hy => hdd y (hsub hy).1
  · exact fun y hy => (hsub hy).2.le

end SquaresInCircles.Eight.ContactMinimumDerivatives
end
end
end
