module

public import SquaresInCircles.Eight.TableFree.ContactArcMinimum
public import SquaresInCircles.Common.Analysis

/-!
# One-sided contact-minimum derivatives

Uncompiled calculus draft for the explicit boundary descents in the
hand proofs. A differentiable minimum at a right endpoint has a
nonpositive derivative; reflection gives the left-endpoint statement.
The proofs retain genuine intervals of feasible original contacts.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.ContactMinimumDerivatives

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

/-- Second-order necessary condition on an explicitly supplied open contact arc. -/
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

end SquaresInCircles.Eight.TableFree.ContactMinimumDerivatives
