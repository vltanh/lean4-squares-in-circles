module

public import SquaresInCircles.Eight.TableFree.FirstNegativeContact
public import SquaresInCircles.Eight.TableFree.EndpointPrinciples
public import SquaresInCircles.Eight.TableFree.AlignedNegativeEH0

/-!
# Strict retained mixed slack at the first actual GA0 contact

Uncompiled source. The first contact is selected by the actual GA axis,
independently of the mixed slack. The low mixed derivative integrates up to
that contact. For the high mixed owner, a compact minimum rules out passage
through the proved small-slack derivative strip. Thus the high-anchor cuts
at the first contact and a strictly positive physical mixed margin hold at
the same point.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree

/-- A negative derivative on the nonpositive sublevel cannot cross upwards
from a negative left endpoint to a nonnegative right endpoint. The derivative
is needed only in the open interval. -/
theorem left_sublevel_barrier {f df : ℝ → ℝ} {l u : ℝ}
    (hlu : l<u) (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Ioo l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Ioo l u, f x≤0 → df x<0)
    (hu : 0≤f u) : 0≤f l := by
  by_contra! hl
  obtain ⟨z,hz,hzvalue⟩ := intermediate_value_Icc hlu.le hc
    (show f l/2∈Icc (f l) (f u) by constructor <;> linarith)
  have hlz : l<z := by
    apply lt_of_le_of_ne hz.1
    intro heq
    rw [← heq] at hzvalue
    linarith
  have hzt : z<u := by
    apply lt_of_le_of_ne hz.2
    intro heq
    rw [heq] at hzvalue
    linarith
  have hsub : Icc z u⊆Icc l u := Icc_subset_Icc hz.1 le_rfl
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc z u).Nonempty from ⟨z,⟨le_rfl,hzt.le⟩⟩) (hc.mono hsub)
  have hfm : f m<0 := by
    have hh : f m≤f z := hmin (show z∈Icc z u from ⟨le_rfl,hzt.le⟩)
    linarith
  have hmu : m<u := by
    apply lt_of_le_of_ne hm.2
    intro heq
    rw [heq] at hfm
    linarith
  have hlm : l<m := hlz.trans_le hm.1
  have hbetter := NegativeContact.eventually_right_lt (hd m ⟨hlm,hmu⟩)
    (hneg m ⟨hlm,hmu⟩ hfm.le)
  have hbound : ∀ᶠ x in 𝓝[>] m, x<u :=
    (eventually_lt_nhds hmu).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,hmx,hxu,hfx⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hbetter)).exists
  have hmx' : m<x := hmx
  have hh : f m≤f x := hmin (show x∈Icc z u from ⟨hm.1.trans hmx'.le,hxu.le⟩)
  linarith

namespace AlignedNegative
open PrimaryCap
namespace FirstHard

variable {q t : ℝ} {H G A : SignedPoint} {I : Source q t H G A}

theorem low_mixed_slack (O : FirstHard I) {E : SignedPoint} {e : ℝ}
    (hq : q≤qCap) (hEy : E.y≤0) (he : |e+t|≤7/10)
    (hf : quarterFeasible E H (e+t) 0) :
    e+O.angle∈Icc 0 (7/10 : ℝ) ∧
      0<lowMixedSlack H.circle (A.a-1/2) e E O.angle := by
  obtain ⟨m,hm,hem,hmhard,_⟩ := I.eh0_hard_point hq hEy he hf
  have hmr := O.maximal m ⟨hm.1,hm.2.le⟩ hmhard
  have heR : e+O.angle∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [hem.1,hem.2,O.angle_mem.2,(abs_le.mp he).2]
  have heX (x : ℝ) (hx : x∈Icc O.angle t) : e+x∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [heR.1,hx.1,hx.2,(abs_le.mp he).2]
  let L := lowMixedSlack H.circle (A.a-1/2) e E
  let dL := lowMixedDerivative H.circle (A.a-1/2) e
  have hderiv (x : ℝ) (hx : x∈Icc O.angle t) : HasDerivAt L (dL x) x := by
    have hx0 : 0≤x := O.angle_mem.1.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    exact lowMixedSlack_hasDerivAt E hc
      (I.path_geometry hq ⟨hx0,hx.2⟩).2.2.2.2.2.2
  have hcont : ContinuousOn L (Icc O.angle t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hLt : 0≤L t := by
    have hN := (I.normalize hq).retains_mixed hq he (Or.inl rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    dsimp [L]
    rw [lowMixedSlack_actual E (heX t ⟨O.angle_mem.2.le,le_rfl⟩)]
    exact sub_nonneg.mpr hN
  have hreserve := derivative_reserve (f := fun x => -L x)
    (df := fun x => -dL x) (k := 3/50) hcont.neg
    (fun x hx => (hderiv x (Ioo_subset_Icc_self hx)).fun_neg)
    (fun x hx => by
      have hh := I.lowMixedDerivative_negative hq
        ⟨O.angle_mem.1.trans_lt hx.1,hx.2.le⟩
        (O.later_unavailable ⟨hx.1,hx.2.le⟩) (heX x (Ioo_subset_Icc_self hx))
      dsimp [dL]
      linarith)
    (show O.angle∈Icc O.angle t from ⟨le_rfl,O.angle_mem.2.le⟩)
    (show t∈Icc O.angle t from ⟨O.angle_mem.2.le,le_rfl⟩) O.angle_mem.2.le
  have hmovement : 0<(3/50 : ℝ)*(t-O.angle) := by
    exact mul_pos (by norm_num) (sub_pos.mpr O.angle_mem.2)
  exact ⟨heR,by dsimp [L] at hLt hreserve; linarith⟩

theorem high_mixed_slack (O : FirstHard I) {E : SignedPoint} {e : ℝ}
    (hq : q≤qCap) (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    e+O.angle∈Icc 0 (11/50 : ℝ) ∧
      0<highMixedSlack H.circle (A.a-1/2) e E O.angle := by
  obtain ⟨m,hm,hem,hmhard,_⟩ := I.eh1_hard_point hq hEs hEc hEy he hf
  have hmr := O.maximal m ⟨hm.1,hm.2.le⟩ hmhard
  have heR : e+O.angle∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hem.1,O.angle_mem.2,(abs_le.mp he).2]
  have heX (x : ℝ) (hx : x∈Icc O.angle t) : e+x∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [heR.1,hx.1,hx.2,(abs_le.mp he).2]
  let L := highMixedSlack H.circle (A.a-1/2) e E
  let dL := highMixedDerivative H.circle (A.a-1/2) e E
  let F : ℝ → ℝ := fun x => L x-(t-x)/4000
  let dF : ℝ → ℝ := fun x => dL x+1/4000
  have hderiv (x : ℝ) (hx : x∈Icc O.angle t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := O.angle_mem.1.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hL := highMixedSlack_hasDerivAt (e := e) E hc
      (I.path_geometry hq ⟨hx0,hx.2⟩).2.2.2.2.2.2
    have h := hL.fun_sub (((hasDerivAt_id' x).const_sub t).div_const 4000)
    convert h using 1
    show dL x+1/4000=_
    ring
  have hcont : ContinuousOn F (Icc O.angle t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hN := (I.normalize hq).retains_mixed hq
      (show |e+t|≤7/10 by linarith) (Or.inr rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    have hwide : e+t∈Icc 0 (7/10 : ℝ) := by
      have hh := heX t ⟨O.angle_mem.2.le,le_rfl⟩
      exact ⟨hh.1,by linarith [hh.2]⟩
    have h1 : L t=quarterProjection E (movingAnchor H.circle (A.a-1/2) t) (e+t) 1-
        edgeWidth (e+t) := highMixedSlack_actual E hwide
    have hN' : edgeWidth (e+t)≤quarterProjection E (movingAnchor H.circle (A.a-1/2) t) (e+t) 1 :=
      hN
    show 0≤L t-(t-t)/4000
    rw [h1]
    linarith
  have hbarrier : 0≤F O.angle := left_sublevel_barrier O.angle_mem.2 hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx hFx => by
      have hx0 : 0<x := O.angle_mem.1.trans_lt hx.1
      have hsmall : L x≤1/1000 := by
        dsimp [F] at hFx
        linarith [I.tilt_cap]
      have hh := I.highMixedDerivative_negative hq hEc hEy
        ⟨hx0,hx.2.le⟩ (O.later_unavailable ⟨hx.1,hx.2.le⟩)
        (heX x (Ioo_subset_Icc_self hx)) hsmall
      dsimp [dF,dL]
      linarith) hFt
  have hmovement : 0<(t-O.angle)/4000 :=
    div_pos (sub_pos.mpr O.angle_mem.2) (by norm_num)
  exact ⟨heR,by dsimp [F,L] at hbarrier; linarith⟩

end FirstHard
end AlignedNegative
end SquaresInCircles.Eight.TableFree
