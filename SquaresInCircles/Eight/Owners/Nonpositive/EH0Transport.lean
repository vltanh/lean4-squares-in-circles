module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Words.Aligned.MixedE
public import SquaresInCircles.Eight.Owners.E.InteriorGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles

/-!
# Eight squares: the original rotated EH0 contact above H reaches E=H

The actual EH0 inequality supplies a short tangent interval.  On that
whole interval the original q-circle has a uniform projection-growth
reserve.  Moving to H's frame gives an actual E point with EH1 exact and
DE3 strictly improved.  This is an exclusion construction, so its initial
primary lift is not counted as a source-circle decrease.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveEH0Transport

def root (q b : ℝ) : ℝ := Real.sqrt (q-(b+1/2)^2)
def primary (q b : ℝ) : ℝ := root q b-1/2
def M (q α b : ℝ) : ℝ :=
  (primary q b-1/2)*Real.sin α+(b-1/2)*Real.cos α
def N (q α b : ℝ) : ℝ :=
  (primary q b-1/2)*Real.cos α-(b-1/2)*Real.sin α
def Md (q α b : ℝ) : ℝ :=
  Real.cos α-((b+1/2)/root q b)*Real.sin α

theorem root_bounds {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    (9/5:ℝ)<root q b ∧ (root q b)^2=q-(b+1/2)^2 := by
  have hy0 : 0≤b+1/2 := by linarith [hb.1]
  have hy1 : b+1/2≤3/5 := by linarith [hb.2]
  have hy2 := pow_le_pow_left₀ hy0 hy1 2
  have hr : 0<q-(b+1/2)^2 := by norm_num [qLow] at hqL; nlinarith
  have he := Real.sq_sqrt hr.le
  have hn := Real.sqrt_nonneg (q-(b+1/2)^2)
  refine ⟨?_,he⟩
  dsimp [root]
  norm_num [qLow] at hqL
  nlinarith

theorem primary_bounds {q b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (1/10:ℝ)) :
    (13/10:ℝ)<primary q b ∧ primary q b<283/200 := by
  have hr := root_bounds hqL hb
  have hminor := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤b+1/2 by linarith [hb.1]) 2
  have hQ := hqU
  norm_num [qCap] at hQ
  dsimp [primary]
  constructor
  · linarith [hr.1]
  · nlinarith [hr.2]

theorem root_ratio {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    0≤(b+1/2)/root q b ∧ (b+1/2)/root q b<1/3 := by
  have hr : 0<root q b := by linarith [(root_bounds hqL hb).1]
  constructor
  · exact div_nonneg (by linarith [hb.1]) hr.le
  · apply (div_lt_iff₀ hr).2
    linarith [(root_bounds hqL hb).1,hb.2]

theorem primary_hasDerivAt {q b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    HasDerivAt (primary q) (-((b+1/2)/root q b)) b := by
  have hr := root_bounds hqL hb
  have hr0 : 0<root q b := by linarith [hr.1]
  have harg : q-(b+1/2)^2≠0 := by nlinarith [hr.2]
  have hd := ((hasDerivAt_const b q).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt harg
  convert hd.sub_const (1/2) using 1
  · rfl
  · dsimp [root]
    field_simp [hr0.ne']
    ring

theorem M_hasDerivAt {q α b : ℝ} (hqL : qLow≤q) (hb : b∈Icc 0 (1/10:ℝ)) :
    HasDerivAt (M q α) (Md q α b) b := by
  convert (((primary_hasDerivAt hqL hb).sub_const (1/2)).mul_const (Real.sin α)).add
    (((hasDerivAt_id b).sub_const (1/2)).mul_const (Real.cos α)) using 1
  · rfl
  · dsimp [Md]
    ring

theorem M_derivative_lower {q α b : ℝ} (hqL : qLow≤q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    (87/100:ℝ)<Md q α b := by
  have hr := root_ratio hqL hb
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hsu : Real.sin α≤27/100 := (Real.sin_le hα.1).trans hα.2
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := α)
  have hprod := mul_le_mul_of_nonneg_right hr.2.le hs
  dsimp [Md]
  norm_num at hsq
  nlinarith

theorem M_growth {q α b c : ℝ} (hqL : qLow≤q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ))
    (hc : c∈Icc 0 (1/10:ℝ)) (hbc : b≤c) :
    (87/100)*(c-b)≤M q α c-M q α b := by
  exact derivative_reserve
    (fun z hz => (M_hasDerivAt hqL hz).continuousAt.continuousWithinAt)
    (fun z hz => M_hasDerivAt hqL (Ioo_subset_Icc_self hz))
    (fun z hz => (M_derivative_lower hqL hα (Ioo_subset_Icc_self hz)).le) hb hc hbc

def angularUpper (α : ℝ) : ℝ := (183/200)*Real.cos α+(1/2)*Real.sin α
def angularUpperD (α : ℝ) : ℝ := -(183/200)*Real.sin α+(1/2)*Real.cos α

theorem angularUpper_hasDerivAt (α : ℝ) :
    HasDerivAt angularUpper (angularUpperD α) α := by
  have h := ((Real.hasDerivAt_cos α).const_mul (183/200)).fun_add
    ((Real.hasDerivAt_sin α).const_mul (1/2))
  refine HasDerivAt.congr_deriv (show HasDerivAt angularUpper _ α from h) ?_
  simp only [angularUpperD]
  ring

theorem angularUpperD_positive {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0<angularUpperD α := by
  have hs := (Real.sin_le hα.1).trans hα.2
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := α)
  dsimp [angularUpperD]
  norm_num at hsq
  nlinarith

theorem angularUpper_bound {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    angularUpper α<127/125 := by
  have hh := derivative_reserve
    (f := angularUpper) (df := angularUpperD)
    (l := (0:ℝ)) (u := 27/100) (x := α) (y := 27/100) (k := 0)
    (fun z _ => (angularUpper_hasDerivAt z).continuousAt.continuousWithinAt)
    (fun z _ => angularUpper_hasDerivAt z)
    (fun z hz => (angularUpperD_positive (Ioo_subset_Icc_self hz)).le)
    hα (by norm_num) hα.2
  have hc := cos_upper_four (show (0:ℝ)≤27/100 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤27/100 by norm_num)
  have hend : angularUpper (27/100)<127/125 := by
    dsimp [angularUpper]
    norm_num at hc hs
    linarith
  linarith

theorem M_lower {q α b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    -(1/2:ℝ)≤M q α b := by
  have ha := (primary_bounds hqL hqU hb).1
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hc : 0≤Real.cos α := by
    have hsq := pow_le_pow_left₀ hα.1 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hfirst := mul_nonneg (show 0≤primary q b-1/2 by linarith) hs
  have hsecond := mul_le_mul_of_nonneg_right (show -(1/2:ℝ)≤b-1/2 by linarith [hb.1]) hc
  have hcos := Real.cos_le_one α
  dsimp [M]
  linarith

theorem N_upper {q α b : ℝ} (hqL : qLow≤q) (hqU : q≤qCap)
    (hα : α∈Icc 0 (27/100:ℝ)) (hb : b∈Icc 0 (1/10:ℝ)) :
    N q α b<127/125 := by
  have ha := (primary_bounds hqL hqU hb).2
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hc : 0≤Real.cos α := by
    have hsq := pow_le_pow_left₀ hα.1 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hfirst := mul_le_mul_of_nonneg_right (show primary q b-1/2≤183/200 by linarith) hc
  have hsecond := mul_nonneg hb.1 hs
  have hbound : N q α b≤angularUpper α := by
    dsimp [N,angularUpper]
    nlinarith
  exact hbound.trans_lt (angularUpper_bound hα)

theorem angular_identity (q α b x : ℝ) :
    M q (α+x) b=M q α b*Real.cos x+N q α b*Real.sin x := by
  simp only [M,N,Real.sin_add,Real.cos_add]
  ring

/-- The actual EH0 demand pays for the entire rotation, with an explicit
strict reserve on the original whole angle interval. -/
theorem strict_endpoint_gain {q α x b c AH BH : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hα : α∈Icc 0 (27/100:ℝ))
    (hx : x∈Ioc 0 (7/10:ℝ)) (hb : b∈Icc 0 (1/10:ℝ))
    (hc : c∈Icc 0 (1/10:ℝ)) (hbc : b≤c)
    (hA : 1/2≤AH) (hB : 603/500≤BH)
    (hcontact : AH*(1-Real.cos x)+BH*Real.sin x≤c-b) :
    (1769/200000)*Real.sin x<M q α c-M q (α+x) b := by
  have hg := M_growth hqL hα hb hc hbc
  have hm := M_lower hqL hqU hα hb
  have hn := N_upper hqL hqU hα hb
  have hs : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hc0 : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hcos := AlignedMixedE.cosine_loss ⟨hx.1.le,hx.2⟩
  have hA' := mul_le_mul_of_nonneg_right hA hc0
  have hB' := mul_le_mul_of_nonneg_right hB hs.le
  have hm' := mul_le_mul_of_nonneg_right hm hc0
  have hn' := mul_lt_mul_of_pos_right hn hs
  rw [angular_identity]
  nlinarith

theorem source_primary_le {q : ℝ} {E : SignedPoint}
    (hqL : qLow≤q) (hs : E.Sorted) (hy : E.y≤0) (hc : E.Contained q)
    (hb : -E.y∈Icc 0 (1/10:ℝ)) : E.a≤primary q (-E.y) := by
  have hr := root_bounds hqL hb
  have hh := hc
  rw [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy] at hh
  have hEa := hs.1
  dsimp [primary]
  nlinarith [hr.1,hr.2]

/-- A real endpoint of the original rotated EH0 pair.  DE3 is strict,
EH1 is exact, and the new point is on the same working q-circle. -/
theorem endpoint_state {q α x : ℝ} {H D E : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHa : 1/2<H.a) (hHu : H.a<11/10) (hHy : 353/500<H.y)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Contained q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : x∈Ioc 0 (7/10:ℝ))
    (hsum : α+x≤7/10)
    (hDE : quarterFeasible D E (α+x) 3)
    (hEH : quarterFeasible E H (-x) 0) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible H.a D.a α q P ∧ P.2.2=α ∧
      EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P ∧
      EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
  let b : ℝ := -E.y
  let c : ℝ := H.a-1
  have hb0 : 0≤b := by dsimp [b]; linarith
  have hxsin : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hcosloss : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hcontact : (H.a-1/2)*(1-Real.cos x)+(H.y+1/2)*Real.sin x≤c-b := by
    have hw := edgeWidth_negative_formula ⟨hx.1.le,hx.2⟩
    dsimp [quarterFeasible] at hEH
    rw [hw] at hEH
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hEH
    dsimp [c,b]
    linarith
  have hpositive : 0<(H.a-1/2)*(1-Real.cos x)+(H.y+1/2)*Real.sin x :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hcosloss)
      (mul_pos (by linarith) hxsin)
  have hbc : b<c := by linarith
  have hc : c∈Icc 0 (1/10:ℝ) := by dsimp [c] at *; constructor <;> linarith
  have hb : b∈Icc 0 (1/10:ℝ) := ⟨hb0,hbc.le.trans hc.2⟩
  have hHlarge : 1<H.a := by dsimp [c] at hbc; linarith
  have hgain := strict_endpoint_gain hqL hqU hα hx hb hc hbc.le
    (show 1/2≤H.a-1/2 by linarith) (show 603/500≤H.y+1/2 by linarith) hcontact
  have hlift : E.a≤primary q b := source_primary_le hqL hEs hEy hEc hb
  have hsumdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hx.1],hsum⟩
  have hsin := (transport_trig hsumdom).2.2.1
  have hlift' := mul_le_mul_of_nonneg_right hlift hsin
  have hsource : 0≤D.a-1/2+M q (α+x) b := by
    have h : edgeWidth (α+x)≤D.a+E.a*Real.sin (α+x)-E.y*Real.cos (α+x) := hDE
    rw [edgeWidth_positive_formula hsumdom] at h
    dsimp only [M,b]
    linarith
  have htarget : 0<D.a-1/2+M q α c := by
    have hg0 : 0<(1769/200000:ℝ)*Real.sin x := mul_pos (by norm_num) hxsin
    linarith
  let P : EInteriorGeometry.State := (primary q c,c,α)
  have hprim := primary_bounds hqL hqU hc
  have hcircle : EInteriorGeometry.corner P=q := by
    have hr := (root_bounds hqL hc).2
    dsimp [P,EInteriorGeometry.corner,primary]
    linear_combination hr
  have hDEstrict : EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P := by
    dsimp [EInteriorGeometry.W,EInteriorGeometry.deValue,P,M] at *
    linarith
  have hEHexact : EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
    simp [P,EInteriorGeometry.W,EInteriorGeometry.ehValue,c]
  refine ⟨P,?_,rfl,hDEstrict,hEHexact⟩
  exact {
    b_nonneg := hc.1
    sorted := by change c≤primary q c; linarith [hc.2,hprim.1]
    angle := ⟨hα.1,le_rfl⟩
    circle := hcircle.le
    DE := hDEstrict.le
    EH := hEHexact.le }

end SquaresInCircles.Eight.NonpositiveEH0Transport
