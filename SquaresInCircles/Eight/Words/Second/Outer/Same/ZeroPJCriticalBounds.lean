module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKReference
public import SquaresInCircles.Eight.Words.Second.Outer.SourceReference

/-!
# Eight squares: the complete P/J critical-coordinate and mixed-curvature bounds

E>0 makes U increase.  The full radial interval
then controls the derivative of V/U, and integration gives the single
lower bound (V/U)(P')^3>.2725 on the whole critical curve.
-/

section
/-!
## The original P/J stationary curve

Angular stationarity determines the target
circle coordinate from the original source coordinate.  The definitions
below retain that exact circle relation; no critical point is selected
or assumed to exist.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def p (t : ℝ) : ℝ := PLabel.d1 t
def E (t : ℝ) : ℝ := PLabel.d2 t-(t-1/2)*(p t)^3
def ED (t : ℝ) : ℝ :=
  PLabel.d3 t-(p t)^3-3*(t-1/2)*(p t)^2*PLabel.d2 t
def criticalU (t : ℝ) : ℝ := (Q0+1-(t-1/2)^2-1/(p t)^2)/2
def criticalV (t : ℝ) : ℝ := Real.sqrt (Q0-(criticalU t)^2)
def criticalRatio (t : ℝ) : ℝ := criticalV t/criticalU t
def criticalRatioD (t : ℝ) : ℝ :=
  -Q0*E t/((criticalU t)^2*criticalV t*(p t)^3)
def sourceInterval : Set ℝ := Icc (3/5) outerDiagonal

lemma source_domain {t : ℝ} (ht : t∈sourceInterval) : t∈Icc 0 outerDiagonal :=
  ⟨by linarith [ht.1],ht.2⟩

lemma p_positive {t : ℝ} (ht : t∈Icc 0 outerDiagonal) : 0<p t := by
  dsimp [p]
  linarith [(P_first_bounds ht).1]

lemma p_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt p (PLabel.d2 t) t := PLabel.d1_hasDerivAt (outer_domain ht)

lemma E_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt E (ED t) t :=
  ((PLabel.d2_hasDerivAt (outer_domain ht)).fun_sub
    (((hasDerivAt_id' t).sub_const (1/2)).fun_mul ((p_hasDerivAt ht).fun_pow 3))).congr_deriv
      (by dsimp only [ED]; push_cast; ring)

lemma criticalU_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
    HasDerivAt criticalU (E t/(p t)^3) t := by
  have hp := p_positive ht
  have hd := (((((hasDerivAt_id t).sub_const (1/2)).pow 2).const_sub
    (Q0+1)).sub ((hasDerivAt_const t (1:ℝ)).div ((p_hasDerivAt ht).pow 2)
      (pow_ne_zero 2 hp.ne'))).div_const 2
  convert hd using 1
  · rfl
  · dsimp [E]
    field_simp [hp.ne']
    ring

lemma criticalV_sq {t : ℝ} (hr : 0≤Q0-(criticalU t)^2) :
    (criticalV t)^2=Q0-(criticalU t)^2 := Real.sq_sqrt hr

lemma criticalRatio_hasDerivAt {t : ℝ} (ht : t∈Icc 0 outerDiagonal)
    (hu : 0<criticalU t) (hr : 0<Q0-(criticalU t)^2) :
    HasDerivAt criticalRatio (criticalRatioD t) t := by
  have hp := p_positive ht
  have hv : 0<criticalV t := Real.sqrt_pos.mpr hr
  have hV := (((criticalU_hasDerivAt ht).fun_pow 2).const_sub Q0).sqrt hr.ne'
  have hd := hV.fun_div (criticalU_hasDerivAt ht) hu.ne'
  refine hd.congr_deriv ?_
  change _=-Q0*E t/((criticalU t)^2*criticalV t*(p t)^3)
  have hs : Real.sqrt (Q0-criticalU t^2)=criticalV t := rfl
  rw [hs]
  field_simp
  linear_combination -2*(E t)*criticalV_sq hr.le

lemma stationary_coordinate {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : criticalU (b B x)=U B := by
  have hp := p_positive hd.2.2
  have hv := v_positive hd.1 hd.2.1
  have hvp : p (b B x)*v B x=1 := by
    dsimp [p,angleFirst] at *
    linarith
  have hv2 : (v B x)^2=1/(p (b B x))^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hp.ne')).2
    nlinarith [sq_nonneg (p (b B x)*v B x-1)]
  have hn := norm_identity hd.1 x
  rw [hv2] at hn
  dsimp [criticalU,NegativeTwo.Inverse.q] at *
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
/-!
## Exact endpoints for the whole P/J critical interval

Only the two physical interval endpoints and
one rational target coordinate occur here.  Their radical brackets are
proved by squares, and the literal labels retain their exact rational
coefficients.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma six_reference :
    (876298/1000000:ℝ)<p (3/5) ∧ p (3/5)<876299/1000000 ∧
      (253479/1000000:ℝ)<PLabel.d2 (3/5) ∧
      PLabel.d2 (3/5)<6337/25000 ∧ PLabel.d3 (3/5)<91/250 := by
  have hu := shifted_chart_reference (outer_domain six_mem)
    (l := (411217703899/250000000000:ℝ))
    (u := (1644870815597/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  rcases GeneralReference.label PLabel six_mem ⟨le_rfl,le_rfl⟩
    ⟨hu.1.le,hu.2.le⟩ (by norm_num) (by norm_num) with
    ⟨_,_,hpl,hpu,hdl,hdu⟩
  have hthird := SourceReference.source_third_upper six_mem
    (by norm_num : (0:ℝ)<411217703899/250000000000) hu.1.le
    (by norm_num : (0:ℝ)<91/250) (by norm_num [Q0])
  have e1 : (876298/1000000:ℝ)<GeneralReference.firstLo PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000) := by
    norm_num [GeneralReference.firstLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e2 : GeneralReference.firstHi PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000)<(876299/1000000:ℝ) := by
    norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e3 : (253479/1000000:ℝ)<GeneralReference.secondLo PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000) := by
    norm_num [GeneralReference.secondLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  have e4 : GeneralReference.secondHi PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000)<(6337/25000:ℝ) := by
    norm_num [GeneralReference.secondHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  dsimp only [p]
  exact ⟨by linarith,by linarith,by linarith,by linarith,hthird⟩

lemma diagonal_reference :
    (972646/1000000:ℝ)<p outerDiagonal ∧ p outerDiagonal<972647/1000000 ∧
      (8209/20000:ℝ)<PLabel.d2 outerDiagonal ∧ PLabel.d3 outerDiagonal<779/1000 := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hb := diagonal_fine
  have hu : U outerDiagonal∈Icc
      (139921406510940/100000000000000:ℝ) (139921406510941/100000000000000) := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
    constructor <;> linarith [hb.1,hb.2]
  rcases GeneralReference.label PLabel hd ⟨hb.1.le,hb.2.le⟩ hu
    (by norm_num) (by norm_num) with ⟨_,_,hpl,hpu,hdl,_⟩
  have hthird := SourceReference.source_third_upper hd
    (by norm_num : (0:ℝ)<139921406510940/100000000000000) hu.1
    (by norm_num : (0:ℝ)<779/1000) (by
      norm_num [Q0]
      linarith [hb.1])
  have e1 : (972646/1000000:ℝ)<GeneralReference.firstLo PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000) := by
    norm_num [GeneralReference.firstLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e2 : GeneralReference.firstHi PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000)<
        (972647/1000000:ℝ) := by
    norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e3 : (8209/20000:ℝ)<GeneralReference.secondLo PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000) := by
    norm_num [GeneralReference.secondLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  dsimp only [p]
  exact ⟨by linarith,by linarith,by linarith,hthird⟩

lemma E_endpoints : (43/1000:ℝ)<E outerDiagonal ∧ E (3/5)<187/1000 := by
  have hp := diagonal_reference
  have hp3 := pow_le_pow_left₀ (p_positive
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).le hp.2.1.le 3
  have hz : outerDiagonal-1/2<(79843/200000:ℝ) := by linarith [diagonal_fine.2]
  have hprod := mul_le_mul hz.le hp3 (pow_nonneg (p_positive
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).le 3)
    (by norm_num : (0:ℝ)≤79843/200000)
  have hs := six_reference
  have hs3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤876298/1000000) hs.1.le 3
  dsimp [E]
  constructor <;> nlinarith

lemma criticalU_endpoints :
    (1801/1000:ℝ)<criticalU (3/5) ∧ criticalU (3/5)<18017/10000 ∧
      criticalU outerDiagonal<37/20 := by
  have hs := six_reference
  have hps := p_positive six_mem
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤876298/1000000) hs.1.le 2
  have hhi := pow_le_pow_left₀ hps.le hs.2.1.le 2
  have hrlo : (1:ℝ)/(p (3/5))^2<1303/1000 := by
    apply (div_lt_iff₀ (pow_pos hps 2)).2
    linarith
  have hrhi : (6511/5000:ℝ)<1/(p (3/5))^2 := by
    apply (lt_div_iff₀ (pow_pos hps 2)).2
    linarith
  have hp := diagonal_reference
  have hpd := p_positive (show outerDiagonal∈Icc 0 outerDiagonal from
    ⟨outer_zero_mem.2,le_rfl⟩)
  have hdp := pow_le_pow_left₀ hpd.le hp.2.1.le 2
  have hrec : (1057/1000:ℝ)<1/(p outerDiagonal)^2 := by
    apply (lt_div_iff₀ (pow_pos hpd 2)).2
    linarith
  have hz : (399/1000:ℝ)<outerDiagonal-1/2 := by
    linarith [fine_outer_endpoint_bounds.2]
  have hz2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤399/1000) hz.le 2
  have hQ : Q0=9789/2500 := rfl
  dsimp only [criticalU]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma J_eight_twentyfifths_second : -(109/250:ℝ)<JLabel.d2 (8/25) := by
  have hm : (8/25:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := shifted_chart_reference (outer_domain hm)
    (l := (18008/10000:ℝ)) (u := (1801/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := JLabel.second_chart_reference (outer_domain hm)
    (l := (18008/10000:ℝ)) (u := (1801/1000:ℝ))
    (dlo := (-(109/250):ℝ)) (dhi := (0:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [JLabel,W,Q0]) (by norm_num [JLabel,W,Q0])
  exact hh.1

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
/-!
## One decreasing curvature on the entire P/J critical interval

Convexity gives one chord for P''' and a
lower tangent for P'.  Their exact differential identity then makes E
strictly decreasing throughout [.6,d].  The physical angular equation
itself excludes all smaller source coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma third_chord {t : ℝ} (ht : t∈sourceInterval) :
    PLabel.d3 t<(91/250:ℝ)+(7/5)*(t-3/5) := by
  have hc : ConcaveOn ℝ (Icc (3/5) outerDiagonal)
      (fun y => (91/250:ℝ)+(7/5)*(y-3/5)-PLabel.d3 y) := by
    apply concave_of_deriv2
      (f' := fun y => (7/5:ℝ)-PLabel.d4 y) (f'' := fun y => -PLabel.d5 y)
    · intro y hy
      exact (((((hasDerivAt_id' y).sub_const (3/5)).const_mul (7/5)).const_add
        (91/250)).fun_sub (PLabel.d3_hasDerivAt (outer_domain (source_domain hy)))).congr_deriv
          (by ring)
    · intro y hy
      exact (PLabel.d4_hasDerivAt (outer_domain (source_domain hy))).const_sub (7/5)
    · intro y hy
      exact neg_nonpos.mpr (P_fifth_positive (source_domain hy)).le
  have hh := concave_gt_of_endpoints hc ht
    (show (0:ℝ)<91/250+(7/5)*(3/5-3/5)-PLabel.d3 (3/5) by
      linarith [six_reference.2.2.2.2])
    (show (0:ℝ)<91/250+(7/5)*(outerDiagonal-3/5)-PLabel.d3 outerDiagonal by
      linarith [diagonal_reference.2.2.2,fine_outer_endpoint_bounds.2])
  linarith

lemma second_lower {t : ℝ} (ht : t∈sourceInterval) :
    (253/1000:ℝ)<PLabel.d2 t := by
  have hh := P_second_monotone six_mem (source_domain ht) ht.1
  linarith [six_reference.2.2.1]

lemma first_tangent {t : ℝ} (ht : t∈sourceInterval) :
    (219/250:ℝ)+(253/1000)*(t-3/5)<p t := by
  have hm : MonotoneOn (fun y => p y-(253/1000)*y) sourceInterval :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => ((p_hasDerivAt (source_domain hy)).sub
        ((hasDerivAt_id y).const_mul (253/1000))).continuousAt.continuousWithinAt)
      (fun y hy => (p_hasDerivAt (source_domain (Ioo_subset_Icc_self hy))).sub
        ((hasDerivAt_id y).const_mul (253/1000)))
      (fun y hy => by linarith [second_lower (Ioo_subset_Icc_self hy)])
  have hh := hm ⟨le_rfl,six_mem.2⟩ ht ht.1
  linarith [six_reference.1]

lemma E_derivative_negative {t : ℝ} (ht : t∈sourceInterval) :
    ED t< -(29/100:ℝ) := by
  let x := t-3/5
  have hx : x∈Icc (0:ℝ) (3/10) := by
    dsimp [x]
    constructor <;> linarith [ht.1,ht.2,outer_endpoint_bounds.2.2.2]
  have hp := first_tangent ht
  have hpp := second_lower ht
  have hthird := third_chord ht
  have hp0 := p_positive (source_domain ht)
  have hlinear : (219/250:ℝ)+(253/1000)*x≤p t := by simpa [x] using hp.le
  have hlinear0 : 0≤(219/250:ℝ)+(253/1000)*x := by linarith [hx.1]
  have hcube := pow_le_pow_left₀ hlinear0 hlinear 3
  have hpbase : (219/250:ℝ)≤p t := by linarith [hx.1]
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤219/250) hpbase 2
  have hproduct := mul_le_mul hsq hpp.le (by norm_num : (0:ℝ)≤253/1000)
    (sq_nonneg (p t))
  have hweight : 0≤3*(1/10+x) := by linarith [hx.1]
  have hweighted := mul_le_mul_of_nonneg_left hproduct hweight
  have hx2 := sq_nonneg x
  have hx3 := pow_nonneg hx.1 3
  have he : t-1/2=1/10+x := by dsimp [x]; ring
  dsimp [ED]
  rw [he]
  have hthird' : PLabel.d3 t<(91/250:ℝ)+(7/5)*x := by simpa [x] using hthird
  nlinarith only [hthird',hcube,hweighted,hx.2,hx2,hx3]

lemma E_antitone : AntitoneOn E sourceInterval :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (E_hasDerivAt (source_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => E_hasDerivAt (source_domain (Ioo_subset_Icc_self ht)))
    (fun t ht => by linarith [E_derivative_negative (Ioo_subset_Icc_self ht)])

theorem E_bounds {t : ℝ} (ht : t∈sourceInterval) :
    (43/1000:ℝ)<E t ∧ E t<187/1000 := by
  have hl := E_antitone ht ⟨six_mem.2,le_rfl⟩ ht.2
  have hu := E_antitone ⟨le_rfl,six_mem.2⟩ ht ht.1
  exact ⟨E_endpoints.1.trans_le hl,hu.trans_lt E_endpoints.2⟩

lemma velocity_circle {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (v B x+Real.cos x)^2+(b B x-1/2-Real.sin x)^2=Q0 := by
  have hU := UW_circle (outer_domain hB)
  have ht := Real.sin_sq_add_cos_sq x
  have he : v B x+Real.cos x=U B*Real.cos x+W B*Real.sin x := by
    dsimp [v,U,W]
    ring
  have hz : b B x-1/2-Real.sin x=W B*Real.cos x-U B*Real.sin x := by
    dsimp [b,U,W]
    ring
  rw [he,hz]
  linear_combination hU+((U B)^2+(W B)^2)*ht

lemma small_source_velocity {B x : ℝ} (hd : Domain B x) (hb : b B x≤3/5) :
    v B x<(1141/1000:ℝ) := by
  have hv := v_positive hd.1 hd.2.1
  have ht := positive_trig hd.2.1
  have hn := velocity_circle hd.1 (x := x)
  have htr := Real.sin_sq_add_cos_sq x
  have hproj := mul_le_mul_of_nonneg_right
    (show b B x-1/2≤(1/10:ℝ) by linarith) ht.2.2.1
  have hcos := mul_lt_mul_of_pos_left ht.1 hv
  by_contra! hlarge
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1141/1000) hlarge 2
  norm_num [Q0] at hn
  nlinarith [sq_nonneg (b B x-1/2),ht.2.2.2.1]

theorem stationary_source {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : (3/5:ℝ)<b B x := by
  by_contra! hsmall
  have hp := P_first_monotone hd.2.2 six_mem hsmall
  have hu : p (b B x)<876299/1000000 := hp.trans_lt six_reference.2.1
  have hv := small_source_velocity hd hsmall
  have hprod := mul_lt_mul hu hv.le (v_positive hd.1 hd.2.1)
    (by norm_num : (0:ℝ)≤876299/1000000)
  dsimp [angleFirst] at hstat
  change PLabel.d1 (b B x)*v B x<(876299/1000000)*(1141/1000) at hprod
  norm_num at hprod
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic

lemma criticalU_monotone : MonotoneOn criticalU sourceInterval :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (criticalU_hasDerivAt (source_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => criticalU_hasDerivAt (source_domain (Ioo_subset_Icc_self ht)))
    (fun t ht => div_nonneg (by linarith [(E_bounds (Ioo_subset_Icc_self ht)).1])
      (pow_nonneg (p_positive (source_domain (Ioo_subset_Icc_self ht))).le 3))

lemma criticalU_bounds {t : ℝ} (ht : t∈sourceInterval) :
    (1801/1000:ℝ)<criticalU t ∧ criticalU t<37/20 := by
  exact ⟨criticalU_endpoints.1.trans_le
      (criticalU_monotone ⟨le_rfl,six_mem.2⟩ ht ht.1),
    (criticalU_monotone ht ⟨six_mem.2,le_rfl⟩ ht.2).trans_lt
      criticalU_endpoints.2.2⟩

lemma critical_data {t : ℝ} (ht : t∈sourceInterval) :
    0<criticalU t ∧ 0<Q0-(criticalU t)^2 ∧ 0<criticalV t ∧
      (criticalU t)^2+(criticalV t)^2=Q0 ∧
      (7/10:ℝ)<criticalV t ∧ criticalV t<41/50 ∧
      (189/500:ℝ)<criticalRatio t := by
  have hu := criticalU_bounds ht
  have hu0 : 0<criticalU t := by linarith
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1801/1000) hu.1.le 2
  have hh := pow_le_pow_left₀ hu0.le hu.2.le 2
  have hrad : 0<Q0-(criticalU t)^2 := by norm_num [Q0]; linarith
  have hv : 0<criticalV t := Real.sqrt_pos.mpr hrad
  have hc := criticalV_sq hrad.le
  have hvl : (7/10:ℝ)<criticalV t := by norm_num [Q0] at hc; nlinarith
  have hvu : criticalV t<(41/50:ℝ) := by norm_num [Q0] at hc; nlinarith
  refine ⟨hu0,hrad,hv,by linarith,hvl,hvu,?_⟩
  apply (lt_div_iff₀ hu0).2
  nlinarith

lemma critical_mass_lower {t : ℝ} (ht : t∈sourceInterval) :
    (463/250:ℝ)^2*(871/1250)<(criticalU t)^2*criticalV t := by
  let f : ℝ→ℝ := fun u => u^4*(Q0-u^2)
  let df : ℝ→ℝ := fun u => 2*u^3*(2*Q0-3*u^2)
  have hd (u : ℝ) : HasDerivAt f (df u) u :=
    (((hasDerivAt_id' u).fun_pow 4).fun_mul
      (((hasDerivAt_id' u).fun_pow 2).const_sub Q0)).congr_deriv
        (by dsimp only [df]; push_cast; ring)
  have hm : AntitoneOn f (Icc (9/5:ℝ) (463/250)) :=
    antiOn_of_hasDeriv_nonpos
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => hd u)
      (fun u hu => by
        have hu0 : 0≤u := by linarith [hu.1]
        have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/5) hu.1.le 2
        have hn : 2*Q0-3*u^2≤0 := by norm_num [Q0]; linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn)
  have hu := criticalU_bounds ht
  have hdom : criticalU t∈Icc (9/5:ℝ) (463/250) :=
    ⟨by linarith,by linarith⟩
  have hmin := hm hdom (by norm_num) hdom.2
  have hreference : ((463/250:ℝ)^2*(871/1250))^2<f (463/250) := by
    norm_num [f,Q0]
  have hh := critical_data ht
  have he : ((criticalU t)^2*criticalV t)^2=f (criticalU t) := by
    dsimp only [f]
    linear_combination (criticalU t)^4*hh.2.2.2.1
  have hpos : 0<(criticalU t)^2*criticalV t :=
    mul_pos (pow_pos hh.1 2) hh.2.2.1
  exact lt_of_pow_lt_pow_left₀ 2 hpos.le (by rw [he]; linarith)

lemma criticalRatio_derivative_lower {t : ℝ} (ht : t∈sourceInterval) :
    -(23/50:ℝ)<criticalRatioD t := by
  have hd := critical_data ht
  have hp := p_positive (source_domain ht)
  have hfirst := first_tangent ht
  have hpbase : (219/250:ℝ)<p t := by linarith [ht.1]
  have hp3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤219/250) hpbase.le 3
  have hmass := critical_mass_lower ht
  have hden := mul_lt_mul hmass hp3
    (by norm_num : (0:ℝ)<(219/250)^3)
    (mul_nonneg (sq_nonneg (criticalU t)) hd.2.2.1.le)
  have he := (E_bounds ht).2
  have hpos : 0<(criticalU t)^2*criticalV t*(p t)^3 := by positivity
  dsimp [criticalRatioD]
  apply (lt_div_iff₀ hpos).2
  norm_num [Q0] at he hden ⊢
  nlinarith

lemma criticalRatio_initial : (227/500:ℝ)<criticalRatio (3/5) := by
  have ht : (3/5:ℝ)∈sourceInterval := ⟨le_rfl,six_mem.2⟩
  have hd := critical_data ht
  have hu := criticalU_endpoints.2.1
  have hu2 := pow_le_pow_left₀ hd.1.le hu.le 2
  have hprod := mul_le_mul_of_nonneg_left hu2
    (by norm_num : (0:ℝ)≤1+(227/500)^2)
  dsimp [criticalRatio]
  apply (lt_div_iff₀ hd.1).2
  have hc := hd.2.2.2.1
  norm_num [Q0] at hc
  nlinarith [hd.2.2.1]

lemma criticalRatio_tangent {t : ℝ} (ht : t∈sourceInterval) :
    (227/500:ℝ)-(23/50)*(t-3/5)<criticalRatio t := by
  have hm : MonotoneOn (fun u => criticalRatio u+(23/50)*u) sourceInterval :=
    monoOn_of_hasDeriv_nonneg
      (fun u hu => ((criticalRatio_hasDerivAt (source_domain hu)
        (critical_data hu).1 (critical_data hu).2.1).add
          ((hasDerivAt_id u).const_mul (23/50))).continuousAt.continuousWithinAt)
      (fun u hu => (criticalRatio_hasDerivAt (source_domain (Ioo_subset_Icc_self hu))
        (critical_data (Ioo_subset_Icc_self hu)).1
        (critical_data (Ioo_subset_Icc_self hu)).2.1).add
          ((hasDerivAt_id u).const_mul (23/50)))
      (fun u hu => by linarith [criticalRatio_derivative_lower (Ioo_subset_Icc_self hu)])
  have hh := hm ⟨le_rfl,six_mem.2⟩ ht ht.1
  linarith [criticalRatio_initial]

def productMinorant (x : ℝ) : ℝ :=
  (227/500-(23/50)*x)*(219/250+(253/1000)*x)^3

lemma productMinorant_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) :
    (109/400:ℝ)<productMinorant x := by
  let df : ℝ→ℝ := fun y => (219/250+(253/1000)*y)^2*
    (3*(253/1000)*(227/500)-(23/50)*(219/250)-4*(23/50)*(253/1000)*y)
  have hd (y : ℝ) : HasDerivAt productMinorant (df y) y :=
    ((((hasDerivAt_id' y).const_mul (23/50)).const_sub (227/500)).fun_mul
      ((((hasDerivAt_id' y).const_mul (253/1000)).const_add (219/250)).fun_pow 3)).congr_deriv
        (by dsimp only [df]; push_cast; ring)
  have hm : AntitoneOn productMinorant (Icc (0:ℝ) (3/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => hd y)
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (by norm_num; linarith [hy.1]))
  exact (by norm_num [productMinorant] : (109/400:ℝ)<productMinorant (3/10)).trans_le
    (hm hx (by norm_num) hx.2)

theorem critical_mixed_lower {t : ℝ} (ht : t∈sourceInterval) :
    (109/400:ℝ)<criticalRatio t*(p t)^3 := by
  let x := t-3/5
  have hx : x∈Icc (0:ℝ) (3/10) := by
    dsimp [x]
    constructor <;> linarith [ht.1,ht.2,outer_endpoint_bounds.2.2.2]
  have hr := criticalRatio_tangent ht
  have hp := first_tangent ht
  have hrl : 0≤(227/500:ℝ)-(23/50)*x := by linarith [hx.2]
  have hpl : 0≤(219/250:ℝ)+(253/1000)*x := by linarith [hx.1]
  have hp3 := pow_le_pow_left₀ hpl (show (219/250:ℝ)+(253/1000)*x≤p t by
    simpa [x] using hp.le) 3
  have hle := mul_le_mul_of_nonneg_left hp3 hrl
  have hlt := mul_lt_mul_of_pos_right
    (show (227/500:ℝ)-(23/50)*x<criticalRatio t by simpa [x] using hr)
    (pow_pos (p_positive (source_domain ht)) 3)
  have hh := productMinorant_lower hx
  dsimp [productMinorant] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end
