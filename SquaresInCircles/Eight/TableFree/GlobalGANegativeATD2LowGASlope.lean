module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowABSlope

/-!
# The absolute low GA angular baseline slope

Uncompiled transcription of (53)--(54). The physical slope is increased
in its original coefficients k and l. The l derivative uses the exact
maximum of `(1+2u)/(1+u)^(3/2)`. The resulting fixed-coefficient rational
function is decreased to the prescribed sine endpoint `.248`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowGASlope
open Candidate Secondary SecantBaseline SecantCoordinate

def factor (u : ℝ) : ℝ := (1+2*u)/(Real.sqrt (1+u))^3
def factorFirst (u : ℝ) : ℝ := (1/2-u)/(Real.sqrt (1+u))^5
def norm (k l s : ℝ) : ℝ := Real.sqrt (l^2+k^2*(Real.cos s)^2)
def slope (k l s : ℝ) : ℝ :=
  (l*(13/12+Real.sin s)-R*l^2*Real.sin s/norm k l s)/(Real.cos s)^2
def slopeK (k l s : ℝ) : ℝ := R*l^2*Real.sin s*k/(norm k l s)^3
def slopeL (k l s : ℝ) : ℝ :=
  (13/12+Real.sin s-R*Real.sin s*l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3)/(Real.cos s)^2
def rational (y : ℝ) : ℝ := (13/12-(169/250)*y)/(1-y^2)
def rationalFirst (y : ℝ) : ℝ :=
  (-(169/250)+(13/6)*y-(169/250)*y^2)/(1-y^2)^2

theorem factor_hasDerivAt {u : ℝ} (hu : 0≤u) :
    HasDerivAt factor (factorFirst u) u := by
  have hp : 0<1+u := by linarith
  have hs := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have hroot := ((hasDerivAt_id u).const_add 1).sqrt hp.ne'
  have hd := (((hasDerivAt_id u).const_mul (2:ℝ)).const_add 1).div
    (hroot.pow 3) (pow_ne_zero 3 hs.ne')
  convert hd using 1
  · rfl
  · dsimp [factorFirst]
    field_simp [hs.ne']
    nlinarith

theorem factor_maximum {u : ℝ} (hu : 0≤u) : factor u≤factor (1/2) := by
  by_cases hh : u≤1/2
  · have hm : MonotoneOn factor (Icc (0:ℝ) (1/2)) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun v hv => (factor_hasDerivAt hv.1).continuousAt.continuousWithinAt)
        (fun v hv => factor_hasDerivAt hv.1.le)
      intro v hv
      exact div_nonneg (by linarith [hv.2]) (pow_nonneg (Real.sqrt_nonneg _) 5)
    exact hm ⟨hu,hh⟩ (by norm_num) hh
  · have hm : AntitoneOn factor (Icc (1/2:ℝ) u) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun v hv => (factor_hasDerivAt (by linarith [hv.1])).continuousAt.continuousWithinAt)
        (fun v hv => factor_hasDerivAt (by linarith [hv.1]))
      intro v hv
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hv.1]) (pow_nonneg (Real.sqrt_nonneg _) 5)
    exact hm ⟨le_rfl,(lt_of_not_ge hh).le⟩ ⟨(lt_of_not_ge hh).le,le_rfl⟩ (lt_of_not_ge hh).le

theorem factor_upper {u : ℝ} (hu : 0≤u) : factor u<109/100 := by
  have hp : 0<Real.sqrt (1+(1/2:ℝ)) := by positivity
  have hs : (Real.sqrt (1+(1/2:ℝ)))^2=3/2 := by
    norm_num [Real.sq_sqrt]
  have hh : factor (1/2)<(109/100:ℝ) := by
    unfold factor
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    have hc : (Real.sqrt (1+(1/2:ℝ)))^3=(3/2)*Real.sqrt (1+(1/2:ℝ)) := by
      nlinarith only [congrArg (fun v : ℝ => v*Real.sqrt (1+(1/2:ℝ))) hs]
    rw [hc]
    nlinarith
  exact (factor_maximum hu).trans_lt hh

theorem norm_positive {k l s : ℝ} (hl : 0<l) : 0<norm k l s :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (k*Real.cos s)])

theorem norm_square (k l s : ℝ) : (norm k l s)^2=l^2+k^2*(Real.cos s)^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_scale {k l s : ℝ} (hl : 0<l) :
    norm k l s=l*denominator (k/l) s := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hd := denominator_pos (k/l) s
  have hsq : (l*denominator (k/l) s)^2=(norm k l s)^2 := by
    rw [mul_pow,denominator_sq,norm_square]
    field_simp [hl.ne']
    ring
  nlinarith [mul_pos hl hd]

theorem slope_eq {k l s : ℝ} (hl : 0<l) :
    slope k l s=angleSlope l (k/l) s := by
  rw [slope,norm_scale hl]
  dsimp [angleSlope]
  field_simp [hl.ne',(denominator_pos (k/l) s).ne']
  ring

theorem norm_hasDerivAt_k {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun k => norm k l s) (k*(Real.cos s)^2/norm k l s) k := by
  have hp := norm_positive (k:=k) (s:=s) hl
  have hd := (((((hasDerivAt_id k).pow 2).mul_const ((Real.cos s)^2)).const_add (l^2))).sqrt
    (show l^2+k^2*(Real.cos s)^2≠0 by nlinarith [norm_square k l s])
  convert hd using 1
  · rfl
  · dsimp [norm]
    ring

theorem norm_hasDerivAt_l {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun l => norm k l s) (l/norm k l s) l := by
  have hp := norm_positive (k:=k) (s:=s) hl
  have hd := ((((hasDerivAt_id l).pow 2).add_const (k^2*(Real.cos s)^2))).sqrt
    (show l^2+k^2*(Real.cos s)^2≠0 by nlinarith [norm_square k l s])
  convert hd using 1
  · rfl
  · dsimp [norm]
    ring

theorem slope_hasDerivAt_k {k l s : ℝ} (hl : 0<l) (hc : Real.cos s≠0) :
    HasDerivAt (fun k => slope k l s) (slopeK k l s) k := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hd := (((hasDerivAt_const k (R*l^2*Real.sin s)).div
    (norm_hasDerivAt_k hl) hn.ne').const_sub (l*(13/12+Real.sin s))).div_const ((Real.cos s)^2)
  convert hd using 1
  · rfl
  · dsimp [slopeK]
    field_simp [hn.ne',hc]
    ring

theorem slope_hasDerivAt_l {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun l => slope k l s) (slopeL k l s) l := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hn2 := norm_square k l s
  have hd := (((hasDerivAt_id l).mul_const (13/12+Real.sin s)).sub
    (((((hasDerivAt_id l).pow 2).const_mul R).mul_const (Real.sin s)).div
      (norm_hasDerivAt_l hl) hn.ne')).div_const ((Real.cos s)^2)
  convert hd using 1
  · rfl
  · dsimp [slopeL]
    field_simp [hn.ne']
    nlinarith [congrArg (fun v : ℝ => R*l*Real.sin s*v) hn2]

theorem normalized_factor {k l s : ℝ} (hl : 0<l) :
    l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3=
      factor ((k*Real.cos s/l)^2) := by
  have hN := norm_positive (k:=k) (s:=s) hl
  have hS : 0<Real.sqrt (1+(k*Real.cos s/l)^2) := by positivity
  have hS2 := Real.sq_sqrt (by positivity : 0≤1+(k*Real.cos s/l)^2)
  have he : norm k l s=l*Real.sqrt (1+(k*Real.cos s/l)^2) := by
    have hsq : (l*Real.sqrt (1+(k*Real.cos s/l)^2))^2=(norm k l s)^2 := by
      rw [mul_pow,hS2,norm_square]
      field_simp [hl.ne']
      ring
    nlinarith [mul_pos hl hS]
  rw [he]
  dsimp [factor]
  field_simp [hl.ne',hS.ne']
  ring

theorem sine_GA {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    Real.sin s∈Icc 0 (31/125:ℝ) := by
  have hb := trig_bracket (l:=0) (u:=(1/4:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  exact ⟨(transport_trig hsf).2.2.1,by norm_num at hb; linarith [hb.2.1]⟩

theorem slopeL_positive {k l s : ℝ} (hl : 0<l) (hs : s∈Icc 0 (1/4:ℝ)) :
    0<slopeL k l s := by
  have hy := sine_GA hs
  have hf := factor_upper (sq_nonneg (k*Real.cos s/l))
  have hf0 : 0≤factor ((k*Real.cos s/l)^2) := by dsimp [factor]; positivity
  have hR := Curvature.radius_bounds.2
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hp := mul_le_mul (show R≤(99/50:ℝ) by linarith) hf.le hf0 (by norm_num : (0:ℝ)≤99/50)
  have hpy := mul_le_mul_of_nonneg_right hp hy.1
  have hy' := mul_le_mul_of_nonneg_left hy.2
    (by norm_num : (0:ℝ)≤(99/50)*(109/100)-1)
  have hnum : 0<13/12+Real.sin s-R*Real.sin s*factor ((k*Real.cos s/l)^2) := by
    nlinarith only [hpy,hy']
  have hc : 0<Real.cos s := by linarith [Explicit.GA_cut_cosine hs]
  have he : R*Real.sin s*l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3=
      R*Real.sin s*factor ((k*Real.cos s/l)^2) := by
    rw [←normalized_factor hl]
    ring
  rw [slopeL,he]
  exact div_pos hnum (sq_pos_of_pos hc)

theorem coefficient_comparison {k l s : ℝ}
    (hk : (2/3:ℝ)≤k) (hl : (1023/1000:ℝ)≤l) (hs : s∈Icc 0 (1/4:ℝ)) :
    slope (2/3) (1023/1000) s≤slope k l s := by
  have hl0 : 0<l := by linarith
  have hc : Real.cos s≠0 := ne_of_gt (by linarith [Explicit.GA_cut_cosine hs])
  have hy := sine_GA hs
  have hmK : MonotoneOn (fun k => slope k l s) (Icc (2/3:ℝ) k) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (slope_hasDerivAt_k (k:=a) hl0 hc).continuousAt.continuousWithinAt)
      (fun a _ => slope_hasDerivAt_k hl0 hc)
    intro a ha
    dsimp [slopeK]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (sq_nonneg l)) hy.1)
        (by linarith [ha.1])) (pow_nonneg (norm_positive (k:=a) (s:=s) hl0).le 3)
  have hmL : MonotoneOn (fun l => slope (2/3) l s) (Icc (1023/1000:ℝ) l) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun b hb => (slope_hasDerivAt_l (k:=(2/3:ℝ)) (s:=s) (by linarith [hb.1])).continuousAt.continuousWithinAt)
      (fun b hb => slope_hasDerivAt_l (k:=(2/3:ℝ)) (s:=s) (by linarith [hb.1]))
    intro b hb
    exact (slopeL_positive (k:=(2/3:ℝ)) (by linarith [hb.1]) hs).le
  exact (hmL ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl).trans
    (hmK ⟨le_rfl,hk⟩ ⟨hk,le_rfl⟩ hk)

theorem rational_hasDerivAt {y : ℝ} (hy : y∈Icc 0 (31/125:ℝ)) :
    HasDerivAt rational (rationalFirst y) y := by
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hn : 1-y^2≠0 := by nlinarith
  have hd := (((hasDerivAt_id y).const_mul (169/250:ℝ)).const_sub (13/12:ℝ)).div
    (((hasDerivAt_id y).pow 2).const_sub 1) hn
  convert hd using 1
  · rfl
  · dsimp [rationalFirst]
    field_simp [hn]
    ring

theorem rational_antitone : AntitoneOn rational (Icc (0:ℝ) (31/125)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y hy => (rational_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun y hy => rational_hasDerivAt (Ioo_subset_Icc_self hy))
  intro y hy
  exact div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [hy.2,sq_nonneg y]) (sq_nonneg _)

theorem fixed_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    (249/250:ℝ)<slope (2/3) (1023/1000) s := by
  have hy := sine_GA hs
  have hc : 0<Real.cos s := by linarith [Explicit.GA_cut_cosine hs]
  have hcoef := coefficient_upper (r₀:=((2/3:ℝ)/(1023/1000))) (c₀:=(121/125:ℝ)) (D:=(419/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (show (121/125:ℝ)≤Real.cos s by linarith [Explicit.GA_cut_cosine hs])
    (by norm_num [qCap])
  have hp := mul_le_mul_of_nonneg_right hcoef.le hy.1
  have hcos2 : (Real.cos s)^2=1-(Real.sin s)^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  have hrational := rational_antitone hy (show (31/125:ℝ)∈Icc 0 (31/125:ℝ) by norm_num) hy.2
  have hrlower := mul_le_mul_of_nonneg_left hrational (by norm_num : (0:ℝ)≤1023/1000)
  have hendpoint : (249/250:ℝ)<(1023/1000)*rational (31/125) := by norm_num [rational]
  have hbound : (1023/1000)*rational (Real.sin s)≤angleSlope (1023/1000) ((2/3)/(1023/1000)) s := by
    dsimp [rational,angleSlope]
    rw [←hcos2,←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hc)).2
    nlinarith only [hp]
  rw [slope_eq (by norm_num : (0:ℝ)<1023/1000)]
  exact (hendpoint.trans_le hrlower).trans_le hbound

theorem original {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    (249/250:ℝ)<angleSlope (Explicit.l .low z) (Explicit.k .low z/Explicit.l .low z) s := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hh := (fixed_lower hs).trans_le (coefficient_comparison hklo.le hllo.le hs)
  rwa [slope_eq (by linarith : 0<Explicit.l .low z)] at hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowGASlope
