module

public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.Mid.HighTargetReferences
public import SquaresInCircles.Eight.Frames.Mid.HighVaryingCalculus
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: complete high/high varying support by one quadratic reserve

The full second-derivative lower bound and the
actual value and slope at `4/5` imply the strict bound on `[3/5,19/20]`.
-/

section
/-!
## The varying high/high support and its exact fourth derivative

An affine reparameterization reuses the already differentiated plane
norm.  The support itself retains the actual high-arc cut endpoint.
The fourth derivative is negative throughout `[.6,.95]`, so its second
derivative is concave on that whole interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighVaryingCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def domain : Set ℝ := Icc (3/5:ℝ) (19/20)
def lam (x : ℝ) : ℝ := 367/500-(2/5)*x
def gain : ℝ := 80/73
def tau (x : ℝ) : ℝ := gain*x-94/365
def X : ℝ := 1+a1-b1
def Y : ℝ := 1-a1-b1
def N (x : ℝ) : ℝ := FrameMidHighVaryingCalculus.N false (tau x)
def N1 (x : ℝ) : ℝ := gain*FrameMidHighVaryingCalculus.N1 false (tau x)
def N2 (x : ℝ) : ℝ := gain^2*FrameMidHighVaryingCalculus.N2 false (tau x)
def N3 (x : ℝ) : ℝ := gain^3*FrameMidHighVaryingCalculus.N3 false (tau x)
def N4 (x : ℝ) : ℝ := gain^4*FrameMidHighVaryingCalculus.N4 false (tau x)
def Delta : ℝ := (4/25)*(u+v)^2
def T (x : ℝ) : ℝ := (2/5)*(v-u-2*lam x)

def F (x : ℝ) : ℝ :=
  x+9/100+2*lam x+u*(1+a1)+v*b1+
    (lam x*X-9/100)*Real.cos x+(lam x*Y-9/100)*Real.sin x-R*N x
def Fd (x : ℝ) : ℝ :=
  1/5+(lam x*Y-9/100-(2/5)*X)*Real.cos x+
    (-lam x*X+9/100-(2/5)*Y)*Real.sin x-R*N1 x
def Fdd (x : ℝ) : ℝ :=
  (-lam x*X+9/100-(4/5)*Y)*Real.cos x+
    (-lam x*Y+9/100+(4/5)*X)*Real.sin x-R*N2 x
def Fddd (x : ℝ) : ℝ :=
  (-lam x*Y+9/100+(6/5)*X)*Real.cos x+
    (lam x*X-9/100+(6/5)*Y)*Real.sin x-R*N3 x
def Fdddd (x : ℝ) : ℝ :=
  (lam x*X-9/100+(8/5)*Y)*Real.cos x+
    (lam x*Y-9/100-(8/5)*X)*Real.sin x-R*N4 x

theorem lam_reparameterization (x : ℝ) :
    FrameMidHighVaryingCalculus.lam false (tau x)=lam x := by
  dsimp [FrameMidHighVaryingCalculus.lam,FrameMidHighVaryingCalculus.origin,
    FrameMidHighVaryingCalculus.m,tau,gain,lam]
  ring

theorem lam_deriv (x : ℝ) : HasDerivAt lam (-(2/5:ℝ)) x := by
  have h := (hasDerivAt_const x (367/500:ℝ)).fun_sub ((hasDerivAt_id x).const_mul (2/5:ℝ))
  convert h using 1
  · funext y
    simp only [lam,id]
  · ring

theorem tau_deriv (x : ℝ) : HasDerivAt tau gain x := by
  have h := ((hasDerivAt_id x).const_mul gain).sub_const (94/365:ℝ)
  convert h using 1
  · funext y
    simp only [tau,id]
  · ring


theorem N_pos (x : ℝ) : 0<N x := FrameMidHighVaryingCalculus.N_pos false (tau x)

theorem N_sq (x : ℝ) : (N x)^2=(u+lam x)^2+(v-lam x)^2 := by
  have hh := FrameMidHighVaryingCalculus.N_sq false (tau x)
  rw [lam_reparameterization] at hh
  have hs : sign false= -1 := by simp [sign]
  rw [N,hh,hs]
  ring


theorem N_literal (x : ℝ) : N x=Real.sqrt ((u+lam x)^2+(v-lam x)^2) := by
  rw [← N_sq,Real.sqrt_sq (N_pos x).le]

theorem N1_formula (x : ℝ) : N1 x=T x/N x := by
  dsimp [N1,FrameMidHighVaryingCalculus.N1,FrameMidHighVaryingCalculus.T]
  rw [lam_reparameterization]
  dsimp [FrameMidHighVaryingCalculus.m,sign,T,gain,N]
  ring

theorem N2_formula (x : ℝ) : N2 x=Delta/(N x)^3 := by
  dsimp [N2,FrameMidHighVaryingCalculus.N2,FrameMidHighVaryingCalculus.Delta,
    FrameMidHighVaryingCalculus.m,sign,Delta,gain,N]
  ring

theorem N4_formula (x : ℝ) : N4 x=3*Delta*(4*(T x)^2-Delta)/(N x)^7 := by
  dsimp [N4,FrameMidHighVaryingCalculus.N4,FrameMidHighVaryingCalculus.T]
  rw [lam_reparameterization]
  dsimp [FrameMidHighVaryingCalculus.Delta,FrameMidHighVaryingCalculus.m,
    sign,T,Delta,gain,N]
  ring

theorem N_deriv (x : ℝ) : HasDerivAt N (N1 x) x := by
  have h := (FrameMidHighVaryingCalculus.N_deriv false (tau x)).comp x (tau_deriv x)
  rw [show N=FrameMidHighVaryingCalculus.N false ∘ tau from rfl]
  exact h.congr_deriv (by rw [N1]; ring)

theorem N1_deriv (x : ℝ) : HasDerivAt N1 (N2 x) x := by
  have h := ((FrameMidHighVaryingCalculus.N1_deriv false (tau x)).comp x
    (tau_deriv x)).const_mul gain
  rw [show N1=fun y => gain*(FrameMidHighVaryingCalculus.N1 false ∘ tau) y from rfl]
  exact h.congr_deriv (by rw [N2]; ring)

theorem N2_deriv (x : ℝ) : HasDerivAt N2 (N3 x) x := by
  have h := ((FrameMidHighVaryingCalculus.N2_deriv false (tau x)).comp x
    (tau_deriv x)).const_mul (gain^2)
  rw [show N2=fun y => gain^2*(FrameMidHighVaryingCalculus.N2 false ∘ tau) y from rfl]
  exact h.congr_deriv (by rw [N3]; ring)

theorem N3_deriv (x : ℝ) : HasDerivAt N3 (N4 x) x := by
  have h := ((FrameMidHighVaryingCalculus.N3_deriv false (tau x)).comp x
    (tau_deriv x)).const_mul (gain^3)
  rw [show N3=fun y => gain^3*(FrameMidHighVaryingCalculus.N3 false ∘ tau) y from rfl]
  exact h.congr_deriv (by rw [N4]; ring)


theorem multiplier_bounds {x : ℝ} (hx : x∈domain) :
    (177/500:ℝ)≤lam x ∧ lam x≤247/500 := by
  dsimp [domain,lam] at *
  constructor <;> linarith [hx.1,hx.2]

theorem coordinate_bounds : 0<X ∧ X<(507/250:ℝ) ∧ Y< -(699/500:ℝ) := by
  rw [X,Y,b1_eq]
  refine ⟨?_,?_,?_⟩ <;> linarith [a1_precise.1,a1_precise.2]


theorem fourth_norm_positive {x : ℝ} (hx : x∈domain) : 0<N4 x := by
  have hl := multiplier_bounds hx
  have hcomp : 0<4*lam x+u-3*v := by dsimp [u,v]; linarith [hl.1]
  have hbase : 0<2*lam x+u-v := by dsimp [u,v]; linarith [hl.1]
  have hgap : 0<u+v := by norm_num [u,v]
  have hs : (u+v)^2<4*(2*lam x+u-v)^2 := by nlinarith
  have hdelta : 0<Delta := by norm_num [Delta,u,v]
  have hnum : 0<4*(T x)^2-Delta := by dsimp [T,Delta]; nlinarith
  rw [N4_formula]
  exact div_pos (mul_pos (mul_pos (by norm_num) hdelta) hnum) (pow_pos (N_pos x) 7)

theorem F_deriv (x : ℝ) : HasDerivAt F (Fd x) x := by
  have hb := (((hasDerivAt_id x).add_const (9/100:ℝ)).fun_add
    ((lam_deriv x).const_mul 2)).add_const (u*(1+a1)+v*b1)
  have hc := (((lam_deriv x).mul_const X).sub_const (9/100:ℝ)).fun_mul (Real.hasDerivAt_cos x)
  have hs := (((lam_deriv x).mul_const Y).sub_const (9/100:ℝ)).fun_mul (Real.hasDerivAt_sin x)
  have h := ((hb.fun_add hc).fun_add hs).fun_sub ((N_deriv x).const_mul R)
  convert h using 1
  · funext y
    simp only [F,id]
    ring
  · simp only [Fd]
    ring


theorem Fd_deriv (x : ℝ) : HasDerivAt Fd (Fdd x) x := by
  have hc := ((((lam_deriv x).mul_const Y).sub_const (9/100:ℝ)).sub_const ((2/5)*X)).fun_mul
    (Real.hasDerivAt_cos x)
  have hs := (((((lam_deriv x).mul_const X).neg).add_const (9/100:ℝ)).sub_const
    ((2/5)*Y)).fun_mul (Real.hasDerivAt_sin x)
  have h := (((hasDerivAt_const x (1/5:ℝ)).fun_add hc).fun_add hs).fun_sub
    ((N1_deriv x).const_mul R)
  convert h using 1
  · funext y
    simp only [Fd,Pi.neg_apply]
    ring
  · simp only [Fdd,Pi.neg_apply]
    ring


theorem Fdd_deriv (x : ℝ) : HasDerivAt Fdd (Fddd x) x := by
  have hc := (((((lam_deriv x).mul_const X).neg).add_const (9/100:ℝ)).sub_const
    ((4/5)*Y)).fun_mul (Real.hasDerivAt_cos x)
  have hs := (((((lam_deriv x).mul_const Y).neg).add_const (9/100:ℝ)).add_const
    ((4/5)*X)).fun_mul (Real.hasDerivAt_sin x)
  have h := (hc.fun_add hs).fun_sub ((N2_deriv x).const_mul R)
  convert h using 1
  · funext y
    simp only [Fdd,Pi.neg_apply]
    ring
  · simp only [Fddd,Pi.neg_apply]
    ring


theorem Fddd_deriv (x : ℝ) : HasDerivAt Fddd (Fdddd x) x := by
  have hc := (((((lam_deriv x).mul_const Y).neg).add_const (9/100:ℝ)).add_const
    ((6/5)*X)).fun_mul (Real.hasDerivAt_cos x)
  have hs := ((((lam_deriv x).mul_const X).sub_const (9/100:ℝ)).add_const
    ((6/5)*Y)).fun_mul (Real.hasDerivAt_sin x)
  have h := (hc.fun_add hs).fun_sub ((N3_deriv x).const_mul R)
  convert h using 1
  · funext y
    simp only [Fddd,Pi.neg_apply]
    ring
  · simp only [Fdddd,Pi.neg_apply]
    ring


theorem fourth_negative {x : ℝ} (hx : x∈domain) : Fdddd x<0 := by
  have hl := multiplier_bounds hx
  have hcoord := coordinate_bounds
  have hxy := mul_le_mul hl.2 hcoord.2.1.le hcoord.1.le (by norm_num : (0:ℝ)≤247/500)
  have hc : lam x*X-9/100+(8/5)*Y<0 := by nlinarith [hcoord.2.2]
  have hly := mul_nonpos_of_nonneg_of_nonpos (show 0≤lam x by linarith [hl.1])
    (show Y≤0 by linarith [hcoord.2.2])
  have hs : lam x*Y-9/100-(8/5)*X<0 := by linarith
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hcos := mul_nonpos_of_nonpos_of_nonneg hc.le ht.2.2.1
  have hsin := mul_nonpos_of_nonpos_of_nonneg hs.le ht.1
  have hn := mul_pos R_pos (fourth_norm_positive hx)
  dsimp [Fdddd]
  linarith

theorem second_concave : ConcaveOn ℝ domain Fdd :=
  concave_of_deriv2 (fun x _ => Fdd_deriv x) (fun x _ => Fddd_deriv x)
    (fun _ hx => (fourth_negative hx).le)

end SquaresInCircles.Eight.FrameHighHighVaryingCalculus
end
end
end

section
/-!
## Closed-arc support selection for all high/high signs

The small negative-target multiplier has no interior minimum: if both
coefficients were negative, the exact trigonometric circle would violate
the coefficient norm.  The varying family keeps its multiplier and angle
correlated throughout the full interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighSupports
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalSelection FrameDiagonalTrigonometry

theorem positive_target_endpoints {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (7/20:ℝ) (6/5)) :
    min (target false true (39/100) x 0) (target false true (39/100) x b1)≤
      target false true (39/100) x B := by
  apply target_endpoints_of_one_coefficient hB
  right
  have hs := sum_early hx
  norm_num [targetV,transverse,sign,v]
  linarith

theorem middle_negative_target {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (3/5:ℝ) (4/5)) :
    target false false (43/100) x b1≤target false false (43/100) x B := by
  have hD := difference_080_upper ⟨by linarith [hx.1],hx.2⟩
  have hC := sum_middle ⟨hx.1,by linarith [hx.2]⟩
  apply target_last_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem small_negative_coefficients (x : ℝ) :
    0≤targetU false false (17/50) x ∨ 0≤targetV false false (17/50) x := by
  by_contra h
  push Not at h
  have hU : u<(17/50)*(Real.sin x-Real.cos x) := by
    norm_num [targetU,primary,sign] at h
    linarith [h.1]
  have hV : v<(17/50)*(Real.sin x+Real.cos x) := by
    norm_num [targetV,transverse,sign] at h
    linarith [h.2]
  have hpU := mul_pos (sub_pos.mpr hU)
    (show 0<(17/50)*(Real.sin x-Real.cos x)+u by
      have hu : 0<u := by norm_num [u]
      linarith)
  have hpV := mul_pos (sub_pos.mpr hV)
    (show 0<(17/50)*(Real.sin x+Real.cos x)+v by
      have hv : 0<v := by norm_num [v]
      linarith)
  have hid : ((17/50:ℝ)*(Real.sin x-Real.cos x))^2+
      ((17/50:ℝ)*(Real.sin x+Real.cos x))^2=2*(17/50:ℝ)^2 := by
    linear_combination (289/1250:ℝ)*(Real.sin_sq_add_cos_sq x)
  norm_num [u,v] at hpU hpV
  nlinarith

theorem small_negative_target_endpoints {B x : ℝ} (hB : B∈arc false) :
    min (target false false (17/50) x 0) (target false false (17/50) x b1)≤
      target false false (17/50) x B :=
  target_endpoints_of_one_coefficient hB (small_negative_coefficients x)

theorem varying_negative_target {B x : ℝ} (hB : B∈arc false)
    (hx : x∈FrameHighHighVaryingCalculus.domain) :
    target false false (FrameHighHighVaryingCalculus.lam x) x b1≤
      target false false (FrameHighHighVaryingCalculus.lam x) x B := by
  let l := FrameHighHighVaryingCalculus.lam x
  have hl : (177/500:ℝ)≤l ∧ l≤247/500 :=
    FrameHighHighVaryingCalculus.multiplier_bounds hx
  have hD := difference_095_upper ⟨by linarith [hx.1],hx.2⟩
  have hC := sum_middle hx
  have hld := mul_le_mul_of_nonneg_left hD.le (show 0≤l by linarith [hl.1])
  have hlc := mul_le_mul (show (177/500:ℝ)≤l from hl.1) hC.le
    (by norm_num : (0:ℝ)≤69/50) (by linarith [hl.1] : 0≤l)
  have hUbound : -targetU false false l x<(127/5000:ℝ) := by
    norm_num [targetU,primary,sign,u]
    nlinarith [hl.2]
  apply target_last_of_derivative hB
  intro z hz
  have hr := slope_high_bounds hz
  by_cases hU : 0≤targetU false false l x
  · have hp := mul_nonneg hU hr.1
    norm_num [targetV,transverse,sign,v]
    linarith
  · have hp := mul_le_mul_of_nonneg_left hr.2.le
      (neg_nonneg.mpr (lt_of_not_ge hU).le)
    norm_num [targetV,transverse,sign,v]
    nlinarith

theorem opposite_source_cut {b : ℝ} (hb : b∈arc false) :
    source false false (73/200) b1≤ source false false (73/200) b := by
  apply source_last_of_derivative hb
  intro z hz
  have hr := slope_high_bounds hz
  norm_num [sourceU,sourceV,primary,transverse,sign,u,v]
  linarith [hr.2]

end SquaresInCircles.Eight.FrameHighHighSupports
end
end
end

section
/-!
## Two curvature endpoints and one tangent for the high/high support

The three norm cages follow by squaring positive rationals against the
literal quadratic norm.  The actual high endpoint and radius are enclosed
by their defining circle.  The comparisons below are fixed references for
the whole-interval derivative argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighVaryingReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameHighHighVaryingCalculus
open StationaryPrimitives (Interval)
open FrameMidHighTargetReferences (aBox bBox)
open FrameMidHighVaryingReferences (rBox sinBox cosBox)

def xBox : Interval X := ((Interval.point 1).add aBox).sub bBox
def yBox : Interval Y := ((Interval.point 1).sub aBox).sub bBox

structure SupportIntervals (x : ℝ) where
  value : Interval (F x)
  first : Interval (Fd x)
  second : Interval (Fdd x)

def supportIntervals {x : ℝ} (hx : 0≤x)
    (Z : Interval (N x)) (hZ : 0<Z.lo) : SupportIntervals x := by
  let l := Interval.point (lam x)
  let small := Interval.point (9/100:ℝ)
  let m := Interval.point (2/5:ℝ)
  let mm := Interval.point (4/5:ℝ)
  let s := sinBox hx
  let c := cosBox hx
  let n1 := (Interval.point (T x)).div Z hZ
  let n2 := (Interval.point Delta).div Z.cube (Interval.cube_lo_pos hZ)
  refine ⟨?_,?_,?_⟩
  · exact ((((((((Interval.point x).add small).add ((Interval.point 2).mul l)).add ((Interval.point u).mul ((Interval.point 1).add aBox))).add ((Interval.point v).mul bBox)).add (((l.mul xBox).sub small).mul c)).add (((l.mul yBox).sub small).mul s)).sub (rBox.mul Z))
  · have hh := ((((Interval.point (1/5:ℝ)).add ((((l.mul yBox).sub small).sub (m.mul xBox)).mul c)).add ((((l.mul xBox).neg.add small).sub (m.mul yBox)).mul s)).sub (rBox.mul n1))
    convert hh using 1
    simp only [Fd,N1_formula]
    ring
  · have hh := (((((l.mul xBox).neg.add small).sub (mm.mul yBox)).mul c).add ((((l.mul yBox).neg.add small).add (mm.mul xBox)).mul s)).sub (rBox.mul n2)
    convert hh using 1
    simp only [Fdd,N2_formula]
    ring

theorem norm_reference {x l h : ℝ} (hl : 0<l) (hlh : l<h)
    (hl2 : l^2<(u+lam x)^2+(v-lam x)^2)
    (hh2 : (u+lam x)^2+(v-lam x)^2<h^2) : N x∈Icc l h := by
  have hn := N_pos x
  have hs := N_sq x
  constructor <;> nlinarith

def leftNorm : Interval (N (3/5)) := Interval.of_bounds
  (norm_reference (l := (58345671/100000000:ℝ)) (h := (58345673/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))
def rightNorm : Interval (N (19/20)) := Interval.of_bounds
  (norm_reference (l := (46090109/100000000:ℝ)) (h := (46090111/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))
def tangentNorm : Interval (N (4/5)) := Interval.of_bounds
  (norm_reference (l := (10152507/20000000:ℝ)) (h := (50762537/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))

def leftReference := supportIntervals (show (0:ℝ)≤3/5 by norm_num)
  leftNorm (by norm_num [leftNorm,Interval.of_bounds])
def rightReference := supportIntervals (show (0:ℝ)≤19/20 by norm_num)
  rightNorm (by norm_num [rightNorm,Interval.of_bounds])
def tangentReference := supportIntervals (show (0:ℝ)≤4/5 by norm_num)
  tangentNorm (by norm_num [tangentNorm,Interval.of_bounds])

private lemma r55_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r55_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl

private lemma r55_bBox_lo : bBox.lo=((Interval.point (2/5:ℝ)).mul aBox).lo :=
  r55_mpr_lo b1_eq _ _
private lemma r55_bBox_hi : bBox.hi=((Interval.point (2/5:ℝ)).mul aBox).hi :=
  r55_mpr_hi b1_eq _ _

private lemma r55_first_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).first.lo=
      ((((Interval.point (1/5:ℝ)).add (((((Interval.point (lam x)).mul yBox).sub
        (Interval.point (9/100:ℝ))).sub ((Interval.point (2/5:ℝ)).mul xBox)).mul (cosBox hx))).add
        (((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
          ((Interval.point (2/5:ℝ)).mul yBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point (T x)).div Z hZ))).lo := by
  dsimp only [supportIntervals]
  apply r55_mpr_lo
  simp only [Fd,N1_formula]
  ring
private lemma r55_first_hi {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).first.hi=
      ((((Interval.point (1/5:ℝ)).add (((((Interval.point (lam x)).mul yBox).sub
        (Interval.point (9/100:ℝ))).sub ((Interval.point (2/5:ℝ)).mul xBox)).mul (cosBox hx))).add
        (((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
          ((Interval.point (2/5:ℝ)).mul yBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point (T x)).div Z hZ))).hi := by
  dsimp only [supportIntervals]
  apply r55_mpr_hi
  simp only [Fd,N1_formula]
  ring
private lemma r55_second_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).second.lo=
      (((((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
        ((Interval.point (4/5:ℝ)).mul yBox)).mul (cosBox hx)).add
        (((((Interval.point (lam x)).mul yBox).neg.add (Interval.point (9/100:ℝ))).add
          ((Interval.point (4/5:ℝ)).mul xBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point Delta).div Z.cube (Interval.cube_lo_pos hZ)))).lo := by
  dsimp only [supportIntervals]
  apply r55_mpr_lo
  simp only [Fdd,N2_formula]
  ring

private lemma r55_value_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).value.lo=
      ((((((((Interval.point x).add (Interval.point (9/100:ℝ))).add
        ((Interval.point 2).mul (Interval.point (lam x)))).add
        ((Interval.point u).mul ((Interval.point 1).add aBox))).add ((Interval.point v).mul bBox)).add
        ((((Interval.point (lam x)).mul xBox).sub (Interval.point (9/100:ℝ))).mul (cosBox hx))).add
        ((((Interval.point (lam x)).mul yBox).sub (Interval.point (9/100:ℝ))).mul (sinBox hx))).sub
        (rBox.mul Z)).lo := rfl

local macro "hh_varying_arithmetic" : tactic => `(tactic|
  norm_num [leftReference,rightReference,tangentReference,r55_first_lo,r55_first_hi,
    r55_second_lo,r55_value_lo,leftNorm,rightNorm,tangentNorm,aBox,r55_bBox_lo,r55_bBox_hi,
    rBox,xBox,yBox,sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
    Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
    Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8])

theorem endpoint_curvatures : (1/2:ℝ)<Fdd (3/5) ∧ (1/2:ℝ)<Fdd (19/20) := by
  have hl : (1/2:ℝ)<leftReference.second.lo := by
    hh_varying_arithmetic
  have hr : (1/2:ℝ)<rightReference.second.lo := by
    hh_varying_arithmetic
  exact ⟨hl.trans_le leftReference.second.mem.1,hr.trans_le rightReference.second.mem.1⟩

theorem tangent_value : (911/1000:ℝ)<F (4/5) := by
  have hh : (911/1000:ℝ)<tangentReference.value.lo := by
    hh_varying_arithmetic
  exact hh.trans_le tangentReference.value.mem.1

theorem tangent_slope : |Fd (4/5)|<(1/250:ℝ) := by
  have hl : -(1/250:ℝ)<tangentReference.first.lo := by
    hh_varying_arithmetic
  have hr : tangentReference.first.hi<(1/250:ℝ) := by
    hh_varying_arithmetic
  exact abs_lt.mpr ⟨hl.trans_le tangentReference.first.mem.1,
    tangentReference.first.mem.2.trans_lt hr⟩

end SquaresInCircles.Eight.FrameHighHighVaryingReferences
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighVaryingScalars
open FrameHighHighVaryingCalculus FrameHighHighVaryingReferences

theorem curvature {x : ℝ} (hx : x∈domain) : (1/2:ℝ)<Fdd x :=
  concave_gt_of_endpoints second_concave hx endpoint_curvatures.1 endpoint_curvatures.2

theorem lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (19/20)) : (9099/10000:ℝ)<F x := by
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/2:ℝ)) (fun z _ => F_deriv z) (fun z _ => Fd_deriv z)
    (fun z hz => (curvature hz).le)
    (show (4/5:ℝ)∈domain by constructor <;> norm_num [domain]) hx
  have hd := abs_lt.mp tangent_slope
  have hs := mul_pos (sub_pos.mpr hd.2)
    (show 0<Fd (4/5)+1/250 by linarith [hd.1])
  nlinarith [tangent_value,sq_nonneg (x-4/5+2*Fd (4/5))]

end SquaresInCircles.Eight.FrameHighHighVaryingScalars
end
end
end
