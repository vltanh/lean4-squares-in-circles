module

public import SquaresInCircles.Eight.TableFree.FrameMidHighVaryingCalculus

/-!
# The varying high/high support and its exact fourth derivative

An affine reparameterization reuses the already differentiated plane
norm.  The support itself retains the actual high-arc cut endpoint.
The fourth derivative is negative throughout `[.6,.95]`, so its second
derivative is concave on that whole interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighVaryingCalculus
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

theorem N3_formula (x : ℝ) : N3 x=-3*Delta*T x/(N x)^5 := by
  dsimp [N3,FrameMidHighVaryingCalculus.N3,FrameMidHighVaryingCalculus.T]
  rw [lam_reparameterization]
  dsimp [FrameMidHighVaryingCalculus.Delta,FrameMidHighVaryingCalculus.m,
    sign,T,Delta,gain,N]
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
    (fun x hx => (fourth_negative hx).le)

end SquaresInCircles.Eight.TableFree.FrameHighHighVaryingCalculus
