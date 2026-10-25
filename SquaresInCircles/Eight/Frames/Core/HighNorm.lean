module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Curvature
public import SquaresInCircles.Eight.Frames.High.Arc

/-!
# Eight squares: the actual norm majorant for the core/high primary support

The quadratic majorant follows from the exact radical derivatives on the
whole sine range.  Its tangent is taken at sine one; both endpoint norm
comparisons and the uniform curvature bound are exact squared inequalities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighNorm
open FramePair FrameCircleArc FrameHighArc FrameCurvature
open FrameMidArc (g)

def energy (s : ℝ) : ℝ := (g-u*s)^2+(v*s)^2
def n (s : ℝ) : ℝ := Real.sqrt (energy s)
def nd (s : ℝ) : ℝ := ((u^2+v^2)*s-g*u)/n s
def ndd (s : ℝ) : ℝ := g^2*v^2/(n s)^3
def upper (s : ℝ) : ℝ := 602451/500000-(457/500)*s+(7/20)*s^2

theorem energy_one_pos : 0<energy 1 := by norm_num [energy,g,u,v]
theorem n_one_bounds : (640901/1000000:ℝ)<n 1 ∧ n 1<320451/500000 := by
  have hs : (n 1)^2=energy 1 := Real.sq_sqrt energy_one_pos.le
  have hp : 0≤n 1 := Real.sqrt_nonneg _
  norm_num [energy,g,u,v] at hs
  constructor <;> by_contra! hbad <;> nlinarith

theorem energy_minimum {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : energy 1≤energy s := by
  have hcoef : 0≤2*g*u-(u^2+v^2)*(1+s) := by
    dsimp [g,u,v]
    linarith [hs.2]
  have hp := mul_nonneg (sub_nonneg.mpr hs.2) hcoef
  dsimp [energy]
  nlinarith

theorem n_positive {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : 0<n s :=
  Real.sqrt_pos.mpr (energy_one_pos.trans_le (energy_minimum hs))

theorem n_sq {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : (n s)^2=energy s :=
  Real.sq_sqrt (energy_one_pos.le.trans (energy_minimum hs))

theorem n_lower {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : n 1≤n s := by
  have he := energy_minimum hs
  have he0 := n_sq (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have he1 := n_sq hs
  have hp := n_positive hs
  have hp0 := n_one_bounds.1
  nlinarith

theorem n_deriv {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : HasDerivAt n (nd s) s := by
  have hE : HasDerivAt energy (2*(g-u*s)*(-u)+2*(v*s)*v) s := by
    have h := ((((hasDerivAt_id' s).const_mul u).const_sub g).fun_pow 2).fun_add
      (((hasDerivAt_id' s).const_mul v).fun_pow 2)
    show HasDerivAt (fun y => (g-u*y)^2+(v*y)^2) _ s
    convert h using 1
    norm_num
  have he := hE.sqrt (energy_one_pos.trans_le (energy_minimum hs)).ne'
  show HasDerivAt (fun y => Real.sqrt (energy y)) _ s
  convert he using 1
  have hn := (n_positive hs).ne'
  dsimp [nd] at hn ⊢
  rw [show n s = Real.sqrt (energy s) from rfl] at hn ⊢
  field_simp
  ring

theorem nd_deriv {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : HasDerivAt nd (ndd s) s := by
  have hn := (n_positive hs).ne'
  have hd := ((((hasDerivAt_id s).const_mul (u^2+v^2)).sub_const (g*u))).div
    (n_deriv hs) hn
  convert hd using 1
  · rfl
  · dsimp [nd,ndd]
    field_simp [hn]
    have he := n_sq hs
    dsimp [energy] at he
    nlinarith

theorem curvature_bound {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : ndd s<(7/10:ℝ) := by
  have hn : (640901/1000000:ℝ)<n s := n_one_bounds.1.trans_le (n_lower hs)
  have hpow := pow_le_pow_left₀ (show (0:ℝ)≤640901/1000000 by norm_num) hn.le 3
  dsimp [ndd]
  apply (div_lt_iff₀ (pow_pos (n_positive hs) 3)).2
  norm_num [g,v] at *
  nlinarith

theorem endpoint_slope : -(107/500:ℝ)<nd 1 := by
  have hp : 0<n 1 := by linarith [n_one_bounds.1]
  dsimp [nd]
  apply (lt_div_iff₀ hp).2
  norm_num [u,v,g]
  nlinarith [n_one_bounds.1]

theorem n_upper {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : n s<upper s := by
  have hh := upper_tangent (M := (7/10:ℝ)) hs
    (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
    (fun z hz => n_deriv hz) (fun z hz => nd_deriv hz)
    (fun z hz => (curvature_bound hz).le)
  have hd := mul_le_mul_of_nonpos_right endpoint_slope.le (sub_nonpos.mpr hs.2)
  dsimp [upper]
  nlinarith [n_one_bounds.2]

theorem norm_rescale {s : ℝ} (hs : 0<s) :
    Real.sqrt ((g/s-u)^2+v^2)*s=n s := by
  have he : (((g/s-u)^2+v^2)*s^2)=energy s := by
    dsimp [energy]
    field_simp
  rw [n, ← he, Real.sqrt_mul' _ (sq_nonneg s), Real.sqrt_sq hs.le]

end SquaresInCircles.Eight.FrameCoreHighNorm
