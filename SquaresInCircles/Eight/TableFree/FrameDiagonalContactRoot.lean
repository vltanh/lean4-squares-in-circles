module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalTransport

/-!
# Explicit moving line/circle contacts in diagonal coordinates

The positive root is written explicitly.  Its circle equation, contact
equation and tangent identity are algebraic; differentiability is derived
from the positive radicand.  Later contact paths therefore need no
existential minimizer or implicit differentiability premise.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalContactRoot
open FramePair FrameDiagonalArc

def N (l : ℝ) : ℝ := Real.sqrt (4*Q0-l^2)
def Nd (l : ℝ) : ℝ := -l/N l
def X (c d l : ℝ) : ℝ := (d*l+c*N l)/2-1
def Y (c d l : ℝ) : ℝ := (-c*l+d*N l)/2
def XD (c d l cp dp lp : ℝ) : ℝ :=
  (dp*l+d*lp+cp*N l+c*Nd l*lp)/2
def YD (c d l cp dp lp : ℝ) : ℝ :=
  (-cp*l-c*lp+dp*N l+d*Nd l*lp)/2

theorem N_pos {l : ℝ} (hl : 0<4*Q0-l^2) : 0<N l := Real.sqrt_pos.mpr hl
theorem N_sq {l : ℝ} (hl : 0≤4*Q0-l^2) : (N l)^2=4*Q0-l^2 := Real.sq_sqrt hl

theorem N_deriv {l : ℝ} (hl : 0<4*Q0-l^2) : HasDerivAt N (Nd l) l := by
  have hd := ((hasDerivAt_const l (4*Q0)).sub ((hasDerivAt_id l).pow 2)).sqrt hl.ne'
  convert hd using 1 <;> dsimp [Nd,N] <;> ring

theorem X_deriv {c d l : ℝ→ℝ} {x cp dp lp : ℝ}
    (hc : HasDerivAt c cp x) (hd : HasDerivAt d dp x) (hl : HasDerivAt l lp x)
    (hp : 0<4*Q0-(l x)^2) :
    HasDerivAt (fun t => X (c t) (d t) (l t))
      (XD (c x) (d x) (l x) cp dp lp) x := by
  have hn := (N_deriv hp).comp x hl
  convert (((hd.mul hl).add (hc.mul hn)).div_const 2).sub_const 1 using 1
  · rfl
  · dsimp [XD]
    ring

theorem Y_deriv {c d l : ℝ→ℝ} {x cp dp lp : ℝ}
    (hc : HasDerivAt c cp x) (hd : HasDerivAt d dp x) (hl : HasDerivAt l lp x)
    (hp : 0<4*Q0-(l x)^2) :
    HasDerivAt (fun t => Y (c t) (d t) (l t))
      (YD (c x) (d x) (l x) cp dp lp) x := by
  have hn := (N_deriv hp).comp x hl
  convert (((hc.neg.mul hl).add (hd.mul hn)).div_const 2) using 1
  · rfl
  · dsimp [YD]
    ring

theorem contact {c d l : ℝ} (hu : c^2+d^2=2) :
    d*(X c d l+1)-c*Y c d l=l := by
  calc
    d*(X c d l+1)-c*Y c d l=(c^2+d^2)*l/2 := by dsimp [X,Y]; ring
    _=l := by rw [hu]; ring

theorem circle {c d l : ℝ} (hu : c^2+d^2=2) (hl : 0≤4*Q0-l^2) :
    (X c d l+1)^2+(Y c d l)^2=2*Q0 := by
  have he : (X c d l+1)^2+(Y c d l)^2=
      (c^2+d^2)*(l^2+(N l)^2)/4 := by dsimp [X,Y]; ring
  rw [he,hu,N_sq hl]
  ring

theorem radial_tangent {c d l cp dp lp : ℝ}
    (hunit : c*cp+d*dp=0) (hl : 0<4*Q0-l^2) :
    (X c d l+1)*XD c d l cp dp lp+Y c d l*YD c d l cp dp lp=0 := by
  have hn := (N_pos hl).ne'
  have he : (X c d l+1)*XD c d l cp dp lp+Y c d l*YD c d l cp dp lp=
      (c^2+d^2)*(l*lp+N l*Nd l*lp)/4+
        (c*cp+d*dp)*(l^2+(N l)^2)/4 := by dsimp [X,Y,XD,YD]; ring
  rw [he,hunit]
  dsimp [Nd]
  field_simp [hn]
  ring

theorem contact_tangent {c d l cp dp lp : ℝ}
    (hu : c^2+d^2=2) (hunit : c*cp+d*dp=0) :
    d*XD c d l cp dp lp-c*YD c d l cp dp lp+
      dp*(X c d l+1)-cp*Y c d l=lp := by
  have he : d*XD c d l cp dp lp-c*YD c d l cp dp lp+
      dp*(X c d l+1)-cp*Y c d l=
        (c^2+d^2)*lp/2+(c*cp+d*dp)*l := by
    dsimp [X,Y,XD,YD]
    ring
  rw [he,hu,hunit]
  ring

theorem YD_contact {c d l cp dp lp : ℝ}
    (hu : c^2+d^2=2) (hunit : c*cp+d*dp=0)
    (hl : 0<4*Q0-l^2) (hX : X c d l+1≠0) :
    YD c d l cp dp lp*(c+d*(Y c d l/(X c d l+1)))=
      dp*(X c d l+1)-cp*Y c d l-lp := by
  have hr := radial_tangent hunit hl
  have ht := contact_tangent hu hunit
  apply (mul_right_cancel₀ hX)
  field_simp [hX]
  linear_combination -(X c d l+1)*ht+d*hr

theorem X_eq_chart {c d l : ℝ} (hu : c^2+d^2=2)
    (hl : 0≤4*Q0-l^2) (hX : 0≤X c d l+1) :
    X c d l=A (Y c d l) := by
  have hc := circle hu hl
  dsimp [A]
  rw [show 2*Q0-(Y c d l)^2=(X c d l+1)^2 by linarith,
    Real.sqrt_sq hX]
  ring

theorem target_root_bounds {c d l : ℝ}
    (hc : c∈Icc (4899/5000:ℝ) (51/50))
    (hd : d∈Icc (4899/5000:ℝ) (51/50))
    (hl : l∈Icc (197/100:ℝ) (12/5)) :
    0<4*Q0-l^2 ∧ 0<Y c d l ∧ Y c d l<4/5 ∧ 0<X c d l+1 := by
  have hsqL := pow_le_pow_left₀ (show 0≤l by linarith [hl.1]) hl.2 2
  have hsqU := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤197/100) hl.1 2
  have hrad : 0<4*Q0-l^2 := by norm_num [Q0] at *; nlinarith
  have hs := N_sq hrad.le
  have hn := N_pos hrad
  have hN : (157/50:ℝ)<N l ∧ N l<86/25 := by
    norm_num [Q0] at hs
    constructor <;> nlinarith
  have hc0 : 0≤c := by linarith [hc.1]
  have hd0 : 0≤d := by linarith [hd.1]
  have hl0 : 0≤l := by linarith [hl.1]
  have hclL := mul_le_mul hc.1 hl.1 (by norm_num) hc0
  have hclU := mul_le_mul hc.2 hl.2 hl0 (by norm_num)
  have hdnL := mul_le_mul hd.1 hN.1.le (by norm_num) hd0
  have hdnU := mul_le_mul hd.2 hN.2.le hn.le (by norm_num)
  have hdl := mul_pos (by linarith [hd.1] : 0<d) (by linarith [hl.1] : 0<l)
  have hcn := mul_pos (by linarith [hc.1] : 0<c) hn
  refine ⟨hrad,?_,?_,?_⟩ <;> dsimp [Y,X] <;> nlinarith

theorem source_root_bounds {l : ℝ} (hl : l∈Icc (19/10:ℝ) (243/100)) :
    0<4*Q0-l^2 ∧ 0<Y 1 1 l ∧ Y 1 1 l<4/5 ∧ 0<X 1 1 l+1 := by
  have hl0 : 0≤l := by linarith [hl.1]
  have hsqL := pow_le_pow_left₀ hl0 hl.2 2
  have hsqU := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19/10) hl.1 2
  have hrad : 0<4*Q0-l^2 := by norm_num [Q0] at *; nlinarith
  have hs := N_sq hrad.le
  have hn := N_pos hrad
  have hlt : l<N l := by norm_num [Q0] at hs; nlinarith
  have hut : N l<l+8/5 := by norm_num [Q0] at hs; nlinarith
  refine ⟨hrad,?_,?_,?_⟩ <;> dsimp [X,Y] <;> nlinarith

end SquaresInCircles.Eight.TableFree.FrameDiagonalContactRoot
