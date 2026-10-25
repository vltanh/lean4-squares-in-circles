module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Frames.NearestAxisSigns
public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Frames.Pair.Shape
public import SquaresInCircles.Eight.Owners.CircularNorm

/-!
# Eight squares: the two actual rotating norms in the core/high transverse support

Every norm is positive on the whole real line.  The exact circle identity
provides the global lower curvature bound; on the final first-quadrant
interval the positive-target norm has positive curvature itself.
-/

section
/-!
## The primary axis of a core source against a high target

A core state and a high state `B` separated along the primary axis of the core square, at a frame
angle `x ∈ [-203/250, 5/2]`, have the cost of the pair above `8833/10000`, for both signs of the
source and ties included (`core_primary`). The weak margin forces `x > 6/5`; for a negative target
it forces the marker `H B` above `7/10` (`negative_target_large_marker`, `core_primary_negative`),
and for a positive target it forces `x > 49/20` and then a marker below `27/50`
(`positive_target_cut`, `positive_target_small_marker`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighCorePrimary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2)
open FrameCoreHighGeometry

theorem trig_endpoints :
    (63/200:ℝ)<Real.cos (5/4:ℝ) ∧
      (637/1000:ℝ)<Real.sin (49/20:ℝ) ∧
        -(771/1000:ℝ)<Real.cos (49/20:ℝ) ∧
          (299/500:ℝ)<Real.sin (5/2:ℝ) ∧
            -(401/500:ℝ)<Real.cos (5/2:ℝ) := by
  have h0 := cos_lower_six (show (0:ℝ)≤5/4 by norm_num)
  have h1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤49/20 by norm_num)
  have h2 := Arithmetic.cos10_le_cos (show (0:ℝ)≤49/20 by norm_num)
  have h3 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤5/2 by norm_num)
  have h4 := Arithmetic.cos10_le_cos (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem negative_target_large_marker {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : x∈Icc (6/5:ℝ) (5/4))
    (hm : 0≤coreHighPrimary false a B x) : (7/10:ℝ)<H B := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (5/4:ℝ)≤Real.pi) hx.2
  have hA := mul_le_mul_of_nonneg_right
    (show (1399/1000:ℝ)≤A B+1/2 by linarith [hhigh.2.2.1]) ht.2.2.1
  have hBs := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤B-1/2 by linarith [hhigh.1])
  have hBl : (17/20:ℝ)<B := by
    dsimp [coreHighPrimary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [trig_endpoints.1]
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hB.1,hB.2⟩
  have hAu : A B<1 := by
    have hp : 0≤A B := by linarith [hhigh.2.2.1]
    norm_num [Q0] at hcircle
    nlinarith
  dsimp [H,u,v]
  linarith [k_bounds.1]

theorem core_primary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (6/5:ℝ)≤x)
    (hm : 0≤coreHighPrimary false a B x) :
    (8833/10000:ℝ)<coreHighCost i false a b B x := by
  have hsource := (FrameCoreArc.signed_label_bounds i hc).1
  have hch := CorePairGeometry.charge_upper x
  by_cases hlarge : (5/4:ℝ)≤x
  · have htarget := (H_bounds hB).1
    dsimp [coreHighCost,sign] at hsource ⊢
    linarith [H2_bounds.1]
  · have htarget := negative_target_large_marker hc hB ⟨hx,(lt_of_not_ge hlarge).le⟩ hm
    dsimp [coreHighCost,sign] at hsource ⊢
    linarith

theorem positive_target_cut {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (6/5:ℝ)≤x)
    (hm : 0≤coreHighPrimary true a B x) : (49/20:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · have ht := FrameLowPair.quadrant ⟨by linarith [hx],hfirst⟩
    have hA := mul_nonneg (by linarith [hhigh.2.2.1] : 0≤A B) ht.2.2.1
    have hBsin := mul_nonneg (by linarith [hhigh.1] : 0≤B) ht.1
    have hw := width_one_le x
    dsimp [coreHighPrimary,sign] at hm
    linarith
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := second_signs hxq
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (49/20:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (49/20:ℝ) from ⟨hxq.1,hsmall⟩)
      (by rw [Real.sin_pi_div_two]; norm_num : (637/1000:ℝ)<Real.sin (Real.pi/2))
      trig_endpoints.2.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have hd : -Real.cos x<(771/1000:ℝ) := by linarith [trig_endpoints.2.2.1]
    have hA := mul_le_mul_of_nonneg_right
      (show A B-1/2≤7/10 by linarith [hhigh.2.2.2]) (neg_nonneg.mpr ht.2)
    have hBsin := mul_le_mul_of_nonneg_right
      (show (10139/10000:ℝ)≤B+1/2 by linarith [hhigh.1]) ht.1
    dsimp [coreHighPrimary,sign] at hm
    rw [(second_width hxq).1] at hm
    nlinarith

theorem positive_target_small_marker {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (49/20:ℝ) (5/2)) (hm : 0≤coreHighPrimary true a B x) :
    H B<(27/50:ℝ) := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤49/20)
    (by linarith [FrameLowPair.pi_lower] : (5/2:ℝ)≤Real.pi) hx
    (by linarith [trig_endpoints.2.1] : (299/500:ℝ)<Real.sin (49/20:ℝ))
    trig_endpoints.2.2.2.1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hd : -Real.cos x<(401/500:ℝ) := by linarith [trig_endpoints.2.2.2.2]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤7/10 by linarith [hhigh.2.2.2]) (neg_nonneg.mpr ht.2)
  have hBsin := mul_le_mul_of_nonneg_left hs.le (show 0≤B+1/2 by linarith [hhigh.1])
  have hBu : B<(3/5:ℝ) := by
    dsimp [coreHighPrimary,sign] at hm
    rw [(second_width hxq).1] at hm
    nlinarith
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hB.1,hB.2⟩
  have hAl : (57/50:ℝ)<A B := by
    have hB2 := pow_le_pow_left₀ (show 0≤B+1/2 by linarith [hhigh.1])
      (show B+1/2≤11/10 by linarith) 2
    have hp : 0≤A B := by linarith [hhigh.2.2.1]
    norm_num [Q0] at hcircle
    nlinarith
  dsimp [H,u,v]
  linarith [k_bounds.2.1]

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2)) (hm : 0≤coreHighPrimary k a B x) :
    (8833/10000:ℝ)<coreHighCost i k a b B x := by
  have hcut := core_primary_angle k hc hB hx.1 hm
  cases k with
  | false => exact core_primary_negative i hc hB hcut.le hm
  | true =>
      have hcut' := positive_target_cut hc hB hcut.le hm
      have htarget := positive_target_small_marker hc hB ⟨hcut'.le,hx.2⟩ hm
      have hsource := (FrameCoreArc.signed_label_bounds i hc).1
      have hch := CorePairGeometry.charge_upper x
      dsimp [coreHighCost,sign] at hsource ⊢
      linarith

end SquaresInCircles.Eight.FrameCoreHighCorePrimary
end
end
end

section
/-!
## The actual norm majorant for the core/high primary support

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
end
end
end

section
/-!
## The complete core/low full-circle support

One cubic majorizes the actual norm throughout `[0,6/5]`.  Its exact
error polynomial has a concave second derivative, and the cost polynomial
is decreasing on the whole interval.  All fixed comparisons are rational
substitutions in the displayed formulas, without coefficient tables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowNorm
open FramePair FrameCircleArc FrameLowArc
open FrameMidArc (g)
open FramePairCalculus FramePairShape

def U (x : ℝ) : ℝ := 81/200+(543/500)*x-(37/1000)*x^2-(6/125)*x^3
def U1 (x : ℝ) : ℝ := 543/500-(37/500)*x-(18/125)*x^2
def U2 (x : ℝ) : ℝ := -(37/500)-(36/125)*x
def U3 : ℝ := -(36/125)
def C6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
def C4 (x : ℝ) : ℝ := 1-x^2/2+x^4/24
def S5 (x : ℝ) : ℝ := x-x^3/6+x^5/120
def S3 (x : ℝ) : ℝ := x-x^3/6
def P (x : ℝ) : ℝ :=
  (U x)^2-(u^2+v^2+g^2+2*g*(u*Arithmetic.sin9 x-v*C6 x))
def P1 (x : ℝ) : ℝ :=
  2*U x*U1 x-2*g*(u*Arithmetic.cos8 x+v*S5 x)
def P2 (x : ℝ) : ℝ :=
  2*((U1 x)^2+U x*U2 x)+2*g*(u*Arithmetic.sin7 x-v*C4 x)
def P3 (x : ℝ) : ℝ :=
  2*(3*U1 x*U2 x+U x*U3)+2*g*(u*C6 x+v*S3 x)
def P4 (x : ℝ) : ℝ :=
  -(12263172564/100000000000)-(444007233/1000000000)*x+
    x^2*(-(34388813718/100000000000)+(1450412055/10000000000)*x)-
      (7252060275/1000000000000)*x^5

theorem U_deriv (x : ℝ) : HasDerivAt U (U1 x) x := by
  have h := (((hasDerivAt_const x (81/200:ℝ)).add ((hasDerivAt_id' x).const_mul (543/500))).sub
    ((hasDerivAt_pow 2 x).const_mul (37/1000))).sub ((hasDerivAt_pow 3 x).const_mul (6/125))
  refine h.congr_deriv ?_
  rw [U1]
  ring

private theorem U1_deriv (x : ℝ) : HasDerivAt U1 (U2 x) x := by
  have h := ((hasDerivAt_const x (543/500:ℝ)).sub ((hasDerivAt_id' x).const_mul (37/500))).sub
    ((hasDerivAt_pow 2 x).const_mul (18/125))
  refine h.congr_deriv ?_
  rw [U2]
  ring

private theorem U2_deriv (x : ℝ) : HasDerivAt U2 U3 x := by
  have h := (hasDerivAt_const x (-(37/500):ℝ)).sub ((hasDerivAt_id' x).const_mul (36/125))
  refine h.congr_deriv ?_
  rw [U3]
  ring

private theorem sin7_deriv (x : ℝ) : HasDerivAt Arithmetic.sin7 (C6 x) x := by
  have h := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040)
  refine h.congr_deriv ?_
  rw [C6]
  ring

private theorem sin9_deriv (x : ℝ) : HasDerivAt Arithmetic.sin9 (Arithmetic.cos8 x) x := by
  have h := (sin7_deriv x).add ((hasDerivAt_pow 9 x).div_const 362880)
  refine h.congr_deriv ?_
  rw [C6,Arithmetic.cos8]
  ring

private theorem cos8_deriv (x : ℝ) : HasDerivAt Arithmetic.cos8 (-Arithmetic.sin7 x) x := by
  have h := ((((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720)).add
    ((hasDerivAt_pow 8 x).div_const 40320)
  refine h.congr_deriv ?_
  rw [Arithmetic.sin7]
  ring

private theorem C6_deriv (x : ℝ) : HasDerivAt C6 (-S5 x) x := by
  have h := (((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 6 x).div_const 720)
  refine h.congr_deriv ?_
  rw [S5]
  ring

private theorem S5_deriv (x : ℝ) : HasDerivAt S5 (C4 x) x := by
  have h := ((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120)
  refine h.congr_deriv ?_
  rw [C4]
  ring

private theorem C4_deriv (x : ℝ) : HasDerivAt C4 (-S3 x) x := by
  have h := ((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 4 x).div_const 24)
  refine h.congr_deriv ?_
  rw [S3]
  ring

private theorem S3_deriv (x : ℝ) : HasDerivAt S3 (1-x^2/2) x := by
  have h := (hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)
  refine h.congr_deriv ?_
  ring

theorem P_deriv (x : ℝ) : HasDerivAt P (P1 x) x := by
  have h := ((U_deriv x).pow 2).sub
    ((((sin9_deriv x).const_mul u).sub ((C6_deriv x).const_mul v)).const_mul (2*g)
      |>.const_add (u^2+v^2+g^2))
  refine h.congr_deriv ?_
  rw [P1]
  ring

theorem P1_deriv (x : ℝ) : HasDerivAt P1 (P2 x) x := by
  have h := (((U_deriv x).const_mul 2).mul (U1_deriv x)).sub
    ((((cos8_deriv x).const_mul u).add ((S5_deriv x).const_mul v)).const_mul (2*g))
  refine h.congr_deriv ?_
  rw [P2]
  ring

theorem P2_deriv (x : ℝ) : HasDerivAt P2 (P3 x) x := by
  have h := ((((U1_deriv x).pow 2).add ((U_deriv x).mul (U2_deriv x))).const_mul 2).add
    ((((sin7_deriv x).const_mul u).sub ((C4_deriv x).const_mul v)).const_mul (2*g))
  refine h.congr_deriv ?_
  rw [P3]
  ring

theorem P3_deriv (x : ℝ) : HasDerivAt P3 (P4 x) x := by
  have h := (((((U1_deriv x).const_mul 3).mul (U2_deriv x)).add ((U_deriv x).mul_const U3)).const_mul 2).add
    ((((C6_deriv x).const_mul u).add ((S3_deriv x).const_mul v)).const_mul (2*g))
  refine h.congr_deriv ?_
  simp only [P4,U1,U2,U3,S5,u,v,g]
  ring

theorem P4_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : P4 x<0 := by
  have hcoef : -(34388813718/100000000000:ℝ)+(1450412055/10000000000)*x<0 := by
    linarith [hx.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hcoef.le
  have hp := pow_nonneg hx.1 5
  dsimp [P4]
  nlinarith [hx.1]

theorem P3_antitone : AntitoneOn P3 (Icc (0:ℝ) (6/5)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (P3_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P3_deriv x
  · exact fun x hx => (P4_negative (Ioo_subset_Icc_self hx)).le

theorem P2_concave : ConcaveOn ℝ (Icc (0:ℝ) (6/5)) P2 :=
  concave_of_deriv2 (fun x _ => P2_deriv x) (fun x _ => P3_deriv x)
    (fun _ hx => (P4_negative hx).le)

theorem P3_initial_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) :
    (1/40:ℝ)<P3 x := by
  have hh := P3_antitone ⟨hx.1,by linarith [hx.2]⟩
    ⟨by norm_num,by norm_num⟩ hx.2
  have he : (1/40:ℝ)<P3 (1/2:ℝ) := by
    norm_num [P3,U,U1,U2,U3,C6,S3,u,v,g]
  exact he.trans_le hh

theorem P1_initial_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) : 0<P1 x := by
  apply positive_of_curvature (κ := (1/40:ℝ)) (by norm_num) hx
    (show (2/5:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num)
    (fun x _ => P1_deriv x) (fun x _ => P2_deriv x)
    (fun x hx => (P3_initial_lower hx).le)
  norm_num [P1,P2,U,U1,U2,C4,S5,Arithmetic.cos8,Arithmetic.sin7,u,v,g]

theorem P_initial_monotone : MonotoneOn P (Icc (0:ℝ) (1/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (P_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P_deriv x
  · exact fun x hx => (P1_initial_positive (Ioo_subset_Icc_self hx)).le

theorem P_endpoint_lower : (1/6000:ℝ)<P 0 ∧ (1/6000:ℝ)<P (6/5:ℝ) := by
  constructor <;> norm_num [P,U,C6,Arithmetic.sin9,Arithmetic.sin7,u,v,g]

theorem P_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : (1/6000:ℝ)<P x := by
  have hhalf : (1/6000:ℝ)<P (1/2:ℝ) :=
    P_endpoint_lower.1.trans_le (P_initial_monotone
      ⟨le_rfl,by norm_num⟩ ⟨by norm_num,le_rfl⟩ (by norm_num))
  by_cases hfirst : x≤1/2
  · exact P_endpoint_lower.1.trans_le
      (P_initial_monotone ⟨le_rfl,by norm_num⟩ ⟨hx.1,hfirst⟩ hx.1)
  · have he : 0≤P2 (1/2:ℝ) := by
      norm_num [P2,U,U1,U2,C4,Arithmetic.sin7,u,v,g]
    have hd := (P1_initial_positive (show (1/2:ℝ)∈Icc (0:ℝ) (1/2) by
      constructor <;> norm_num)).le
    have hh := endpoint_minimum_of_concave_second
      (show x∈Icc (1/2:ℝ) (6/5) from ⟨(lt_of_not_ge hfirst).le,hx.2⟩)
      (fun x _ => P_deriv x) (fun x _ => P1_deriv x)
      (P2_concave.subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _)) he hd
    exact (lt_min hhalf P_endpoint_lower.2).trans_le hh

theorem U_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : 0<U x := by
  have hm : MonotoneOn U (Icc (0:ℝ) (6/5)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (U_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => U_deriv x
    · intro x hx
      have hx2 := pow_le_pow_left₀ hx.1.le hx.2.le 2
      dsimp [U1]
      nlinarith [hx.2]
  have hh := hm ⟨le_rfl,by norm_num⟩ hx hx.1
  have h0 : U 0=81/200 := by norm_num [U]
  linarith

def N (x : ℝ) : ℝ := Real.sqrt (u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x))
def F (x : ℝ) : ℝ :=
  x+(g+9/50+u+v)/2+u*a0+(g-9/100)*Real.sin x-(9/100)*Real.cos x-R*N x

theorem N_sq {x : ℝ} (_hx : x∈Icc (0:ℝ) (6/5)) :
    (N x)^2=u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x) := by
  have he : u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x)=
      (u+g*Real.sin x)^2+(v-g*Real.cos x)^2 := by
    linear_combination -g^2*(Real.sin_sq_add_cos_sq x)
  exact Real.sq_sqrt (by rw [he]; positivity)

theorem norm_upper {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : N x<U x := by
  have hp := P_positive hx
  have hu := U_positive hx
  have hn := N_sq hx
  have hs := Arithmetic.sin_le_sin9 hx.1
  have hc : C6 x≤Real.cos x := by simpa [C6] using cos_lower_six hx.1
  dsimp [P] at hp
  dsimp [u,v,g] at *
  nlinarith [Real.sqrt_nonneg
    (u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x))]

def costPolynomial (x : ℝ) : ℝ :=
  x+(g+9/50+u+v)/2+u*(2829/2000)-91/100+
    (g-9/100)*Arithmetic.sin7 x-(9/100)*Arithmetic.cos8 x-(1979/1000)*U x
def costDerivative (x : ℝ) : ℝ :=
  -(80911/500000)+(118223/500000)*x-(20871/100000)*x^2-
    (3/200)*x^3+(82281/2000000)*x^4+(3/4000)*x^5-
      (27427/20000000)*x^6-x^7/56000

theorem costPolynomial_deriv (x : ℝ) :
    HasDerivAt costPolynomial (costDerivative x) x := by
  have h := ((((((hasDerivAt_id' x).add_const ((g+9/50+u+v)/2)).add_const (u*(2829/2000))).sub_const
    (91/100)).add ((sin7_deriv x).const_mul (g-9/100))).sub
    ((cos8_deriv x).const_mul (9/100))).sub ((U_deriv x).const_mul (1979/1000))
  refine h.congr_deriv ?_
  simp only [costDerivative,C6,Arithmetic.sin7,U1,g]
  ring

theorem costDerivative_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    costDerivative x< -(1/20:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := pow_le_pow_left₀ hx.1 hx.2 3
  have hx4 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  have hx5 := mul_le_mul_of_nonneg_right hx3 (sq_nonneg x)
  have h3 := pow_nonneg hx.1 3
  have h6 := pow_nonneg hx.1 6
  have h7 := pow_nonneg hx.1 7
  dsimp [costDerivative]
  nlinarith [sq_nonneg ((7/25)*x-237/1000)]

theorem costPolynomial_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    (13/1000:ℝ)<costPolynomial x := by
  have hm : AntitoneOn costPolynomial (Icc (0:ℝ) (6/5)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun x _ => (costPolynomial_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => costPolynomial_deriv x
    · intro x hx
      linarith [costDerivative_negative (Ioo_subset_Icc_self hx)]
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have he : (13/1000:ℝ)<costPolynomial (6/5:ℝ) := by
    norm_num [costPolynomial,U,Arithmetic.sin7,Arithmetic.cos8,u,v,g]
  exact he.trans_le hh

theorem full_circle_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : (91/100:ℝ)<F x := by
  have hu := U_positive hx
  have hn := norm_upper hx
  have hR : R<(1979/1000:ℝ) := by
    have hh := R_sq
    norm_num [Q0] at hh
    nlinarith [R_pos]
  have hRN : R*N x<(1979/1000)*U x :=
    (mul_lt_mul_of_pos_left hn R_pos).trans (mul_lt_mul_of_pos_right hR hu)
  have hs : Arithmetic.sin7 x≤Real.sin x := by
    have := sin_lower_seven hx.1
    unfold Arithmetic.sin7
    linarith
  have hc := Arithmetic.cos_le_cos8 hx.1
  have hpoly := costPolynomial_lower hx
  have ha : (2829/2000:ℝ)<a0 := by linarith [a0_bounds.1]
  dsimp [F,costPolynomial,u,v,g] at *
  linarith

end SquaresInCircles.Eight.FrameCoreLowNorm
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighSecondaryNorm
open FramePair FrameCircleArc FrameHighArc FramePairCalculus
open FrameMidArc (g)

def E : ℝ := g^2+u^2+v^2
def B : ℝ := -2*g*v
def C (j : Bool) : ℝ := -2*g*sign j*u
def N (j : Bool) (x : ℝ) : ℝ := CircularNorm.norm E B (C j) x
def Nd (j : Bool) (x : ℝ) : ℝ := CircularNorm.d1 E B (C j) x
def Ndd (j : Bool) (x : ℝ) : ℝ := CircularNorm.d2 E B (C j) x

theorem energy_positive (j : Bool) (x : ℝ) : 0<CircularNorm.energy E B (C j) x := by
  have ht : sign j*u*Real.sin x+v*Real.cos x<(7/10:ℝ) := by
    apply FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<7/10)
    cases j <;> norm_num [sign,u,v]
  have hg := mul_lt_mul_of_pos_left ht (show 0<2*g by norm_num [g])
  dsimp [CircularNorm.energy,E,B,C,g,u,v] at *
  nlinarith

theorem N_pos (j : Bool) (x : ℝ) : 0<N j x := CircularNorm.norm_pos (energy_positive j x)
theorem N_sq (j : Bool) (x : ℝ) : (N j x)^2=CircularNorm.energy E B (C j) x :=
  CircularNorm.norm_sq (energy_positive j x).le
theorem N_deriv (j : Bool) (x : ℝ) : HasDerivAt (N j) (Nd j x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive j x)
theorem Nd_deriv (j : Bool) (x : ℝ) : HasDerivAt (Nd j) (Ndd j x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive j x)

theorem N_upper (j : Bool) (x : ℝ) : N j x<g+7/10 := by
  have ht : -sign j*u*Real.sin x-v*Real.cos x<(7/10:ℝ) := by
    have hh := FrameCoreArc.projection_lt (a := -sign j*u) (b := -v)
      (by norm_num : (0:ℝ)<7/10)
      (by cases j <;> norm_num [sign,u,v]) x
    nlinarith
  have hN := N_sq j x
  have hp := N_pos j x
  have hg := mul_lt_mul_of_pos_left ht (show 0<2*g by norm_num [g])
  dsimp [CircularNorm.energy,E,B,C,g,u,v] at *
  nlinarith

theorem curvature_lower (j : Bool) (x : ℝ) : -(N j x)/4≤Ndd j x := by
  apply CircularNorm.curvature_lower (energy_positive j x)
  cases j <;> norm_num [E,B,C,sign,g,u,v]

theorem curvature_work (j : Bool) (x : ℝ) : -R*Ndd j x<(9/10:ℝ) := by
  have hc := curvature_lower j x
  have hR := radius_bound
  have hRN : R*N j x<radiusUpper*(g+7/10) :=
    mul_lt_mul'' hR (N_upper j x) R_pos.le (N_pos j x).le
  have hh := mul_le_mul_of_nonneg_left hc R_pos.le
  norm_num [radiusUpper,g] at hRN
  linarith

theorem trig_seven_fifths :
    (197/200:ℝ)<Real.sin (7/5:ℝ) ∧ Real.sin (7/5:ℝ)<493/500 ∧
      (169/1000:ℝ)<Real.cos (7/5:ℝ) ∧ Real.cos (7/5:ℝ)<17/100 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/5 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤7/5 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem positive_first_trig {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) :
    (197/200:ℝ)<Real.sin x ∧ 0≤Real.cos x ∧ Real.cos x<17/100 := by
  have ht := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(7/5:ℝ)) hx.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤7/5)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  exact ⟨by linarith [trig_seven_fifths.1],ht.2.2.1,
    by linarith [trig_seven_fifths.2.2.2]⟩

theorem positive_norm_monotone : MonotoneOn (N true) (Icc (7/5:ℝ) (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv true x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv true x
  · intro x hx
    have ht := positive_first_trig (Ioo_subset_Icc_self hx)
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope,B,C,sign]
    apply div_nonneg
    · norm_num [g,u,v]
      nlinarith
    · exact mul_nonneg (by norm_num) (N_pos true x).le

theorem positive_quarter_norm : N true (Real.pi/2)=FrameCoreHighNorm.n 1 := by
  dsimp [N,CircularNorm.norm,CircularNorm.energy,E,B,C,FrameCoreHighNorm.n,
    FrameCoreHighNorm.energy,sign]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,add_zero]
  congr 1
  ring

theorem positive_norm_curvature {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) : 0<Ndd true x := by
  have hN := positive_norm_monotone hx
    ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hx.2
  rw [positive_quarter_norm] at hN
  have hNu : N true x<(641/1000:ℝ) := by linarith [FrameCoreHighNorm.n_one_bounds.2]
  have hNp := N_pos true x
  have hN2 : (N true x)^2<(641/1000:ℝ)^2 := by nlinarith
  have hD : (641/1000:ℝ)^2<g^2-u^2-v^2 := by norm_num [g,u,v]
  have hnum : (N true x)^4<(g^2-u^2-v^2)^2 := by nlinarith [sq_nonneg (N true x)]
  have hid := CircularNorm.curvature_identity (energy_positive true x)
  have he : E^2-B^2-(C true)^2=(g^2-u^2-v^2)^2 := by
    dsimp [E,B,C,sign]
    ring
  rw [he] at hid
  change Ndd true x+N true x/4=(g^2-u^2-v^2)^2/(4*(N true x)^3) at hid
  have hdiv : N true x/4<(g^2-u^2-v^2)^2/(4*(N true x)^3) := by
    apply (lt_div_iff₀ (by positivity : 0<4*(N true x)^3)).2
    nlinarith only [hnum]
  linarith

theorem norm_endpoints :
    N false 0<(223/250:ℝ) ∧ N false (6/5)<63/40 ∧
      N true (7/5)<67/125 ∧ N true (5/2)<63/50 := by
  have h0 := N_sq false 0
  have hp0 := N_pos false 0
  have h12 := N_sq false (6/5)
  have hp12 := N_pos false (6/5)
  have ht12 := FrameCoreMidScalars.trig_six_fifths
  have h14 := N_sq true (7/5)
  have hp14 := N_pos true (7/5)
  have ht14 := trig_seven_fifths
  have h25 := N_sq true (5/2)
  have hp25 := N_pos true (5/2)
  have ht25 := FrameCoreHighCorePrimary.trig_endpoints
  dsimp [CircularNorm.energy,E,B,C,sign,g,u,v] at h0 h12 h14 h25
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero] at h0
  refine ⟨?_,?_,?_,?_⟩
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h0]; norm_num)
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h12]; norm_num; linarith [ht12.2.1,ht12.2.2.1])
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h14]; norm_num; linarith [ht14.1,ht14.2.2.1])
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h25]; norm_num; linarith [ht25.2.2.2.1,ht25.2.2.2.2])

end SquaresInCircles.Eight.FrameCoreHighSecondaryNorm
end
end
end
