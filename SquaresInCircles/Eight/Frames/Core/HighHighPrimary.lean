module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Core.MidFullCircle
public import SquaresInCircles.Eight.Frames.Core.HighSecondaryNorm
public import SquaresInCircles.Eight.Frames.Low.Pair

/-!
# Eight squares: every original high-source primary witness against a core state

The cancellation multiplier acts on the original weak margin and retains
the entire high circle.  The positive rounded-core branch uses the exact
radical cap forced by that same margin.
-/

section
/-!
## The whole initial core/high primary interval by curvature

The actual trigonometric support is positive on `[3/4,3/2]`.
A sixth-derivative bound proves that its second derivative is concave;
one tangent then gives a uniform upper curvature bound.  The endpoint
chord has a strict rational reserve on the entire original interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighPrimaryCurvature
open FramePair FrameCircleArc FrameHighArc FrameCurvature FrameCoreHighNorm
open FrameMidArc (g)

def gamma : ℝ := 8833/10000
def aa : ℝ := 13*g/12
def B0 : ℝ := 9/100-kUpper+(-u+v+g)/2-gamma+(457/500)*radiusUpper
def B2 : ℝ := 9/100+(7/20)*radiusUpper
def C0 : ℝ := g-(602451/500000)*radiusUpper
def F (x : ℝ) : ℝ :=
  (x+B0)*Real.sin x-B2*(Real.sin x)^2-(9/100)*Real.sin x*Real.cos x+C0+aa*Real.cos x
def F1 (x : ℝ) : ℝ :=
  (1-aa)*Real.sin x+(x+B0)*Real.cos x-2*B2*Real.sin x*Real.cos x-(9/100)*Real.cos (2*x)
def F2 (x : ℝ) : ℝ :=
  (2-aa)*Real.cos x-(x+B0)*Real.sin x-2*B2*Real.cos (2*x)+(9/50)*Real.sin (2*x)
def F3 (x : ℝ) : ℝ :=
  -(3-aa)*Real.sin x-(x+B0)*Real.cos x+4*B2*Real.sin (2*x)+(9/25)*Real.cos (2*x)
def F4 (x : ℝ) : ℝ :=
  -(4-aa)*Real.cos x+(x+B0)*Real.sin x+8*B2*Real.cos (2*x)-(18/25)*Real.sin (2*x)
def F5 (x : ℝ) : ℝ :=
  (5-aa)*Real.sin x+(x+B0)*Real.cos x-16*B2*Real.sin (2*x)-(36/25)*Real.cos (2*x)
def F6 (x : ℝ) : ℝ :=
  (6-aa)*Real.cos x-(x+B0)*Real.sin x-32*B2*Real.cos (2*x)+(72/25)*Real.sin (2*x)

theorem F_deriv (x : ℝ) : HasDerivAt F (F1 x) x := by
  have h := ((((((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_sin x)).sub
    (((Real.hasDerivAt_sin x).pow 2).const_mul B2)).sub
    (((Real.hasDerivAt_sin x).const_mul (9/100)).mul (Real.hasDerivAt_cos x))).add_const C0).add
    ((Real.hasDerivAt_cos x).const_mul aa)
  refine h.congr_deriv ?_
  rw [F1,Real.cos_two_mul]
  linear_combination (9/100:ℝ)*Real.sin_sq_add_cos_sq x

theorem F1_deriv (x : ℝ) : HasDerivAt F1 (F2 x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul (1-aa)).add
    (((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_cos x))).sub
    (((Real.hasDerivAt_sin x).const_mul (2*B2)).mul (Real.hasDerivAt_cos x))).sub
    ((((hasDerivAt_id' x).const_mul 2).cos).const_mul (9/100))
  refine h.congr_deriv ?_
  rw [F2,Real.cos_two_mul]
  linear_combination (2*B2)*Real.sin_sq_add_cos_sq x

theorem F2_deriv (x : ℝ) : HasDerivAt F2 (F3 x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (2-aa)).sub
    (((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_sin x))).sub
    ((((hasDerivAt_id' x).const_mul 2).cos).const_mul (2*B2))).add
    ((((hasDerivAt_id' x).const_mul 2).sin).const_mul (9/50))
  refine h.congr_deriv ?_
  rw [F3]
  ring

theorem F3_deriv (x : ℝ) : HasDerivAt F3 (F4 x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul (-(3-aa))).sub
    (((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_cos x))).add
    ((((hasDerivAt_id' x).const_mul 2).sin).const_mul (4*B2))).add
    ((((hasDerivAt_id' x).const_mul 2).cos).const_mul (9/25))
  refine h.congr_deriv ?_
  rw [F4]
  ring

theorem F4_deriv (x : ℝ) : HasDerivAt F4 (F5 x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (-(4-aa))).add
    (((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_sin x))).add
    ((((hasDerivAt_id' x).const_mul 2).cos).const_mul (8*B2))).sub
    ((((hasDerivAt_id' x).const_mul 2).sin).const_mul (18/25))
  refine h.congr_deriv ?_
  rw [F5]
  ring

theorem F5_deriv (x : ℝ) : HasDerivAt F5 (F6 x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul (5-aa)).add
    (((hasDerivAt_id' x).add_const B0).mul (Real.hasDerivAt_cos x))).sub
    ((((hasDerivAt_id' x).const_mul 2).sin).const_mul (16*B2))).sub
    ((((hasDerivAt_id' x).const_mul 2).cos).const_mul (36/25))
  refine h.congr_deriv ?_
  rw [F6]
  ring

theorem B0_positive : 0<B0 := by
  norm_num [B0,gamma,kUpper,radiusUpper,u,v,g]

theorem F6_upper {x : ℝ} (hx : x∈Icc (3/4:ℝ) (3/2)) : F6 x<(29:ℝ) := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤3/4)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hc0 := cos_upper_four (show (0:ℝ)≤3/4 by norm_num)
  have hcU : Real.cos x<(733/1000:ℝ) := by norm_num at hc0; linarith
  have hprod := mul_nonneg (show 0≤x+B0 by linarith [hx.1,B0_positive]) ht.1
  have hamp : (72/25:ℝ)^2+(-32*B2)^2<(2521/100:ℝ)^2 := by
    norm_num [B2,radiusUpper]
  have hh := FrameCoreArc.projection_lt (a := (72/25:ℝ)) (b := -32*B2)
    (by norm_num : (0:ℝ)<2521/100) hamp (2*x)
  have hcos := mul_le_mul_of_nonneg_left hcU.le (show 0≤6-aa by norm_num [aa,g])
  dsimp [F6,aa,g] at *
  nlinarith

theorem fixed_products {x : ℝ} (hx : 0≤x)
    (hs : 0≤HighOrderTaylor.S11 x) (hc : 0≤HighOrderTaylor.C14 x) :
    (HighOrderTaylor.S11 x)^2≤(Real.sin x)^2 ∧
      (Real.sin x)^2≤(HighOrderTaylor.S13 x)^2 ∧
        (HighOrderTaylor.C14 x)^2≤(Real.cos x)^2 ∧
          (Real.cos x)^2≤(HighOrderTaylor.C12 x)^2 ∧
            HighOrderTaylor.S11 x*HighOrderTaylor.C14 x≤Real.sin x*Real.cos x ∧
              Real.sin x*Real.cos x≤HighOrderTaylor.S13 x*HighOrderTaylor.C12 x := by
  exact product_cage hs hc
    ⟨HighOrderTaylor.S11_le_sin hx,HighOrderTaylor.sin_le_S13 hx⟩
    ⟨HighOrderTaylor.C14_le_cos hx,HighOrderTaylor.cos_le_C12 hx⟩

theorem fourth_contact : F4 (9/8)< -(423/100:ℝ) ∧ |F5 (9/8)|<(117/25:ℝ) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤9/8 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤9/8 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤9/8 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤9/8 by norm_num)
  have hp := fixed_products (x := (9/8:ℝ)) (by norm_num)
    (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8])
  rcases hp with ⟨hs2L,hs2U,hc2L,hc2U,hscL,hscU⟩
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  dsimp [F4,F5,aa,B0,B2,C0,gamma,kUpper,radiusUpper,u,v,g]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  refine ⟨by nlinarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

theorem F4_negative {x : ℝ} (hx : x∈Icc (3/4:ℝ) (3/2)) : F4 x<0 := by
  have hh := upper_tangent (M := (29:ℝ)) hx
    (show (9/8:ℝ)∈Icc (3/4:ℝ) (3/2) by constructor <;> norm_num)
    (fun z _ => F4_deriv z) (fun z _ => F5_deriv z) (fun z hz => (F6_upper hz).le)
  have hdist : |x-9/8|≤(3/8:ℝ) := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hsq : (x-9/8)^2≤(3/8:ℝ)^2 := by
    nlinarith [sq_abs (x-9/8),pow_le_pow_left₀ (abs_nonneg (x-9/8)) hdist 2]
  have hmul := mul_le_mul fourth_contact.2.le hdist (abs_nonneg (x-9/8)) (by norm_num)
  have hterm := le_abs_self (F5 (9/8)*(x-9/8))
  rw [abs_mul] at hterm
  nlinarith [fourth_contact.1]

theorem second_contact : F2 (13/12)<(3/1000:ℝ) ∧ |F3 (13/12)|<(1/50:ℝ) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤13/12 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤13/12 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤13/12 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤13/12 by norm_num)
  have hp := fixed_products (x := (13/12:ℝ)) (by norm_num)
    (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
    (by norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8])
  rcases hp with ⟨hs2L,hs2U,hc2L,hc2U,hscL,hscU⟩
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  dsimp [F2,F3,aa,B0,B2,C0,gamma,kUpper,radiusUpper,u,v,g]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  refine ⟨by nlinarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

theorem F2_upper {x : ℝ} (hx : x∈Icc (3/4:ℝ) (3/2)) : F2 x<(3/250:ℝ) := by
  have hh := upper_tangent (M := (0:ℝ)) hx
    (show (13/12:ℝ)∈Icc (3/4:ℝ) (3/2) by constructor <;> norm_num)
    (fun z _ => F2_deriv z) (fun z _ => F3_deriv z) (fun z hz => (F4_negative hz).le)
  have hdist : |x-13/12|≤(5/12:ℝ) := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hmul := mul_le_mul second_contact.2.le hdist (abs_nonneg (x-13/12)) (by norm_num)
  have hterm := le_abs_self (F3 (13/12)*(x-13/12))
  rw [abs_mul] at hterm
  nlinarith [second_contact.1]

theorem F_endpoints : (3/1000:ℝ)<F (3/4) ∧ (3/1000:ℝ)<F (3/2) := by
  constructor
  all_goals
    first
    | have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤3/4 by norm_num)
      have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤3/4 by norm_num)
      have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤3/4 by norm_num)
      have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤3/4 by norm_num)
      have hp := fixed_products (x := (3/4:ℝ)) (by norm_num)
        (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
        (by norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8])
      rcases hp with ⟨hs2L,hs2U,hc2L,hc2U,hscL,hscU⟩
      norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
        HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
      dsimp [F,aa,B0,B2,C0,gamma,kUpper,radiusUpper,u,v,g]
      nlinarith
    | have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤3/2 by norm_num)
      have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤3/2 by norm_num)
      have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤3/2 by norm_num)
      have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤3/2 by norm_num)
      have hp := fixed_products (x := (3/2:ℝ)) (by norm_num)
        (by norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7])
        (by norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8])
      rcases hp with ⟨hs2L,hs2U,hc2L,hc2U,hscL,hscU⟩
      norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
        HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
      dsimp [F,aa,B0,B2,C0,gamma,kUpper,radiusUpper,u,v,g]
      nlinarith

theorem F_positive {x : ℝ} (hx : x∈Icc (3/4:ℝ) (3/2)) : 0<F x := by
  have hh := lower_of_upper_curvature (M := (3/250:ℝ)) (m := (3/1000:ℝ)) hx
    (by norm_num) (fun z _ => F_deriv z) (fun z _ => F1_deriv z)
    (fun z hz => (F2_upper hz).le) F_endpoints.1 F_endpoints.2
  norm_num at hh
  linarith

def primaryFirst (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)-k+(-u+v+g)/2+
    g/Real.sin x+(13*g/12)*Real.cos x/Real.sin x-
      R*Real.sqrt ((g/Real.sin x-u)^2+v^2)

theorem primaryFirst_lower {x : ℝ} (hx : x∈Icc (3/4:ℝ) (3/2)) : gamma<primaryFirst x := by
  have hs0 : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hx.1]) (by linarith [hx.2,FrameLowPair.pi_lower])
  have hs : Real.sin x∈Icc (0:ℝ) 1 := ⟨hs0.le,Real.sin_le_one x⟩
  have hn := n_upper hs
  have hu : 0<upper (Real.sin x) := (n_positive hs).trans hn
  have hRN := (mul_lt_mul_of_pos_left hn R_pos).trans
    (mul_lt_mul_of_pos_right radius_bound hu)
  have hK := mul_lt_mul_of_pos_right k_bounds.2.2 hs0
  have hscale := norm_rescale hs0
  have h1 : g/Real.sin x*Real.sin x=g := div_mul_cancel₀ g hs0.ne'
  have h2 : (13*g/12)*Real.cos x/Real.sin x*Real.sin x=(13*g/12)*Real.cos x :=
    div_mul_cancel₀ _ hs0.ne'
  have he : (primaryFirst x-gamma)*Real.sin x-F x=
      (kUpper-k)*Real.sin x+radiusUpper*upper (Real.sin x)-R*n (Real.sin x) := by
    simp only [primaryFirst,F,B0,B2,C0,aa,upper]
    linear_combination h1+h2-R*hscale
  have hf := F_positive hx
  have hpos : 0<(primaryFirst x-gamma)*Real.sin x := by linarith
  linarith [(mul_pos_iff_of_pos_right hs0).mp hpos]

end SquaresInCircles.Eight.FrameCoreHighPrimaryCurvature
end
end
end

section
/-!
## The actual core/high primary continuation through the quarter turn

The first-quadrant support decreases to the exact quarter value.  The
second-quadrant support is concave on its whole interval.  The norm and
its radial projection are controlled directly by their squared identities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighPrimaryContinuation
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreHighPrimaryCurvature (gamma primaryFirst)

def X (x : ℝ) : ℝ := g/Real.sin x-u
def N (x : ℝ) : ℝ := Real.sqrt ((X x)^2+v^2)
def Z (x : ℝ) : ℝ := R*X x/N x
def Xd (x : ℝ) : ℝ := -g*Real.cos x/(Real.sin x)^2
def Nd (x : ℝ) : ℝ := X x*Xd x/N x
def Zd (x : ℝ) : ℝ := -R*v^2*g*Real.cos x/((Real.sin x)^2*(N x)^3)
def firstD (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^2*(Real.cos x*(Z x-1)-13/12)
def primarySecond (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x-Real.cos x-1)-k+(-u+v+g)/2+
    g/Real.sin x+(g/12)*Real.cos x/Real.sin x-R*N x
def secondD (x : ℝ) : ℝ :=
  1-(9/100)*(Real.sin x+Real.cos x)+
    g/(Real.sin x)^2*(Real.cos x*(Z x-1)-1/12)
def secondDD (x : ℝ) : ℝ :=
  (9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^3*((1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6)-
      R*v^2*g^2*(Real.cos x)^2/((Real.sin x)^4*(N x)^3)
def quarterValue : ℝ :=
  Real.pi/4+3*g/2-(u-v)*(c0+1/2)-R*FrameCoreHighNorm.n 1

theorem interval_sine {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (299/500:ℝ)<Real.sin x := by
  apply sin_endpoint_lower (by norm_num : (0:ℝ)≤3/4)
    (by linarith [FrameLowPair.pi_lower] : (5/2:ℝ)≤Real.pi) hx
  · have hh := Real.sin_ge_sub_cube (show (0:ℝ)≤3/4 by norm_num)
    norm_num at hh
    linarith
  · exact FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1

theorem X_lower {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) : g-u≤X x := by
  have hs : 0<Real.sin x := by linarith [interval_sine hx]
  have hg : g≤g/Real.sin x := (le_div_iff₀ hs).2
    (mul_le_of_le_one_right (by norm_num [g] : 0≤g) (Real.sin_le_one x))
  dsimp [X]
  linarith

theorem N_pos (x : ℝ) : 0<N x := by
  apply Real.sqrt_pos.mpr
  have hv : (0:ℝ)<v^2 := by norm_num [v]
  nlinarith [sq_nonneg (X x)]

theorem N_sq (x : ℝ) : (N x)^2=(X x)^2+v^2 := Real.sq_sqrt (by positivity)

theorem Z_bounds {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (39/25:ℝ)<Z x ∧ Z x<(1979/1000:ℝ) := by
  have hxL := X_lower hx
  have hx0 : 0<X x := by norm_num [g,u] at hxL; linarith
  have hn := N_pos x
  have hns := N_sq x
  have hr := R_sq
  have hNgt : X x<N x := by norm_num [v] at hns; nlinarith
  have hu : Z x<R := by
    dsimp [Z]
    apply (div_lt_iff₀ hn).2
    exact mul_lt_mul_of_pos_left hNgt R_pos
  have hXsq := pow_le_pow_left₀
    (show (0:ℝ)≤g-u by norm_num [g,u]) hxL 2
  have hl : (39/25:ℝ)*N x<R*X x := by
    have hp := mul_pos R_pos hx0
    have hprod : ((39/25:ℝ)*N x)^2<(R*X x)^2 := by
      rw [mul_pow,mul_pow,hr,hns]
      norm_num [Q0,g,u,v] at *
      nlinarith
    nlinarith
  exact ⟨(lt_div_iff₀ hn).2 hl,hu.trans (by
    have hh := radius_bound
    norm_num [radiusUpper] at hh
    linarith)⟩

theorem X_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt X (Xd x) x := by
  have h := ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs).sub_const u
  convert h using 1
  · rfl
  · simp only [Xd]; ring

theorem N_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt N (Nd x) x := by
  have hp : 0<(X x)^2+v^2 := by
    have hv : (0:ℝ)<v^2 := by norm_num [v]
    nlinarith [sq_nonneg (X x)]
  have h := (((X_deriv hs).pow 2).add_const (v^2)).sqrt hp.ne'
  convert h using 1
  · rfl
  · simp only [Nd,N]; norm_num; ring

theorem Z_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt Z (Zd x) x := by
  have hn := (N_pos x).ne'
  have hd := ((X_deriv hs).const_mul R).div (N_deriv hs) hn
  convert hd using 1
  · rfl
  · simp only [Zd,Nd,Xd]
    field_simp
    linear_combination (R*g*Real.cos x)*N_sq x

theorem first_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt primaryFirst (firstD x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub ((((Real.hasDerivAt_sin x).fun_add
    (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))).sub_const k).add_const
      ((-u+v+g)/2)).fun_add ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs)
  have hd := (hbase.fun_add (((Real.hasDerivAt_cos x).const_mul (13*g/12)).div
    (Real.hasDerivAt_sin x) hs)).fun_sub ((N_deriv hs).const_mul R)
  convert hd using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [firstD,Nd,Xd,Z]
    field_simp
    linear_combination (1300*N x*g)*Real.sin_sq_add_cos_sq x

theorem second_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt primarySecond (secondD x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub ((((Real.hasDerivAt_sin x).fun_sub
    (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))).sub_const k).add_const
      ((-u+v+g)/2)).fun_add ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs)
  have hd := (hbase.fun_add (((Real.hasDerivAt_cos x).const_mul (g/12)).div
    (Real.hasDerivAt_sin x) hs)).fun_sub ((N_deriv hs).const_mul R)
  convert hd using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [secondD,Nd,Xd,Z]
    field_simp
    linear_combination (100*N x*g)*Real.sin_sq_add_cos_sq x

theorem secondD_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt secondD (secondDD x) x := by
  have hbase := (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul
    (9/100)).const_sub 1
  have hquot := (hasDerivAt_const x g).fun_div ((Real.hasDerivAt_sin x).fun_pow 2)
    (pow_ne_zero 2 hs)
  have hterm := (((Real.hasDerivAt_cos x).fun_mul ((Z_deriv hs).sub_const 1)).sub_const (1/12))
  convert hbase.fun_add (hquot.fun_mul hterm) using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [secondDD,Zd,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
    field_simp
    linear_combination (7200*N x^3*g*Real.sin x*(Z x-1))*Real.sin_sq_add_cos_sq x

theorem quarter_lower : (11042/12500:ℝ)<quarterValue := by
  have hN := FrameCoreHighNorm.n_one_bounds.2
  have hN0 : 0≤FrameCoreHighNorm.n 1 := Real.sqrt_nonneg _
  have hRN : R*FrameCoreHighNorm.n 1<radiusUpper*(320451/500000) :=
    mul_lt_mul'' radius_bound hN R_pos.le hN0
  have hd := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [quarterValue,u,v,g,radiusUpper] at hRN ⊢
  linarith

theorem first_quarter : primaryFirst (Real.pi/2)=quarterValue := by
  simp [primaryFirst,quarterValue,FrameCoreHighNorm.n,FrameCoreHighNorm.energy,k]
  ring

theorem second_quarter : primarySecond (Real.pi/2)=quarterValue := by
  simp [primarySecond,quarterValue,N,X,FrameCoreHighNorm.n,FrameCoreHighNorm.energy,k]
  ring

theorem firstD_negative {x : ℝ} (hx : x∈Icc (3/2:ℝ) (Real.pi/2)) : firstD x<0 := by
  have hdom : x∈Icc (3/4:ℝ) (5/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.2]⟩
  have hs := interval_sine hdom
  have ht := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hz := Z_bounds hdom
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤3/2)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤3/2 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc0
  have hcU : Real.cos x<(71/1000:ℝ) := by linarith
  have hZc := mul_le_mul_of_nonneg_right (show Z x-1≤979/1000 by linarith [hz.2]) ht.2.2.1
  have hn : Real.cos x*(Z x-1)-13/12≤(71/1000:ℝ)*(979/1000)-13/12 := by linarith
  have hn0 : Real.cos x*(Z x-1)-13/12≤0 := by linarith
  have hs2 := pow_le_pow_left₀ ht.1 ht.2.1 2
  have hnum0 := mul_nonpos_of_nonneg_of_nonpos (show 0≤g by norm_num [g]) hn0
  have hmul := mul_le_mul_of_nonpos_left hs2 hnum0
  have hdiv : g/(Real.sin x)^2*(Real.cos x*(Z x-1)-13/12)≤
      g*(Real.cos x*(Z x-1)-13/12) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (pow_pos (by linarith [hs] : 0<Real.sin x) 2)).2 (by linarith)
  have hg : g*(Real.cos x*(Z x-1)-13/12)≤g*((71/1000:ℝ)*(979/1000)-13/12) :=
    mul_le_mul_of_nonneg_left hn (by norm_num [g])
  have hgv : g=269343/250000 := rfl
  dsimp only [firstD]
  linarith [ht.2.1]

theorem first_tail_lower {x : ℝ} (hx : x∈Icc (3/2:ℝ) (Real.pi/2)) : gamma<primaryFirst x := by
  have hsin {z : ℝ} (hz : z∈Icc (3/2:ℝ) (Real.pi/2)) : Real.sin z≠0 := by
    have hdom : z∈Icc (3/4:ℝ) (5/2) :=
      ⟨by linarith [hz.1],by linarith [hz.2,Arithmetic.pi_hand_enclosure.2]⟩
    exact (lt_trans (by norm_num) (interval_sine hdom)).ne'
  have hm : AntitoneOn primaryFirst (Icc (3/2:ℝ) (Real.pi/2)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (first_deriv (hsin hz)).continuousAt.continuousWithinAt
    · exact fun z hz => first_deriv (hsin (Ioo_subset_Icc_self hz))
    · exact fun z hz => (firstD_negative (Ioo_subset_Icc_self hz)).le
  have hh := hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2
  rw [first_quarter] at hh
  dsimp [gamma]
  linarith [quarter_lower]

theorem secondDD_negative {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) : secondDD x<0 := by
  have hdom : x∈Icc (3/4:ℝ) (5/2) := ⟨by linarith [hx.1,FrameLowPair.pi_lower],hx.2⟩
  have hs := interval_sine hdom
  have ht := second_signs ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hz := Z_bounds hdom
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (Real.cos x))
    (show 1-Z x≤0 by linarith [hz.1])
  have hn : (1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6≤-(14/25:ℝ) := by
    linarith [ht.2,hz.1]
  have hs3 := pow_le_pow_left₀ ht.1 (Real.sin_le_one x) 3
  have hmul := mul_le_mul_of_nonpos_left hs3 (show g*(-14/25)≤0 by norm_num [g])
  have hdiv : g/(Real.sin x)^3*((1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6)≤g*(-14/25) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos (by linarith [hs] : 0<Real.sin x) 3)).2
    have hh := mul_le_mul_of_nonneg_left hn (show 0≤g by norm_num [g])
    linarith
  have hlast : 0≤R*v^2*g^2*(Real.cos x)^2/((Real.sin x)^4*(N x)^3) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg R_pos.le (sq_nonneg v)) (sq_nonneg g))
        (sq_nonneg _)
    · exact mul_nonneg (pow_nonneg ht.1 4) (pow_nonneg (N_pos x).le 3)
  have hch := CorePairGeometry.charge_upper x
  rw [(second_width ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩).2] at hch
  have hgv : g=269343/250000 := rfl
  dsimp only [secondDD]
  linarith

theorem second_end : (27/25:ℝ)<primarySecond (5/2) := by
  have hsL := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1
  have hcL := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.2
  have hsU0 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsU0
  have hsU : Real.sin (5/2:ℝ)<599/1000 := by linarith
  have hs : 0<Real.sin (5/2:ℝ) := by linarith
  have hgL : g/(599/1000)≤g/Real.sin (5/2:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num [g]) hs (by linarith)
  have hneg := negative_div_lower hcL.le (by norm_num : -(401/500:ℝ)≤0)
    (by norm_num : (0:ℝ)<299/500) hsL.le
  have hcos : (g/12)*(-(401/500)/(299/500))≤(g/12)*Real.cos (5/2)/Real.sin (5/2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hneg (by norm_num [g])
  have hXu : X (5/2)<g/(299/500)-u := by
    dsimp [X]
    exact sub_lt_sub_right (div_lt_div_of_pos_left (by norm_num [g]) (by norm_num) hsL) u
  have hXl := X_lower (show (5/2:ℝ)∈Icc (3/4:ℝ) (5/2) by constructor <;> norm_num)
  have hX0 : 0≤X (5/2) := le_trans (by norm_num [g,u]) hXl
  have hn : N (5/2)<(647/500:ℝ) := by
    have hsq := N_sq (5/2)
    have hX2 := pow_lt_pow_left₀ hXu hX0 (by norm_num : (2:ℕ)≠0)
    refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
    rw [hsq]
    norm_num [g,u,v] at hX2 ⊢
    linarith
  have hRN : R*N (5/2)<radiusUpper*(647/500) :=
    mul_lt_mul'' radius_bound hn R_pos.le (N_pos _).le
  have hch := CorePairGeometry.charge_upper (5/2)
  rw [(second_width (show (5/2:ℝ)∈Icc (Real.pi/2) Real.pi by
    constructor <;> linarith [Arithmetic.pi_hand_enclosure.2,FrameLowPair.pi_lower])).2] at hch
  have hk := k_bounds.2.2
  dsimp only [primarySecond]
  dsimp only [kUpper,radiusUpper,u,v,g] at hk hRN hgL hcos ⊢
  linarith

theorem second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) : gamma<primarySecond x := by
  have hsin {z : ℝ} (hz : z∈Icc (Real.pi/2) (5/2:ℝ)) : Real.sin z≠0 := by
    linarith [interval_sine (show z∈Icc (3/4:ℝ) (5/2) from
      ⟨by linarith [hz.1,FrameLowPair.pi_lower],hz.2⟩)]
  have hc : ConcaveOn ℝ (Icc (Real.pi/2) (5/2:ℝ)) primarySecond := concave_of_deriv2
    (fun z hz => second_deriv (hsin hz)) (fun z hz => secondD_deriv (hsin hz))
    (fun z hz => (secondDD_negative hz).le)
  apply concave_gt_of_endpoints hc hx
  · rw [second_quarter]
    dsimp [gamma]
    linarith [quarter_lower]
  · dsimp [gamma]
    linarith [second_end]

end SquaresInCircles.Eight.FrameCoreHighPrimaryContinuation
end
end
end

section
/-!
## The whole rounded-core target envelope for a high source

The circle cap is kept as an actual radical.  A single decreasing quartic
proves the uniform derivative bound for its radical term; the resulting
cost envelope increases on the whole interval `[2.28,2.5]`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighCorner
open FramePair FrameCircleArc FrameHighArc FramePairCalculus

def z (x : ℝ) : ℝ := Real.sin x+Real.cos x/12
def D (x : ℝ) : ℝ := -Real.cos x+Real.sin x/12
def capK (x : ℝ) : ℝ := 1+z x
def capY (x : ℝ) : ℝ := Real.sqrt (Q0-(capK x)^2)
def J (x : ℝ) : ℝ :=
  x-4119/5000-k+u*(capK x-1/2)-v*(capY x-1/2)
def Jd (x : ℝ) : ℝ := 1-u*D x-v*D x*capK x/capY x
def P (t : ℝ) : ℝ :=
  (123/100)^2*Q0-(145/144+(123/100)^2-t^2)*(1+t)^2

theorem endpoint_trig :
    (379/500:ℝ)<Real.sin (57/25:ℝ) ∧ Real.sin (57/25:ℝ)<759/1000 ∧
      -(163/250:ℝ)<Real.cos (57/25:ℝ) ∧ Real.cos (57/25:ℝ)< -(13/20) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤57/25 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤57/25 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤57/25 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤57/25 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem domain {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    (53/100:ℝ)<z x ∧ z x<71/100 ∧ 0<D x ∧ D x<43/50 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hsL := FrameCoreHighPrimaryContinuation.interval_sine
    (show x∈Icc (3/4:ℝ) (5/2) from ⟨by linarith [hx.1],hx.2⟩)
  have hsin : Real.sin x≤Real.sin (57/25:ℝ) := by
    have hm : AntitoneOn Real.sin (Icc (Real.pi/2) Real.pi) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt
      · exact fun t _ => Real.hasDerivAt_sin t
      · exact fun t ht => (second_signs (Ioo_subset_Icc_self ht)).2
    exact hm ⟨by linarith [Arithmetic.pi_hand_enclosure.2],
      by linarith [FrameLowPair.pi_lower]⟩ hxq hx.1
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hcU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤57/25) hxq.2 hx.1
  have hzL : (53/100:ℝ)<z x := by
    dsimp [z]
    linarith [FrameCoreHighCorePrimary.trig_endpoints.2.2.2.2]
  have hzU : z x<(71/100:ℝ) := by
    dsimp [z]
    linarith [endpoint_trig.2.1,endpoint_trig.2.2.2]
  have hD0 : 0<D x := by dsimp [D]; linarith
  have hid : (D x)^2+(z x)^2=(145/144:ℝ) := by
    dsimp [D,z]
    linear_combination (145/144:ℝ)*(Real.sin_sq_add_cos_sq x)
  refine ⟨hzL,hzU,hD0,?_⟩
  nlinarith

theorem cap_radicand_pos {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    0<Q0-(capK x)^2 := by
  have hz := domain hx
  dsimp [capK]
  norm_num [Q0]
  nlinarith

theorem capY_pos {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : 0<capY x :=
  Real.sqrt_pos.mpr (cap_radicand_pos hx)

theorem capY_sq {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    (capY x)^2=Q0-(capK x)^2 := Real.sq_sqrt (cap_radicand_pos hx).le

theorem P_deriv (t : ℝ) : HasDerivAt P
    (2*(1+t)*(2*t^2+t-145/144-(123/100)^2)) t := by
  have h2 := ((hasDerivAt_id' t).fun_pow 2).const_sub (145/144+(123/100)^2)
  have h3 := ((hasDerivAt_id' t).const_add 1).fun_pow 2
  have h := (h2.fun_mul h3).const_sub ((123/100)^2*Q0)
  convert h using 1
  · rfl
  · norm_num
    ring

theorem P_antitone : AntitoneOn P (Icc (53/100:ℝ) (71/100)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t _ => (P_deriv t).continuousAt.continuousWithinAt
  · exact fun t _ => P_deriv t
  · intro t ht
    have ht0 : 0≤t := by linarith [ht.1]
    have hs := pow_le_pow_left₀ ht0 ht.2.le 2
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · nlinarith

theorem ratio_bound {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    D x*capK x/capY x<(123/100:ℝ) := by
  have hz := domain hx
  have hp := P_antitone ⟨hz.1.le,hz.2.1.le⟩ ⟨by norm_num,le_rfl⟩ hz.2.1.le
  have he : 0<P (71/100) := by norm_num [P,Q0]
  have hp0 : 0<P (z x) := he.trans_le hp
  have hid : (D x)^2+(z x)^2=(145/144:ℝ) := by
    dsimp [D,z]
    linear_combination (145/144:ℝ)*(Real.sin_sq_add_cos_sq x)
  have hy := capY_sq hx
  have hY0 := capY_pos hx
  have hK0 : 0≤capK x := by dsimp [capK]; linarith [hz.1]
  have hsq : (D x*capK x)^2<((123/100)*capY x)^2 := by
    have hid' := congrArg (fun w : ℝ => (1+z x)^2*w) hid
    rw [mul_pow,mul_pow,hy]
    dsimp only [P,capK] at hp0 hid' ⊢
    linarith
  apply (div_lt_iff₀ hY0).2
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

theorem capK_deriv (x : ℝ) : HasDerivAt capK (-D x) x := by
  have h := ((Real.hasDerivAt_sin x).fun_add ((Real.hasDerivAt_cos x).div_const 12)).const_add 1
  convert h using 1
  · rfl
  · simp only [D]; ring

theorem capY_deriv {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) :
    HasDerivAt capY (capK x*D x/capY x) x := by
  have hd := ((capK_deriv x).fun_pow 2).const_sub Q0
  have h := hd.sqrt (cap_radicand_pos hx).ne'
  convert h using 1
  · rfl
  · simp only [capY]
    norm_num
    ring

theorem J_deriv {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : HasDerivAt J (Jd x) x := by
  have hd := ((((hasDerivAt_id' x).sub_const (4119/5000)).sub_const k).fun_add
    (((capK_deriv x).sub_const (1/2)).const_mul u)).fun_sub
    (((capY_deriv hx).sub_const (1/2)).const_mul v)
  convert hd using 1
  · rfl
  · simp only [Jd]; ring

theorem Jd_positive {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : 0<Jd x := by
  have hD := (domain hx).2.2.2
  have hG := ratio_bound hx
  have he : Jd x=1-u*D x-v*(D x*capK x/capY x) := by simp only [Jd]; ring
  rw [he]
  have hDu := mul_lt_mul_of_pos_left hD (show 0<u by norm_num [u])
  have hGv := mul_lt_mul_of_pos_left hG (show 0<v by norm_num [v])
  dsimp only [u,v] at hDu hGv ⊢
  linarith

theorem J_lower {x : ℝ} (hx : x∈Icc (57/25:ℝ) (5/2)) : (99/100:ℝ)<J x := by
  have hm : MonotoneOn J (Icc (57/25:ℝ) (5/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (J_deriv ht).continuousAt.continuousWithinAt
    · exact fun t ht => J_deriv (Ioo_subset_Icc_self ht)
    · exact fun t ht => (Jd_positive (Ioo_subset_Icc_self ht)).le
  have ht0 : (57/25:ℝ)∈Icc (57/25:ℝ) (5/2) := ⟨le_rfl,by norm_num⟩
  have hh := hm ht0 hx hx.1
  have hK : (17/10:ℝ)<capK (57/25) := by
    dsimp [capK,z]
    linarith [endpoint_trig.1,endpoint_trig.2.2.1]
  have hY : capY (57/25)<(507/500:ℝ) := by
    have hy := capY_sq ht0
    have hy0 := capY_pos ht0
    norm_num [Q0] at hy
    nlinarith
  have he : (99/100:ℝ)<J (57/25) := by
    dsimp [J,u,v]
    linarith [k_bounds.2.1]
  exact he.trans_le hh

end SquaresInCircles.Eight.FrameCoreHighCorner
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighHighPrimary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2 g K)
open FrameCoreHighGeometry
open FrameCoreHighPrimaryCurvature (gamma primaryFirst primaryFirst_lower)
open FrameCoreHighPrimaryContinuation (N X primarySecond)
open FrameCoreHighCorner (capK capY)

def CancellationSide (j : Bool) (a B : ℝ) : Prop :=
  j=false ∨ (a=7/12 ∧ B≤1/2)
def G (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-k+(-u+v+g/Real.sin x)/2-R*N x+
    (g/Real.sin x)*pairWidth x+(g/Real.sin x)*(7/12)*Real.cos x

theorem cancellation_target (j : Bool) {a B x : ℝ}
    (hc : CoreState a B) (hside : CancellationSide j a B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (g/Real.sin x)*(7/12)*Real.cos x≤
      -sign j*coreLabel a B+(g/Real.sin x)*a*Real.cos x+
        (g/Real.sin x)*sign j*B*Real.sin x := by
  have hs := FrameCoreHighPrimaryContinuation.interval_sine hx
  have hs0 : 0<Real.sin x := by linarith
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) hs0.le
  have hlamU : g/Real.sin x<2 := (div_lt_iff₀ hs0).2 (by dsimp [g]; linarith)
  have hclam := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hlam0
  have hcan : (g/Real.sin x)*Real.sin x=g := div_mul_cancel₀ _ hs0.ne'
  cases j with
  | false =>
      have ht := positive_support (r := -(g/Real.sin x)*Real.cos x)
        (z := (g/Real.sin x)*Real.sin x) hc
        (by dsimp [K]; nlinarith) (by rw [hcan])
      simp only [sign,Bool.false_eq_true,↓reduceIte]
      linarith
  | true =>
      have ha : a=7/12 := by
        rcases hside with h | h
        · cases h
        · exact h.1
      subst a
      have hcB : g/Real.sin x*Real.sin x*B=g*B := by rw [hcan]
      dsimp [coreLabel,sign]
      linarith

theorem cancellation_support (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hside : CancellationSide j a B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary j b a B x) :
    G x≤highCoreCost i j b a B x := by
  have hs := FrameCoreHighPrimaryContinuation.interval_sine hx
  have hlam0 : 0≤g/Real.sin x := div_nonneg (by norm_num [g]) (by linarith)
  have hscaled := mul_nonneg hlam0 hm
  have hsource := circle_linear_lower (A_circle ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩)
    (u-g/Real.sin x) (-v)
  have hn : Real.sqrt ((u-g/Real.sin x)^2+(-v)^2)=N x := by
    dsimp [N,X]
    congr 1
    ring
  rw [hn] at hsource
  have hsign := FrameHighArc.minus_label_le i hb
  have htarget := cancellation_target j hc hside hx
  dsimp [G,highCoreCost,highCorePrimary,H] at *
  nlinarith

theorem G_lower {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) : gamma<G x := by
  have hs : Real.sin x≠0 := by linarith [FrameCoreHighPrimaryContinuation.interval_sine hx]
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨by linarith [hx.1],hq⟩
    have he : G x=primaryFirst x := by
      dsimp [G,primaryFirst,N,X]
      rw [hw.1,hw.2]
      field_simp [hs]
      ring
    rw [he]
    by_cases hshort : x≤3/2
    · exact primaryFirst_lower ⟨hx.1,hshort⟩
    · exact FrameCoreHighPrimaryContinuation.first_tail_lower ⟨(lt_of_not_ge hshort).le,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hw := second_width hxq
    have he : G x=primarySecond x := by
      dsimp [G,primarySecond]
      rw [hw.1,hw.2]
      field_simp [hs]
      ring
    rw [he]
    exact FrameCoreHighPrimaryContinuation.second_lower ⟨hxq.1,hx.2⟩

theorem rounded_quadrant_false {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤highCorePrimary true b a B x) : False := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have ht := FrameLowPair.quadrant hx
  have hA := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ)≤a by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]) ht.2.2.1
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  dsimp [highCorePrimary,sign] at hm
  rw [hw] at hm
  nlinarith

theorem rounded_cap {b a B x : ℝ}
    (hc : CoreState a B) (hB : 1/2≤B) (hx : x∈Icc (Real.pi/2) Real.pi)
    (hm : 0≤highCorePrimary true b a B x) : capK x≤A b+1/2 := by
  have hcore := core_bounds hc
  have ht := second_signs hx
  have hA := mul_le_mul_of_nonpos_right hcore.2.1 ht.2
  have hB' := mul_le_mul_of_nonneg_right hB ht.1
  dsimp [highCorePrimary,sign] at hm
  rw [(second_width hx).1] at hm
  dsimp [capK,FrameCoreHighCorner.z]
  nlinarith

theorem rounded_cut {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    (57/25:ℝ)<x := by
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · exact rounded_quadrant_false hb hc hB ⟨by linarith [hx.1],hfirst⟩ hm
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hcap := rounded_cap hc hB hxq hm
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (57/25:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (57/25:ℝ) from ⟨hxq.1,hsmall⟩)
      (by rw [Real.sin_pi_div_two]; norm_num : (379/500:ℝ)<Real.sin (Real.pi/2))
      FrameCoreHighCorner.endpoint_trig.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have ha := (high_bounds hb).2.2.2
    dsimp [capK,FrameCoreHighCorner.z] at hcap
    linarith [FrameCoreHighCorner.endpoint_trig.2.2.1]

theorem rounded_tangent_cap {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (57/25:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    b≤capY x-1/2 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcap := rounded_cap hc hB hxq hm
  have hz := FrameCoreHighCorner.domain hx
  have hy := FrameCoreHighCorner.capY_pos hx
  have hs := FrameCoreHighCorner.capY_sq hx
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hb.1,hb.2⟩
  have hK0 : 0≤capK x := by dsimp [capK]; linarith [hz.1]
  have hA := pow_le_pow_left₀ hK0 hcap 2
  have hbp : 0≤b+1/2 := by linarith [(high_bounds hb).1]
  nlinarith

theorem rounded_primary (i : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hB : 1/2≤B)
    (hx : x∈Icc (3/4:ℝ) (5/2)) (hm : 0≤highCorePrimary true b a B x) :
    gamma<highCoreCost i true b a B x := by
  have hcut := rounded_cut hb hc hB hx hm
  have hdom : x∈Icc (57/25:ℝ) (5/2) := ⟨hcut.le,hx.2⟩
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hcut,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcapA := rounded_cap hc hB hxq hm
  have hcapB := rounded_tangent_cap hb hc hB hdom hm
  have hA := mul_le_mul_of_nonneg_left hcapA (show 0≤u by norm_num [u])
  have hB' := mul_le_mul_of_nonneg_left hcapB (show 0≤v by norm_num [v])
  have hsource := FrameHighArc.minus_label_le i hb
  have htarget := (label_bounds hc).2
  have hch := CorePairGeometry.charge_upper x
  have hscalar := FrameCoreHighCorner.J_lower hdom
  dsimp [highCoreCost,FrameCoreHighCorner.J,H,sign,gamma] at *
  nlinarith

theorem high_primary (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hpositive : j=true → -(13/500:ℝ)≤x)
    (hm : 0≤highCorePrimary j b a B x) :
    (8833/10000:ℝ)<highCoreCost i j b a B x := by
  have hcut := high_primary_angle j hb hc hx.1 hpositive hm
  have hdom : x∈Icc (3/4:ℝ) (5/2) := ⟨hcut.le,hx.2⟩
  change gamma<highCoreCost i j b a B x
  cases j with
  | false => exact (G_lower hdom).trans_le (cancellation_support i false hb hc (Or.inl rfl) hdom hm)
  | true =>
      by_cases hB : B<1/2
      · have ha := (label_side hc hB).1
        exact (G_lower hdom).trans_le (cancellation_support i true hb hc (Or.inr ⟨ha,hB.le⟩) hdom hm)
      · exact rounded_primary i hb hc (le_of_not_gt hB) hdom hm

end SquaresInCircles.Eight.FrameCoreHighHighPrimary
end
end
end
