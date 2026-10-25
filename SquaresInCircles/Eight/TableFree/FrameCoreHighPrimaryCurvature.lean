module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighNorm

/-!
# The whole initial core/high primary interval by curvature

The actual trigonometric support is positive on `[3/4,3/2]`.
A sixth-derivative bound proves that its second derivative is concave;
one tangent then gives a uniform upper curvature bound.  The endpoint
chord has a strict rational reserve on the entire original interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighPrimaryCurvature
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

end SquaresInCircles.Eight.TableFree.FrameCoreHighPrimaryCurvature
