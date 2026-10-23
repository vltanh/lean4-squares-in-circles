module

public import SquaresInCircles.Eight.TableFree.ZeroPrimaryMarkers
public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# One complete scalar bound for the original zero-owner signs

Uncompiled source.  The norm is strictly convex on the entire allowed
angle interval, so the original boosted charge is concave.  Two exact
Taylor and positive-square endpoint comparisons give its strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalZeroSign

abbrev K : ℝ := 18721/10000
abbrev M : ℝ := 222/125
def norm (d : ℝ) : ℝ := Real.sqrt (K-M*Real.cos d)
def normD (d : ℝ) : ℝ := M*Real.sin d/(2*norm d)
def normDD (d : ℝ) : ℝ :=
  M*(2*K*Real.cos d-M*(1+(Real.cos d)^2))/(4*(norm d)^3)
def scalar (d : ℝ) : ℝ :=
  d+13/200+(6/5)*(Real.sin d+Real.cos d)-CommonQuarter.radius*norm d
def scalarD (d : ℝ) : ℝ :=
  1+(6/5)*(Real.cos d-Real.sin d)-CommonQuarter.radius*normD d
def scalarDD (d : ℝ) : ℝ :=
  -(6/5)*(Real.sin d+Real.cos d)-CommonQuarter.radius*normDD d

theorem radicand_positive (d : ℝ) : 0<K-M*Real.cos d := by
  have hh := Real.cos_le_one d
  dsimp [K,M]
  linarith

theorem norm_positive (d : ℝ) : 0<norm d := Real.sqrt_pos.mpr (radicand_positive d)

theorem norm_sq (d : ℝ) : (norm d)^2=K-M*Real.cos d :=
  Real.sq_sqrt (radicand_positive d).le

theorem norm_derivative (d : ℝ) : HasDerivAt norm (normD d) d := by
  have hh := ((hasDerivAt_const d K).sub ((Real.hasDerivAt_cos d).const_mul M)).sqrt
    (radicand_positive d).ne'
  convert hh using 1
  · rfl
  · dsimp [normD,norm]
    ring

theorem norm_second_derivative (d : ℝ) : HasDerivAt normD (normDD d) d := by
  have hn := (norm_positive d).ne'
  have hh := ((Real.hasDerivAt_sin d).const_mul M).div
    ((norm_derivative d).const_mul 2) (by positivity : 2*norm d≠0)
  convert hh using 1
  · rfl
  · dsimp [normD,normDD]
    field_simp [hn]
    nlinarith [congrArg (fun x : ℝ => 2*M*Real.cos d*x) (norm_sq d),
      congrArg (fun x : ℝ => M^2*x) (Real.sin_sq_add_cos_sq d)]

theorem norm_second_nonneg {d : ℝ} (hd : d∈Icc 0 frameCap) : 0≤normDD d := by
  have ht := transport_trig hd
  have hc : 3/4≤Real.cos d := by linarith [ht.1]
  have hf : 0≤2*K-M*(Real.cos d+3/4) := by
    dsimp [K,M]
    linarith [ht.2.1]
  have hp := mul_nonneg (sub_nonneg.mpr hc) hf
  have hnum : 0<2*K*Real.cos d-M*(1+(Real.cos d)^2) := by
    dsimp [K,M] at hp ⊢
    nlinarith only [hp]
  dsimp [normDD]
  exact div_nonneg (mul_nonneg (by norm_num [M]) hnum.le)
    (by positivity)

theorem scalar_derivative (d : ℝ) : HasDerivAt scalar (scalarD d) d := by
  convert (((hasDerivAt_id d).add_const (13/200)).add
    (((Real.hasDerivAt_sin d).add (Real.hasDerivAt_cos d)).const_mul (6/5))).sub
      ((norm_derivative d).const_mul CommonQuarter.radius) using 1
  · rfl
  · dsimp [scalarD]
    ring

theorem scalar_second_derivative (d : ℝ) : HasDerivAt scalarD (scalarDD d) d := by
  convert ((hasDerivAt_const d 1).add
    (((Real.hasDerivAt_cos d).sub (Real.hasDerivAt_sin d)).const_mul (6/5))).sub
      ((norm_second_derivative d).const_mul CommonQuarter.radius) using 1
  · rfl
  · dsimp [scalarDD]
    ring

theorem scalar_concave : ConcaveOn ℝ (Icc (29/100:ℝ) frameCap) scalar := by
  apply concave_of_deriv2 (fun d _ => scalar_derivative d)
    (fun d _ => scalar_second_derivative d)
  intro d hd
  have hd' : d∈Icc 0 frameCap := ⟨by linarith [hd.1],hd.2⟩
  have ht := transport_trig hd'
  have hn := norm_second_nonneg hd'
  have hR : 0≤CommonQuarter.radius := Real.sqrt_nonneg Q0
  have hp := mul_nonneg hR hn
  dsimp [scalarDD]
  linarith [ht.1,ht.2.2.1]

theorem scalar_left : (1:ℝ)<scalar (29/100) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x:=(29/100:ℝ))
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤29/100 by norm_num)
  have hc' : (191/200:ℝ)≤Real.cos (29/100) := by norm_num at hc; linarith
  have hs' : (57/200:ℝ)≤Real.sin (29/100) := by norm_num at hs; linarith
  have hn : norm (29/100)<21/50 := by
    have he := norm_sq (29/100)
    dsimp [K,M] at he
    nlinarith [norm_positive (29/100)]
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hp := (mul_lt_mul_of_pos_left hn hR).trans
    (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2 (by norm_num : (0:ℝ)<21/50))
  dsimp [scalar]
  nlinarith only [hc',hs',hp]

theorem scalar_right : (1:ℝ)<scalar frameCap := by
  have hc := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
  have hs := Real.sin_ge_sub_cube (show 0≤frameCap by norm_num [frameCap])
  have hc' : (19/25:ℝ)≤Real.cos frameCap := by norm_num [frameCap] at hc ⊢; linarith
  have hs' : (16/25:ℝ)≤Real.sin frameCap := by norm_num [frameCap] at hs ⊢; linarith
  have hn : norm frameCap<723/1000 := by
    have he := norm_sq frameCap
    dsimp [K,M] at he
    nlinarith [norm_positive frameCap]
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hp := (mul_lt_mul_of_pos_left hn hR).trans
    (mul_lt_mul_of_pos_right CommonQuarter.radius_bounds.2
      (by norm_num : (0:ℝ)<723/1000))
  dsimp [scalar,frameCap]
  nlinarith only [hc',hs',hp]

theorem scalar_gt_one {d : ℝ} (hd : d∈Icc (29/100:ℝ) frameCap) : 1<scalar d :=
  concave_gt_of_endpoints scalar_concave hd scalar_left scalar_right

end SquaresInCircles.Eight.TableFree.GlobalZeroSign
