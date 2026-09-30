module
public import SquaresInCircles.Six.Analytic.HighDiagonalAffineTransverse

@[expose] public section

/-!
# A tangent profile that retains the shared central coordinates

The rational box constant 5641/50000 is an upper bound on c0. The OWN
constraint on D gives a lower radial profile. The far-corner circle then
bounds not only |bD|, but |bD| + 2 times every increase above that profile.
This is a whole-interval concavity argument with the two physical endpoints
1/2 and pi/4. No grid or external arithmetic result is a proof premise.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def coreCeiling : ℝ := 5641/50000

def diagonalBase (d : ℝ) : ℝ := 1/2+(19359/50000)*(Real.cos d+Real.sin d)

def diagonalBudget (d : ℝ) : ℝ := 773/2500-(17/100)*d

lemma rho0_lt_five_digit : rho0 < 55641/50000 := by
  have h := Real.sqrt_lt_sqrt
    (show 0 ≤ Q0-1/4 by norm_num [Q0])
    (show Q0-1/4 < ((80641:ℝ)/50000)^2 by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at h
  dsimp [rho0]
  linarith

lemma c0_lt_coreCeiling : c0 < coreCeiling := by
  dsimp [c0,coreCeiling]
  linarith [rho0_lt_five_digit]

private def profileCircle (d : ℝ) : ℝ :=
  1+(19359/50000)^2-Q0+
    2*(19359/50000)*(Real.cos d+Real.sin d)+
    (19359/50000)^2*Real.sin (2*d)+(2023/2500-(17/100)*d)^2

private lemma profileCircle_identity (d : ℝ) :
    profileCircle d=(diagonalBase d+1/2)^2+(diagonalBudget d+1/2)^2-Q0 := by
  dsimp [profileCircle,diagonalBase,diagonalBudget]
  rw [Real.sin_two_mul]
  nlinarith only [Real.sin_sq_add_cos_sq d]

private lemma profileCircle_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) profileCircle := by
  let f' : ℝ → ℝ := fun x =>
    2*(19359/50000)*(Real.cos x-Real.sin x)+
    2*(19359/50000)^2*Real.cos (2*x)-2*(17/100)*(2023/2500-(17/100)*x)
  let f'' : ℝ → ℝ := fun x =>
    -2*(19359/50000)*(Real.sin x+Real.cos x)-
    4*(19359/50000)^2*Real.sin (2*x)+2*(17/100)^2
  have hf (x : ℝ) : HasDerivAt profileCircle (f' x) x := by
    have htr := ((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul
      (2*(19359/50000))
    have htwo := (((hasDerivAt_id x).const_mul 2).sin).const_mul ((19359/50000)^2)
    have hsq := ((hasDerivAt_const x (2023/2500)).sub
      ((hasDerivAt_id x).const_mul (17/100))).pow 2
    convert ((htr.const_add (1+(19359/50000)^2-Q0)).add htwo).add hsq using 1 <;>
      dsimp [profileCircle,f'] <;> ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have htr := ((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul
      (2*(19359/50000))
    have htwo := (((hasDerivAt_id x).const_mul 2).cos).const_mul (2*(19359/50000)^2)
    have hlin := ((hasDerivAt_const x (2023/2500)).sub
      ((hasDerivAt_id x).const_mul (17/100))).const_mul (-2*(17/100))
    convert (htr.add htwo).add hlin using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (Real.pi/4))
    (f' := f') (f'' := f'') (by dsimp [profileCircle]; fun_prop)
  · intro x _; exact (hf x).hasDerivWithinAt
  · intro x _; exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [h.1,h.2,Real.pi_pos])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [h.1]) (by linarith [h.2,Real.pi_pos])
    have hs2 := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ 2*x by linarith [h.1]) (show 2*x ≤ Real.pi by linarith [h.2,Real.pi_pos])
    have hw := one_le_abs_cos_add_abs_sin x
    rw [abs_of_nonneg hc,abs_of_nonneg hs] at hw
    dsimp [f'']
    linarith

private lemma profileCircle_left : 0 < profileCircle (1/2) := by
  have hc := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hs := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  let L : ℝ := 1+(19359/50000)*
    ((1-(1/2)^2/2+(1/2)^4/24-(1/2)^6/720)+
      ((1/2)-(1/2)^3/6+(1/2)^5/120-(1/2)^7/5040))
  have hL0 : 0 < L := by norm_num [L]
  have hL : L ≤ diagonalBase (1/2)+1/2 := by
    dsimp [L,diagonalBase]
    nlinarith only [hc,hs]
  have hp := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ diagonalBase (1/2)+1/2+L by linarith)
  rw [profileCircle_identity]
  norm_num [L,diagonalBudget,Q0] at hp ⊢
  nlinarith only [hp]

private lemma profileCircle_right : 0 < profileCircle (Real.pi/4) := by
  have hroot : (1414213:ℝ)/1000000 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hpi : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  let L : ℝ := 1+(19359/50000)*(1414213/1000000)
  let T : ℝ := 2023/2500-(17/100)*(11/14)
  have hL0 : 0 < L := by norm_num [L]
  have hT0 : 0 < T := by norm_num [T]
  have hL : L ≤ diagonalBase (Real.pi/4)+1/2 := by
    dsimp [L,diagonalBase]
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    linarith
  have hT : T ≤ diagonalBudget (Real.pi/4)+1/2 := by
    dsimp [T,diagonalBudget]
    linarith
  have hLs := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ diagonalBase (Real.pi/4)+1/2+L by linarith)
  have hTs := mul_nonneg (sub_nonneg.mpr hT)
    (show 0 ≤ diagonalBudget (Real.pi/4)+1/2+T by linarith)
  rw [profileCircle_identity]
  norm_num [L,T,Q0] at hLs hTs ⊢
  nlinarith only [hLs,hTs]

lemma diagonal_profile_circle {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    Q0 < (diagonalBase d+1/2)^2+(diagonalBudget d+1/2)^2 := by
  have h := positive_on_concave_interval profileCircle_concave hd
    profileCircle_left profileCircle_right
  rw [profileCircle_identity] at h
  linarith

lemma diagonal_base_bounds {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    1 ≤ diagonalBase d ∧ diagonalBase d ≤ 21/20 := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hmono := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2)
  have hsin := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hlow : 4/3 ≤ Real.cos d+Real.sin d := by linarith
  have hu : Real.cos d+Real.sin d ≤ 71/50 := by
    nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.cos d-Real.sin d)]
  dsimp [diagonalBase]
  constructor <;> linarith

/-- The coefficient 2 is a valid one-sided support slope on the full high-D
profile. Increasing the radial coordinate must decrease |b| by at least twice
as much. The coefficient is justified by the far-corner circle below. -/
theorem diagonal_tangent_budget {a b d : ℝ} (hc : ContainedChart a |b|)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (ha : diagonalBase d ≤ a) :
    |b|+2*(a-diagonalBase d) < diagonalBudget d := by
  let z := a-diagonalBase d
  have hz0 : 0 ≤ z := sub_nonneg.mpr ha
  have hz1 : z ≤ 1/4 := by
    dsimp [z]
    linarith [hc.a_le_rho0,rho0_lt_five_digit,(diagonal_base_bounds hd).1]
  have hT0 : 0 ≤ diagonalBudget d+1/2-2*z := by
    dsimp [diagonalBudget]
    linarith [hd.2,Real.pi_lt_d2]
  have hcoef : 0 ≤ (diagonalBase d+1/2)-2*(diagonalBudget d+1/2) := by
    have hbase := (diagonal_base_bounds hd).1
    dsimp [diagonalBudget]
    linarith [hd.1]
  by_contra! hb
  have hB : diagonalBudget d+1/2-2*z ≤ |b|+1/2 := by dsimp [z]; linarith
  have hBs := mul_nonneg (sub_nonneg.mpr hB)
    (show 0 ≤ |b|+1/2+(diagonalBudget d+1/2-2*z) by linarith [abs_nonneg b])
  have hcross := mul_nonneg hz0 hcoef
  have hA : a=diagonalBase d+z := by dsimp [z]; ring
  have hcircle := diagonal_profile_circle hd
  rw [hA] at hc
  nlinarith [hc.containment,sq_nonneg z]

/-- OWN supplies the radial profile with its actual shared-center excess. -/
lemma own_diagonal_profile {a b cx cy d : ℝ}
    (hx : cx ≤ coreCeiling) (hy : cy ≤ coreCeiling)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hown : 0 ≤ centralMargin .own (Real.pi+d) a b cx cy) :
    diagonalBase d+(coreCeiling-cx)*Real.cos d+(coreCeiling-cy)*Real.sin d ≤ a := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at hown
  dsimp [diagonalBase,coreCeiling]
  nlinarith only [hown]

/-- The shared center cannot be optimized independently for D and a wing. -/
theorem diagonal_shared_center_budget {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx ≤ coreCeiling) (hy : cy ≤ coreCeiling)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hown : 0 ≤ centralMargin .own (Real.pi+d) a b cx cy) :
    |b|+2*(coreCeiling-cx)*Real.cos d+2*(coreCeiling-cy)*Real.sin d < diagonalBudget d := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hX := mul_nonneg (sub_nonneg.mpr hx) hcos
  have hY := mul_nonneg (sub_nonneg.mpr hy) hsin
  have ha := own_diagonal_profile hx hy hd hown
  have hb := diagonal_tangent_budget hc hd (by linarith)
  linarith

lemma normalized_diagonal_shared_center_budget {R : ℝ} (P : NormalizedPacking R) :
    |P.transverse 3|+2*(coreCeiling-P.center.1)*Real.cos P.diagonalAngle+
      2*(coreCeiling-P.center.2)*Real.sin P.diagonalAngle < diagonalBudget P.diagonalAngle := by
  have hphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  exact diagonal_shared_center_budget (P.contained 3)
    (P.box.1.2.trans c0_lt_coreCeiling.le) (P.box.2.2.trans c0_lt_coreCeiling.le)
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
    (by simpa only [hphase] using P.own_separator 3 P.diagonal_own)

end SquaresInCircles.Six.Analytic
