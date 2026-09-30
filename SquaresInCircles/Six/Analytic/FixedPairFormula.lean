module
public import SquaresInCircles.Six.Analytic.FixedPair

@[expose] public section

/-!
# Exact smooth formulas on the geometric sign sectors

The only walls are n=0, w=0 and n=w. The displayed root arguments are the
squared norms of the actual fixed-pair forces. This is a symbolic identity,
not a cap-branch assumption or a numerical subdivision.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

def sign (p : Bool) : ℝ := if p then 1 else -1
def positivePart (p : Bool) : ℝ := if p then 1 else 0
def HasSign (p : Bool) (x : ℝ) : Prop := if p then 0≤x else x≤0

def Sector (pn pw pq : Bool) (n w : ℝ) : Prop :=
  HasSign pn n ∧ HasSign pw w ∧ HasSign pq (n-w)

lemma domain_bounds {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    -3/10≤n ∧ n≤5/12 ∧ -11/25≤w ∧ w≤2/5 ∧
      -7/10≤n-w ∧ n-w≤6/7 := by
  cases no <;> cases wo <;> simp only [Domain,Bool.false_eq_true,if_false,if_true] at h
  all_goals rcases h with ⟨hn,hw⟩
  all_goals repeat' constructor
  all_goals linarith [hn.1,hn.2,hw.1,hw.2]

lemma domain_cos_pos {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    0<Real.cos n ∧ 0<Real.cos w ∧ 0<Real.cos (n-w) := by
  rcases domain_bounds h with ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩
  refine ⟨?_,?_,?_⟩
  all_goals apply Real.cos_pos_of_mem_Ioo
  all_goals constructor <;> linarith [Real.pi_gt_d2]

lemma sign_sin {p : Bool} {x : ℝ} (hp : HasSign p x) (hx : |x|≤Real.pi) :
    |Real.sin x|=sign p*Real.sin x ∧ max (Real.sin x) 0=positivePart p*Real.sin x := by
  cases p
  · have ht : x≤0 := hp
    have hs : Real.sin x≤0 := by
      have hn := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-x by linarith)
        (by have h := abs_le.mp hx; linarith [h.1])
      rw [Real.sin_neg] at hn
      linarith
    simp [sign,positivePart,abs_of_nonpos hs,max_eq_right hs]
  · have ht : 0≤x := hp
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht ((le_abs_self x).trans hx)
    simp [sign,positivePart,abs_of_nonneg hs,max_eq_left hs]

def northSq (no : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  if no then
    ![1+rStar^2-2*rStar*Real.sin (n-w),
      1+rStar^2+2*rStar*Real.cos (n-w),(1+rStar)^2,1+rStar^2] u
  else
    ![1+rStar^2+2*rStar*Real.sin w,
      1+rStar^2+2*rStar*Real.cos w,1+rStar^2+2*rStar*Real.cos n,
      1+rStar^2+2*rStar*Real.sin n] u

def westSq (wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  if wo then
    ![(1+rStar)^2+mStar^2,1+(mStar-rStar)^2,
      1+rStar^2+mStar^2-2*rStar*Real.sin (n-w)-2*rStar*mStar*Real.cos (n-w),
      1+rStar^2+mStar^2+2*rStar*Real.cos (n-w)-2*rStar*mStar*Real.sin (n-w)] u
  else
    ![1+rStar^2+mStar^2+2*rStar*Real.cos w+2*mStar*Real.sin w,
      1+(mStar-rStar)^2+2*(mStar-rStar)*Real.sin w,
      1+rStar^2+mStar^2-2*rStar*Real.sin n+2*mStar*Real.sin w-
        2*rStar*mStar*Real.cos (n-w),
      1+rStar^2+mStar^2+2*rStar*Real.cos n+2*mStar*Real.sin w-
        2*rStar*mStar*Real.sin (n-w)] u

private lemma sin_sq_replace (x : ℝ) : Real.sin x^2=1-Real.cos x^2 := by
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma northSq_eq_norm (no : Bool) (u : Fin 4) (n w : ℝ) :
    northSq no u n w=(northForce no u n w).1^2+(northForce no u n w).2^2 := by
  cases no <;> fin_cases u
  all_goals norm_num [northSq,northForce,pairNorthBase,pairNorthSource]
  all_goals simp only [Real.sin_sub,Real.cos_sub]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace n,sin_sq_replace w]
  all_goals ring

lemma westSq_eq_norm (wo : Bool) (u : Fin 4) (n w : ℝ) :
    westSq wo u n w=(westForce wo u n w).1^2+(westForce wo u n w).2^2 := by
  cases wo <;> fin_cases u
  all_goals norm_num [westSq,westForce,pairWestBase,pairWestSource]
  all_goals simp only [Real.sin_sub,Real.cos_sub]
  all_goals ring_nf
  all_goals simp only [sin_sq_replace n,sin_sq_replace w]
  all_goals ring

def constant (no wo : Bool) (u : Fin 4) : ℝ :=
  1+mStar+(if wo then 1/2 else 0)-(if no then cStar else 0)+
    (if u=0 ∨ u=3 then rStar+(if no then 1/2 else 0)
     else if u=1 then 0 else rStar/2)

def northCosCoeff (no : Bool) (u : Fin 4) : ℝ :=
  if no then 1/2+cStar else if u=0 ∨ u=3 then 1 else 1/2

def northSinCoeff (no : Bool) (u : Fin 4) (pn : Bool) : ℝ :=
  sign pn/2+(if no then -cStar*positivePart pn else if u=0 ∨ u=3 then 1/2 else 0)

def westCosCoeff (wo : Bool) : ℝ := if wo then 1/2 else 1

def westSinCoeff (wo pw : Bool) : ℝ :=
  sign pw/2+(if wo then -cStar*positivePart pw else 1/2)

def differenceCosCoeff (u : Fin 4) : ℝ :=
  if u=0 ∨ u=3 then rStar else if u=1 then rStar/2 else 0

def differenceSinCoeff (u : Fin 4) (pq : Bool) : ℝ :=
  if u=1 then rStar*sign pq/2 else rStar*(sign pq-1)/2

def northTrig (no : Bool) (u : Fin 4) (pn : Bool) (n : ℝ) : ℝ :=
  northCosCoeff no u*Real.cos n+northSinCoeff no u pn*Real.sin n

def westTrig (wo pw : Bool) (w : ℝ) : ℝ :=
  westCosCoeff wo*Real.cos w+westSinCoeff wo pw*Real.sin w

def differenceTrig (u : Fin 4) (pq : Bool) (q : ℝ) : ℝ :=
  differenceCosCoeff u*Real.cos q+differenceSinCoeff u pq*Real.sin q

def formula (no wo : Bool) (u : Fin 4) (pn pw pq : Bool) (n w : ℝ) : ℝ :=
  constant no wo u+northTrig no u pn n+westTrig wo pw w+differenceTrig u pq (n-w)-
    northRadius u*Real.sqrt (northSq no u n w)-Six.radius*Real.sqrt (westSq wo u n w)

/-- Exact sector formula, valid across either genuine center-support branch. -/
theorem minorant_eq_formula {no wo : Bool} {u : Fin 4} {pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    minorant no wo u n w=formula no wo u pn pw pq n w := by
  have hc := domain_cos_pos hd
  rcases domain_bounds hd with ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩
  have hN := sign_sin hs.1 (show |n|≤Real.pi by
    apply abs_le.mpr; constructor <;> linarith [Real.pi_gt_d2])
  have hW := sign_sin hs.2.1 (show |w|≤Real.pi by
    apply abs_le.mpr; constructor <;> linarith [Real.pi_gt_d2])
  have hQ := sign_sin hs.2.2 (show |n-w|≤Real.pi by
    apply abs_le.mpr; constructor <;> linarith [Real.pi_gt_d2])
  unfold minorant threshold northUpper northVertex penalty formula
  rw [← northSq_eq_norm,← westSq_eq_norm]
  simp only [angularWidth,abs_of_pos hc.1,abs_of_pos hc.2.1,abs_of_pos hc.2.2,
    hN.1,hN.2,hW.1,hW.2,hQ.1]
  cases no <;> cases wo <;> fin_cases u
  all_goals simp [northForce,westForce,pairNorthBase,pairWestBase,pairNorthSource,pairWestSource,
    constant,northTrig,westTrig,differenceTrig,northCosCoeff,northSinCoeff,
    westCosCoeff,westSinCoeff,differenceCosCoeff,differenceSinCoeff,northRadius]
  all_goals ring

end SquaresInCircles.Six.Analytic.FixedPair
