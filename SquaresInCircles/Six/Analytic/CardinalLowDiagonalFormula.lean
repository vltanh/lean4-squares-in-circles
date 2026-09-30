import SquaresInCircles.Six.Analytic.RotatingTrigConcavity
import SquaresInCircles.Six.Analytic.LowDiagonalEndpoints

/-!
# Cardinal-W low-diagonal stress components

The two choices are the actual forward W-secondary and D-secondary axes.
The weights are (35,40,25)/100 and (43,30,27)/100 on C-D,C-W,W-D.
Universal signed vertex support gives the expressions below. In the D-sourced
case its constant force length is bounded by 5078/10000 by squaring.
The only nonsmooth wall is w=0; the order wall d=w is retained in the domain.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def cardLowAlpha (ds : Bool) : ℝ := if ds then 43/100 else 35/100
def cardLowBeta (ds : Bool) : ℝ := if ds then 30/100 else 40/100
def cardLowMu (ds : Bool) : ℝ := if ds then 27/100 else 25/100

def cardLowC (ds : Bool) : ℝ :=
  1-(613/1000)*cardLowBeta ds-(if ds then (1689/1000)*(5078/10000) else 0)

def cardLowF (ds positive : Bool) (w : ℝ) : ℝ :=
  cardLowBeta ds*Real.cos w+(if positive then cardLowBeta ds*Real.sin w else 0)+
    (if ds then 0 else sineRoot (1689/1000) (40/100) (25/100) w)

def cardLowG (ds : Bool) (d : ℝ) : ℝ :=
  cardLowAlpha ds*(387/1000)*(Real.cos d+Real.sin d)+
    (if ds then sineRoot (1689/1000) (30/100) (27/100) d else 0)

def cardLowH (ds : Bool) (q : ℝ) : ℝ :=
  cardLowMu ds*(Real.cos q+Real.sin q)+
    (if ds then 0 else sineRoot (1689/1000) (35/100) (25/100) q)

def cardLowSmooth (ds positive : Bool) (w d : ℝ) : ℝ :=
  cardLowC ds+cardLowF ds positive w+cardLowG ds d+cardLowH ds (d-w)

def cardLowGap (ds : Bool) (w d : ℝ) : ℝ :=
  if 0≤w then cardLowSmooth ds true w d else cardLowSmooth ds false w d

lemma cardLowSmooth_zero_sign (ds : Bool) (d : ℝ) :
    cardLowSmooth ds true 0 d=cardLowSmooth ds false 0 d := by
  simp [cardLowSmooth,cardLowF]

lemma cardLow_trig {x : ℝ} (hx : 0≤x ∧ x≤9/10) :
    0≤Real.cos x ∧ 0≤Real.sin x ∧ 1≤Real.cos x+Real.sin x := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_nonneg hc,abs_of_nonneg hs] at hw
  exact ⟨hc,hs,hw⟩

lemma cardLow_cos_lower {w : ℝ} (hw : -2/5≤w ∧ w≤2/5) : 23/25≤Real.cos w := by
  have hs := mul_nonneg (show 0≤2/5-w by linarith [hw.2])
    (show 0≤2/5+w by linarith [hw.1])
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := w)]

lemma cardLowF_concave (ds positive : Bool) {l u : ℝ}
    (hl : -2/5≤l) (hu : u≤2/5) (hpos : positive=true → 0≤l) :
    ConcaveOn ℝ (Set.Icc l u) (cardLowF ds positive) := by
  have htrig (x : ℝ) (hx : x∈Set.Icc l u) :
      (13:ℝ)/50≤cardLowBeta ds*Real.cos x+(if positive then cardLowBeta ds*Real.sin x else 0) := by
    have hc := cardLow_cos_lower ⟨hl.trans hx.1,hx.2.trans hu⟩
    cases positive
    · cases ds <;> dsimp [cardLowBeta] <;> linarith
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi
        ((hpos rfl).trans hx.1) (by linarith [hx.2,Real.pi_gt_d2])
      cases ds <;> dsimp [cardLowBeta] <;> linarith
  cases ds
  · have h := rotating_trig_concave
      (C := 0) (A := (40:ℝ)/100) (B := if positive then 40/100 else 0)
      (G := 0) (H := 0) (c := 0) (R := (1689:ℝ)/1000)
      (p := (40:ℝ)/100) (q := (25:ℝ)/100) (L := (13:ℝ)/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun x hx => by cases positive <;> simpa [cardLowBeta] using htrig x hx)
    apply h.congr
    intro x _
    cases positive <;> dsimp [cardLowF,cardLowBeta] <;> ring
  · have h := trig_sum_concave_of_nonnegative
      (C := 0) (A := (30:ℝ)/100) (B := if positive then 30/100 else 0)
      (G := 0) (H := 0) (c := 0)
      (fun x hx => by
        have hh := htrig x hx
        cases positive <;> dsimp [cardLowBeta] at hh ⊢ <;> linarith)
    apply h.congr
    intro x _
    cases positive <;> dsimp [cardLowF,cardLowBeta] <;> ring

lemma cardLowH_concave (ds : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (9/10)) (cardLowH ds) := by
  cases ds
  · have h := rotating_trig_concave
      (C := 0) (A := (25:ℝ)/100) (B := (25:ℝ)/100)
      (G := 0) (H := 0) (c := 0) (R := (1689:ℝ)/1000)
      (p := (35:ℝ)/100) (q := (25:ℝ)/100) (L := (1:ℝ)/4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun x hx => by have hw := (cardLow_trig hx).2.2; nlinarith)
    apply h.congr
    intro x _
    dsimp [cardLowH,cardLowMu]
    ring
  · have h := positive_trig_affine_concave
      (A := (27:ℝ)/100) (B := (27:ℝ)/100) (l := 0) (u := (9:ℝ)/10) (a := 1) (b := 0)
      (by norm_num) (by norm_num)
      (by intro x hx; constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
    apply h.congr
    intro x _
    dsimp [cardLowH,cardLowMu]
    ring

lemma cardLowG_false_concave {l u : ℝ} (hl : 0≤l) (hu : u≤1/2) :
    ConcaveOn ℝ (Set.Icc l u) (cardLowG false) := by
  have h := positive_trig_affine_concave
    (A := (35:ℝ)/100*(387/1000)) (B := (35:ℝ)/100*(387/1000))
    (l := l) (u := u) (a := 1) (b := 0) (by norm_num) (by norm_num)
    (by intro x hx; constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
  apply h.congr
  intro x _
  dsimp [cardLowG,cardLowAlpha]
  ring

end SquaresInCircles.Six.Analytic
