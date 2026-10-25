module

public import SquaresInCircles.Eight.Words.Second.Mixed.AffineScalars

/-!
# Eight squares: every original owner for the common negative mixed pair

The two label rows share an affine lower cost.  Each original weak
axis gives its own global comparison on the lower quarter interval.
The upper interval is paid directly by the core-coordinate bound.
No coordinate of either original square is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedAffine
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

def value (g d b B φ : ℝ) : ℝ := φ-d-g*b+(7/10)*B
def third (φ : ℝ) : ℝ :=
  φ-321/5000-(197/200)*(14/25)+7/20-(7/120)*Real.sin φ+(371/500)*Real.cos φ
def thirdD (φ : ℝ) : ℝ := 1-(7/120)*Real.cos φ-(371/500)*Real.sin φ

lemma lower_first {g d a b A B φ : ℝ} (ht : OuterState A B)
    (hφ : Lower φ) (hg : g∈Icc (7/10) (197/200))
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ+B*Real.cos φ) :
    first g φ-d≤value g d b B φ := by
  have htr := lower_trig hφ
  have hg0 : 0≤g := by linarith [hg.1]
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2
    (by linarith [htr.1] : 0≤Real.sin φ)
  have hc : 0≤7/10-g*Real.cos φ := by
    have hh := mul_le_mul hg.2 htr.2.2.2.1.le htr.2.2.1
      (by norm_num : (0:ℝ)≤197/200)
    nlinarith
  have hp := mul_nonneg hg0
    (show 0≤ -b+outerAxial*Real.sin φ+B*Real.cos φ-
      (1+Real.sin φ+Real.cos φ)/2 by linarith)
  have hB := mul_nonneg hc ht.1
  dsimp [first,value,κ]
  nlinarith

lemma lower_second {g d a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ) (hg : g∈Icc (7/10) (197/200))
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b*Real.sin φ+A) :
    second g φ-d≤value g d b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hcore := CoreAngleEndpoint.state_bounds hs
  have ha := mul_le_mul_of_nonneg_right hcore.1.le htr.2.2.1
  have hb : b+1/2≤(κ-Real.cos φ)/Real.sin φ := by
    apply (le_div_iff₀ hsine).2
    dsimp [κ]
    nlinarith [(NegativeTwo.primary_mem ht).2]
  have hmul := mul_le_mul_of_nonneg_left hb (by linarith [hg.1] : 0≤g)
  have he : (κ-Real.cos φ)/Real.sin φ= -((Real.cos φ-κ)/Real.sin φ) := by ring
  rw [he] at hmul
  have e2 : g*(Real.cos φ-κ)/Real.sin φ=g*((Real.cos φ-κ)/Real.sin φ) := by ring
  dsimp only [second,value]
  rw [e2]
  linarith [ht.1]

lemma third_hasDerivAt (φ : ℝ) : HasDerivAt third (thirdD φ) φ :=
  ((((((hasDerivAt_id φ).sub_const (321/5000)).sub_const
    ((197/200)*(14/25))).add_const (7/20)).sub
      ((Real.hasDerivAt_sin φ).const_mul (7/120))).add
        ((Real.hasDerivAt_cos φ).const_mul (371/500))).congr_deriv
    (by dsimp only [thirdD]; ring)

lemma third_lower {φ : ℝ} (hφ : Lower φ) : (1:ℝ)<third φ := by
  have hm : MonotoneOn third (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (third_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => third_hasDerivAt x)
      (fun x hx => by dsimp [thirdD]; nlinarith [Real.cos_le_one x,Real.sin_le_one x])
  have ha : (87079/100000:ℝ)<lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hl : (1:ℝ)<third lowerAngle := by
    dsimp [third]
    nlinarith [left_trig.2.1,left_trig.2.2.1]
  exact hl.trans_le (hm left_mem hφ hφ.1)

lemma lower_third {g d a b A B φ : ℝ} (hs : CoreState a b)
    (hφ : Lower φ) (hg : g∈Icc (237/250) (197/200)) (hd : d≤321/5000)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) :
    (1:ℝ)<value g d b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hb : b≤14/25 := by linarith [hcore.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  have ha := mul_le_mul_of_nonneg_right hcore.2.1 (by linarith [htr.1] : 0≤Real.sin φ)
  have hc : 0≤g-(7/10)*Real.cos φ := by nlinarith [hg.1,Real.cos_le_one φ]
  have hpay := mul_nonneg hc (sub_nonneg.mpr hb)
  have hgpay := mul_nonneg (show 0≤197/200-g by linarith [hg.2])
    (by norm_num : (0:ℝ)≤14/25)
  have hcompare : third φ≤value g d b B φ := by
    dsimp [third,value]
    nlinarith
  exact (third_lower hφ).trans_le hcompare

lemma lower_fourth {g d a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ) (hg : g∈Icc (237/250) (197/200)) (hd : d≤321/5000)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    (6/5:ℝ)<value g d b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hb : b≤14/25 := by linarith [hcore.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hA : (899/1000:ℝ)≤A := by
    linarith [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2]
  have hAc := mul_le_mul_of_nonneg_right hA htr.2.2.1
  have hc := cotangent_linear hφ
  have hB : 7/18+(1399/1000)*(Real.pi/2-φ)≤B := by
    refine le_of_mul_le_mul_right ?_ hsine
    nlinarith [hcore.2.1]
  have hgb := mul_le_mul hg.2 hb hcore.2.2.1 (by norm_num : (0:ℝ)≤197/200)
  have hx := PositiveThree.lower_deviation hφ
  dsimp [value]
  nlinarith [pi_hand_enclosure.1,hx.2]

theorem original_lower {g d a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ) (hg : g∈Icc (237/250) (197/200)) (hd : d≤321/5000)
    (j : Fin 4) (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (91/100:ℝ)<value g d b B φ := by
  have hg' : g∈Icc (7/10) (197/200) := ⟨by linarith [hg.1],hg.2⟩
  fin_cases j
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ+B*Real.cos φ := by
      norm_num [Eight.forwardMargin,lower_width hφ] at hm
      linarith
    have hh := lower_first (a := a) (d := d) ht hφ hg' hsep
    linarith [first_lower hg' hφ,hg.1]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ-b*Real.sin φ+A := by
      norm_num [Eight.forwardMargin,lower_width hφ] at hm
      linarith
    have hh := lower_second (d := d) hs ht hφ hg' hsep
    linarith [second_lower hg' hφ,hg.1]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B := by
      norm_num [Eight.forwardMargin,lower_width hφ] at hm
      linarith
    linarith [lower_third (A := A) hs hφ hg hd hsep]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ := by
      norm_num [Eight.forwardMargin,lower_width hφ] at hm
      linarith
    linarith [lower_fourth hs ht hφ hg hd hsep]

theorem original {g d a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hg : g∈Icc (237/250) (197/200)) (hd : d≤321/5000)
    (j : Fin 4) (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (91/100:ℝ)<value g d b B φ := by
  by_cases hearly : φ≤Real.pi/2
  · apply original_lower hs ht ?_ hg hd j hm
    exact ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hearly⟩
  · have hcore := CoreAngleEndpoint.state_bounds hs
    have hb : b≤14/25 := by linarith [hcore.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
    have hgb := mul_le_mul hg.2 hb hcore.2.2.1 (by norm_num : (0:ℝ)≤197/200)
    dsimp [value]
    linarith [pi_hand_enclosure.1,ht.1]

end SquaresInCircles.Eight.SecondWord.MixedAffine
