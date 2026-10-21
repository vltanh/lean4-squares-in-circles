module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeContact
public import SquaresInCircles.Eight.TableFree.SecondMixedLHeightAffine

/-!
# The complete original positive-core corner primary owner

The core circle supplies one rational chord for its primary coordinate.
Each of two height minorants then gives a function affine in the core
coordinate and concave in the whole early angle interval. Four endpoint
values suffice for either line. No target contact is selected or assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (29/25)
def height (a b φ : ℝ) : ℝ := 1+(a+1/2)*Real.cos φ-(b-1/2)*Real.sin φ
def chord (b : ℝ) : ℝ := 7/12-(5/12)*(b-1/2)
def support (λ κ b φ : ℝ) : ℝ :=
  φ-e+g*b+λ*(1+(chord b+1/2)*Real.cos φ-(b-1/2)*Real.sin φ)-κ
def supportD (λ b φ : ℝ) : ℝ :=
  1-λ*(chord b+1/2)*Real.sin φ-λ*(b-1/2)*Real.cos φ

lemma terminal_trig :
    (9168031/10000000:ℝ)<Real.sin (29/25) ∧ Real.sin (29/25)<9168032/10000000 ∧
    (3993395/10000000:ℝ)<Real.cos (29/25) ∧ Real.cos (29/25)<3993396/10000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (29/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (29/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (29/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (29/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    0≤Real.sin φ ∧ Real.sin φ≤9168032/10000000 ∧
    (3993395/10000000:ℝ)≤Real.cos φ ∧ Real.cos φ≤64424/100000 := by
  have ht := lower_trig (lower_mem hφ)
  have he : (29/25:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hs := PositiveThree.lower_sin_monotone (lower_mem hφ) (lower_mem he) hφ.2
  have hc := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem he) hφ.2
  exact ⟨by linarith [ht.1],hs.trans terminal_trig.2.1.le,
    terminal_trig.2.2.1.le.trans hc,by linarith [ht.2.2.2.1]⟩

lemma core_chord {a b : ℝ} (hs : CoreState a b) (hb : 1/2≤b) : chord b≤a := by
  rcases hs with ⟨rfl,hb0,hbu⟩ | ⟨hb0,hba,hcircle⟩
  · dsimp [chord]
    linarith
  · have hd := CoreAngleEndpoint.corner_diagonal hb0 hba hcircle
    have hbs : b<(559/1000:ℝ) := hd.1.trans_lt (by linarith [CoreAngleEndpoint.diagonal_bounds.2])
    have has : (5589/10000:ℝ)<a := by linarith [hd.2,CoreAngleEndpoint.diagonal_bounds.1]
    have hp := mul_nonneg (show 0≤b-1/2 by linarith)
      (show 0≤(5/12)*(a-1/2+1/12)-(b-1/2) by linarith)
    have hden : 0<a-1/2+1/12 := by linarith
    apply (mul_le_mul_right hden).mp
    dsimp [chord]
    nlinarith

lemma height_bounds {a b φ : ℝ} (hs : CoreState a b) (hb : 1/2≤b) (hφ : φ∈angles) :
    height a b φ∈Icc (171/125:ℝ) (17/10) := by
  have hc := CoreAngleEndpoint.state_bounds hs
  have hd : CoreAngleEndpoint.diagonal≤a := by
    rcases hs with ⟨rfl,hb0,hbu⟩ | ⟨hb0,hba,hcircle⟩
    · linarith [CoreAngleEndpoint.diagonal_bounds.2]
    · exact (CoreAngleEndpoint.corner_diagonal hb0 hba hcircle).2
  have ht := trig hφ
  have ha : (105892556/100000000:ℝ)≤a+1/2 := by
    linarith [hd,CoreAngleEndpoint.diagonal_bounds.1]
  have hbu : b-1/2≤5892557/100000000 := by
    linarith [hc.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  have hlo := mul_le_mul ha ht.2.2.1 (by norm_num : (0:ℝ)≤3993395/10000000)
    (by linarith [ha] : 0≤a+1/2)
  have hhi := mul_le_mul hbu ht.2.1 ht.1 (by norm_num : (0:ℝ)≤5892557/100000000)
  have hu := mul_le_mul (show a+1/2≤13/12 by linarith [hc.2.1]) ht.2.2.2
    (by linarith [ht.2.2.1] : 0≤Real.cos φ) (by norm_num : (0:ℝ)≤13/12)
  have hn := mul_nonneg (sub_nonneg.mpr hb) ht.1
  dsimp [height]
  constructor <;> nlinarith

lemma support_hasDerivAt (λ κ b φ : ℝ) : HasDerivAt (support λ κ b) (supportD λ b φ) φ := by
  convert (((hasDerivAt_id φ).add_const (-e+g*b)).add
    (((((Real.hasDerivAt_cos φ).const_mul (chord b+1/2)).sub
      ((Real.hasDerivAt_sin φ).const_mul (b-1/2))).const_add 1).const_mul λ)).sub_const κ using 1 <;>
    dsimp [support,supportD] <;> ring

lemma supportD_hasDerivAt (λ b φ : ℝ) : HasDerivAt (supportD λ b)
    (-λ*(chord b+1/2)*Real.cos φ+λ*(b-1/2)*Real.sin φ) φ := by
  convert ((((Real.hasDerivAt_sin φ).const_mul (λ*(chord b+1/2))).const_sub 1).sub
    ((Real.hasDerivAt_cos φ).const_mul (λ*(b-1/2)))) using 1 <;>
    dsimp [supportD] <;> ring

lemma support_concave {λ κ b : ℝ} (hλ : 0≤λ) (hb : b∈Icc (1/2:ℝ) (559/1000)) :
    ConcaveOn ℝ angles (support λ κ b) := by
  apply concave_of_deriv2 (fun φ _ => support_hasDerivAt λ κ b φ)
    (fun φ _ => supportD_hasDerivAt λ b φ)
  intro φ hφ
  have ht := trig hφ
  have hA : (1:ℝ)≤chord b+1/2 := by dsimp [chord]; linarith [hb.2]
  have hp := mul_le_mul hA ht.2.2.1 (by norm_num : (0:ℝ)≤3993395/10000000)
    (by linarith : 0≤chord b+1/2)
  have hq := mul_le_mul (show b-1/2≤59/1000 by linarith [hb.2]) (Real.sin_le_one φ)
    ht.1 (by norm_num : (0:ℝ)≤59/1000)
  have hh := mul_nonneg hλ
    (show 0≤(chord b+1/2)*Real.cos φ-(b-1/2)*Real.sin φ by linarith)
  nlinarith

lemma line_endpoints (high : Bool) :
    let λ : ℝ := if high then 19/20 else 132/125
    let κ : ℝ := if high then 1037727/500000 else 89809/40000
    γ<support λ κ (1/2) lowerAngle ∧ γ<support λ κ (559/1000) lowerAngle ∧
    γ<support λ κ (1/2) (29/25) ∧ γ<support λ κ (559/1000) (29/25) := by
  have hl := MixedAffine.left_trig
  have hr := terminal_trig
  cases high <;> norm_num [support,chord,g,e,γ,EdgeThreeAligned.gp,EdgeThreeAligned.ep,
    EdgeThreeAligned.threshold,lowerAngle] <;>
    repeat' constructor <;> nlinarith [hl.1,hl.2.1,hl.2.2.1,hr.2.1,hr.2.2.1,pi_hand_enclosure.1]

lemma line_lower (high : Bool) {b φ : ℝ} (hb : b∈Icc (1/2:ℝ) (559/1000)) (hφ : φ∈angles) :
    let λ : ℝ := if high then 19/20 else 132/125
    let κ : ℝ := if high then 1037727/500000 else 89809/40000
    γ<support λ κ b φ := by
  let λ : ℝ := if high then 19/20 else 132/125
  let κ : ℝ := if high then 1037727/500000 else 89809/40000
  have hλ : 0≤λ := by cases high <;> norm_num [λ]
  have he := line_endpoints high
  change γ<support λ κ (1/2) lowerAngle ∧ γ<support λ κ (559/1000) lowerAngle ∧
    γ<support λ κ (1/2) (29/25) ∧ γ<support λ κ (559/1000) (29/25) at he
  have hleft := concave_gt_of_endpoints (support_concave (κ := κ) hλ (by norm_num : (1/2:ℝ)∈Icc (1/2) (559/1000))) hφ he.1 he.2.2.1
  have hright := concave_gt_of_endpoints (support_concave (κ := κ) hλ (by norm_num : (559/1000:ℝ)∈Icc (1/2) (559/1000))) hφ he.2.1 he.2.2.2
  have hm := affine_min_le (c := g-λ*Real.sin φ-(5/12)*λ*Real.cos φ) hb
  have hlo : γ<min (support λ κ (1/2) φ) (support λ κ (559/1000) φ) := lt_min hleft hright
  have hid (b : ℝ) : support λ κ b φ=
      (g-λ*Real.sin φ-(5/12)*λ*Real.cos φ)*b+
      (φ-e+λ*(1+(31/24)*Real.cos φ+Real.sin φ/2)-κ) := by dsimp [support,chord]; ring
  have hi0 := hid (1/2:ℝ)
  have hi1 := hid (559/1000:ℝ)
  rw [hi0,hi1,min_add_add_right] at hlo
  change γ<support λ κ b φ
  rw [hid b]
  linarith

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (hb : 1/2≤b)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ+b*Real.sin φ+A) :
    γ<value b B φ := by
  have hc := CoreAngleEndpoint.state_bounds hs
  by_cases he : (29/25:ℝ)≤φ
  · have hL := L_upper (NegativeTwo.source_mem ht)
    have hp := mul_le_mul_of_nonneg_left hb (by norm_num [g,EdgeThreeAligned.gp] : 0≤g)
    dsimp [value,EdgeThreeAligned.positiveCost,γ,EdgeThreeAligned.threshold,g,EdgeThreeAligned.gp,e,EdgeThreeAligned.ep] at *
    linarith
  · have hangle : φ∈angles := ⟨hφ.1,by linarith⟩
    have hu := height_bounds hs hb hangle
    have hactual := EdgeThreeAligned.height_bounds ht
    have hmono := LHeightBounds.eval_monotone
      (show height a b φ∈LHeightBounds.heights from ⟨hu.1,by linarith [hu.2]⟩)
      hactual (show height a b φ≤A+1/2 by dsimp [height]; linarith)
    rw [LHeight_actual ht] at hmono
    have hchord := core_chord hs hb
    have htφ := trig hangle
    have hpaid := mul_le_mul_of_nonneg_right hchord
      (show 0≤Real.cos φ by linarith [htφ.2.2.1])
    have hbd : b∈Icc (1/2:ℝ) (559/1000) :=
      ⟨hb,by linarith [hc.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]⟩
    by_cases hlo : height a b φ≤8/5
    · have hM := LHeightAffine.low ⟨hu.1,hlo⟩
      have hh := line_lower false hbd hangle
      norm_num [support,height,value,EdgeThreeAligned.positiveCost] at hh hM ⊢
      nlinarith
    · have hM := LHeightAffine.high ⟨by linarith,by linarith [hu.2]⟩
      have hh := line_lower true hbd hangle
      norm_num [support,height,value,EdgeThreeAligned.positiveCost] at hh hM ⊢
      nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource.Corner
