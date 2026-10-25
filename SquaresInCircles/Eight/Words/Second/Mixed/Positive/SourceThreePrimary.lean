module

public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Mixed.LPrimaryZeroCost
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateShape
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeSupport

/-!
# Eight squares: the lower primary owner for the positive core source

The side uses the circle support up to `B = .65` (`small_relaxation`). Beyond it, a concave first
derivative leaves the fixed endpoint, the physical zero-source endpoint (`zero_value`) or the
diagonal (`side_original`). The corner has its own comparison at the original height
(`Corner.original`). Every exit is covered.
-/

section
/-!
## The complete original positive-core corner primary owner

The core circle supplies one rational chord for its primary coordinate.
Each of two height minorants then gives a function affine in the core
coordinate and concave in the whole early angle interval. Four endpoint
values suffice for either line. No target contact is selected or assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (29/25)
def height (a b φ : ℝ) : ℝ := 1+(a+1/2)*Real.cos φ-(b-1/2)*Real.sin φ
def chord (b : ℝ) : ℝ := 7/12-(5/12)*(b-1/2)
def support (lam κ b φ : ℝ) : ℝ :=
  φ-e+g*b+lam*(1+(chord b+1/2)*Real.cos φ-(b-1/2)*Real.sin φ)-κ
def supportD (lam b φ : ℝ) : ℝ :=
  1-lam*(chord b+1/2)*Real.sin φ-lam*(b-1/2)*Real.cos φ

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

private lemma r35_left_trig :
    (19121/25000:ℝ)<Real.sin lowerAngle ∧ Real.sin lowerAngle<15297/20000 ∧
    (64421/100000:ℝ)<Real.cos lowerAngle ∧ Real.cos lowerAngle<32211/50000 := by
  obtain ⟨hs1,hs2,hc1,hc2⟩ := trig_taylor_bounds (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin9,sin7,cos10,cos8] at hs1 hs2 hc1 hc2
  simp only [lowerAngle,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    0≤Real.sin φ ∧ Real.sin φ≤9168032/10000000 ∧
    (3993395/10000000:ℝ)≤Real.cos φ ∧ Real.cos φ≤64424/100000 := by
  have ht := lower_trig (lower_mem hφ)
  have he : (29/25:ℝ)∈angles := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],le_rfl⟩
  have hl : 0≤lowerAngle := by dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hs : Real.sin φ≤Real.sin (29/25) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hφ.1,Real.pi_pos])
      (by linarith [pi_hand_enclosure.1]) hφ.2
  have hc : Real.cos (29/25)≤Real.cos φ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hφ.1])
      (by linarith [pi_hand_enclosure.1]) hφ.2
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
    apply le_of_mul_le_mul_right _ hden
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

lemma support_hasDerivAt (lam κ b φ : ℝ) : HasDerivAt (support lam κ b) (supportD lam b φ) φ := by
  have h := (((hasDerivAt_id' φ).add_const (-e+g*b)).add
    (((((Real.hasDerivAt_cos φ).const_mul (chord b+1/2)).sub
      ((Real.hasDerivAt_sin φ).const_mul (b-1/2))).const_add 1).const_mul lam)).sub_const κ
  convert h using 1
  · funext x
    simp only [support,Pi.add_apply,Pi.sub_apply]
    ring
  · simp only [supportD]
    ring

lemma supportD_hasDerivAt (lam b φ : ℝ) : HasDerivAt (supportD lam b)
    (-lam*(chord b+1/2)*Real.cos φ+lam*(b-1/2)*Real.sin φ) φ := by
  have h := (((Real.hasDerivAt_sin φ).const_mul (lam*(chord b+1/2))).const_sub 1).sub
    ((Real.hasDerivAt_cos φ).const_mul (lam*(b-1/2)))
  convert h using 1
  · funext x
    simp only [supportD,Pi.sub_apply]
  · ring

lemma support_concave {lam κ b : ℝ} (hlam : 0≤lam) (hb : b∈Icc (1/2:ℝ) (559/1000)) :
    ConcaveOn ℝ angles (support lam κ b) := by
  apply concave_of_deriv2 (fun φ _ => support_hasDerivAt lam κ b φ)
    (fun φ _ => supportD_hasDerivAt lam b φ)
  intro φ hφ
  have ht := trig hφ
  have hA : (1:ℝ)≤chord b+1/2 := by dsimp [chord]; linarith [hb.2]
  have hp := mul_le_mul hA ht.2.2.1 (by norm_num : (0:ℝ)≤3993395/10000000)
    (by linarith : 0≤chord b+1/2)
  have hq := mul_le_mul (show b-1/2≤59/1000 by linarith [hb.2]) (Real.sin_le_one φ)
    ht.1 (by norm_num : (0:ℝ)≤59/1000)
  have hh := mul_nonneg hlam
    (show 0≤(chord b+1/2)*Real.cos φ-(b-1/2)*Real.sin φ by linarith)
  nlinarith

lemma line_endpoints (high : Bool) :
    let lam : ℝ := if high then 19/20 else 132/125
    let κ : ℝ := if high then 1037727/500000 else 89809/40000
    γ<support lam κ (1/2) lowerAngle ∧ γ<support lam κ (559/1000) lowerAngle ∧
    γ<support lam κ (1/2) (29/25) ∧ γ<support lam κ (559/1000) (29/25) := by
  have hl := r35_left_trig
  have hr := terminal_trig
  have hla : (87079/100000:ℝ)<lowerAngle := by
    dsimp only [lowerAngle]
    linarith [pi_hand_enclosure.1]
  cases high <;>
    simp only [support,chord,g,e,γ,EdgeThreeAligned.gp,EdgeThreeAligned.ep,
      EdgeThreeAligned.threshold,Bool.false_eq_true,↓reduceIte] <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith [hl.1,hl.2.1,hl.2.2.1,hr.2.1,hr.2.2.1]

lemma line_lower (high : Bool) {b φ : ℝ} (hb : b∈Icc (1/2:ℝ) (559/1000)) (hφ : φ∈angles) :
    let lam : ℝ := if high then 19/20 else 132/125
    let κ : ℝ := if high then 1037727/500000 else 89809/40000
    γ<support lam κ b φ := by
  let lam : ℝ := if high then 19/20 else 132/125
  let κ : ℝ := if high then 1037727/500000 else 89809/40000
  have hlam : 0≤lam := by cases high <;> norm_num [lam]
  have he := line_endpoints high
  change γ<support lam κ (1/2) lowerAngle ∧ γ<support lam κ (559/1000) lowerAngle ∧
    γ<support lam κ (1/2) (29/25) ∧ γ<support lam κ (559/1000) (29/25) at he
  have hleft := concave_gt_of_endpoints (support_concave (κ := κ) hlam (by norm_num : (1/2:ℝ)∈Icc (1/2) (559/1000))) hφ he.1 he.2.2.1
  have hright := concave_gt_of_endpoints (support_concave (κ := κ) hlam (by norm_num : (559/1000:ℝ)∈Icc (1/2) (559/1000))) hφ he.2.1 he.2.2.2
  have hm := affine_min_le (c := g-lam*Real.sin φ-(5/12)*lam*Real.cos φ) hb
  have hlo : γ< min (support lam κ (1/2) φ) (support lam κ (559/1000) φ) := lt_min hleft hright
  have hid (b : ℝ) : support lam κ b φ=
      (g-lam*Real.sin φ-(5/12)*lam*Real.cos φ)*b+
      (φ-e+lam*(1+(31/24)*Real.cos φ+Real.sin φ/2)-κ) := by dsimp [support,chord]; ring
  have hi0 := hid (1/2:ℝ)
  have hi1 := hid (559/1000:ℝ)
  rw [hi0,hi1,min_add_add_right] at hlo
  change γ<support lam κ b φ
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
      simp only [support,Bool.false_eq_true,↓reduceIte] at hh
      simp only [height] at hM hmono
      simp only [value,EdgeThreeAligned.positiveCost,γ,g,e] at hh ⊢
      linarith
    · have hM := LHeightAffine.high (u := height a b φ) ⟨by linarith,by linarith [hu.2]⟩
      have hh := line_lower true hbd hangle
      simp only [support,↓reduceIte] at hh
      simp only [height] at hM hmono
      simp only [value,EdgeThreeAligned.positiveCost,γ,g,e] at hh ⊢
      linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Corner
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Primary
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open PositiveThree (Lower lowerAngle lower_trig)

lemma small_relaxation {B φ : ℝ} (hB : B∈Icc (0:ℝ) (13/20)) (hφ : Lower φ)
    (he : φ≤73/50) : γ<H B φ := by
  have hBf := Asymmetric.rational_outer_mem
    (show B∈Icc (0:ℝ) (899/1000) from ⟨hB.1,by linarith [hB.2]⟩)
  have ht := ShortOuterOne.SameContact.arc_state hBf
  have hs : 0<Real.sin φ := by linarith [(lower_trig hφ).1]
  let x := Real.pi/2-φ
  have hx : x∈Icc (11/100:ℝ) (7/10) :=
    ⟨by dsimp [x]; linarith [pi_hand_enclosure.1],by
      show Real.pi/2-φ≤7/10
      linarith [show Real.pi/2-7/10≤φ from hφ.1]⟩
  have hφeq : φ=Real.pi/2-x := by dsimp [x]; ring
  have hL := MixedLEnvelopes.primary hB
  have hLp := mul_le_mul_of_nonneg_right hL.le hs.le
  have hcircle := outer_circle_lower (X := -g) (Y := -PrimarySupport.p*Real.sin φ) ht
  have hnorm : Real.sqrt ((-g)^2+(-PrimarySupport.p*Real.sin φ)^2)=
      MixedPrimarySupport.N g PrimarySupport.p x := by
    rw [hφeq]
    norm_num [Real.sin_sub,MixedPrimarySupport.N]
    congr 1
    ring
  rw [hnorm] at hcircle
  have hraw : (H B φ-γ)*Real.sin φ=
      (φ-e-L B-γ)*Real.sin φ+g*(LPrimaryZero.U φ-1/2-arc B) := by
    dsimp [H,source]
    field_simp [hs.ne']
    ring
  have hpaid : PrimarySupport.f x≤(H B φ-γ)*Real.sin φ := by
    rw [hraw]
    dsimp [LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    rw [hφeq] at hcircle hLp ⊢
    norm_num [Real.sin_sub,Real.cos_sub,PrimarySupport.f,MixedPrimarySupport.minus,
      PrimarySupport.K,PrimarySupport.k,PrimarySupport.p] at hcircle hLp ⊢
    nlinarith
  have hpos := PrimarySupport.positive hx
  nlinarith

lemma small_direct {b B φ : ℝ} (hb : 0≤b) (hB : B∈Icc (0:ℝ) (13/20))
    (hφ : (73/50:ℝ)≤φ) : γ<value b B φ := by
  have hL := MixedLEnvelopes.primary hB
  have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
  dsimp [value,EdgeThreeAligned.positiveCost,γ,EdgeThreeAligned.threshold,e,EdgeThreeAligned.ep] at *
  linarith [hB.2]

lemma endpoint_lower {l B φ : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hB : B∈Icc l outerDiagonal) (hφ : Lower φ)
    (hslope : 0<HB l φ) (hvalue : γ<H l φ) : γ<H B φ := by
  have hdom {y : ℝ} (hy : y∈Icc l outerDiagonal) : y∈Icc 0 outerDiagonal :=
    ⟨hl.1.trans hy.1,hy.2⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (f := fun y => H y φ) (d := fun y => HB y φ)
    (dd := fun y => HBB y φ) (ddd := fun y => HBBB y φ) hB
    (fun y hy => H_hasDerivAt (hdom hy)) (fun y hy => HB_hasDerivAt (hdom hy))
    (fun y hy => HBB_hasDerivAt (hdom hy))
    (fun y hy => (HBBB_negative (hdom hy) hφ).le) hslope
  exact (lt_min hvalue (diagonal_lower hφ)).trans_le hh

lemma zero_source {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : source (LPrimaryZero.b φ) φ=0 := by
  have ha := (ShortOuterOne.SameContact.actual_arc (LPrimaryZero.physical hφ)).1
  simp [source,ha]

lemma zero_value {φ : ℝ} (hφ : φ∈LPrimaryZero.angles) : γ<H (LPrimaryZero.b φ) φ := by
  have hh := LPrimaryZero.actual_positive (LPrimaryZero.physical hφ) hφ (by ring)
  rw [H,zero_source hφ]
  dsimp [γ,EdgeThreeAligned.threshold,e,EdgeThreeAligned.ep]
  linarith

theorem side_original {b A B φ : ℝ} (hb : 0≤b) (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-(7/12)*Real.cos φ+b*Real.sin φ+A) :
    γ<value b B φ := by
  have hB := NegativeTwo.source_mem ht
  have hcmp := original_lower ht hφ hsep
  have h65 : (13/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have h65unit : (13/20:ℝ)∈Icc (13/20:ℝ) EdgeThreeAligned.B1 :=
    ⟨le_rfl,by linarith [EdgeThreeAligned.B1_bounds.1]⟩
  by_cases hsmall : B≤13/20
  · by_cases he : φ≤73/50
    · exact (small_relaxation ⟨hB.1,hsmall⟩ hφ he).trans_le hcmp
    · exact small_direct hb ⟨hB.1,hsmall⟩ (by linarith)
  · have hlarge : (13/20:ℝ)≤B := by linarith
    by_cases he : φ≤73/50
    · exact (endpoint_lower h65 ⟨hlarge,hB.2⟩ hφ (zero_derivative h65unit hφ)
        (small_relaxation (by norm_num) hφ he)).trans_le hcmp
    · have hangle : φ∈LPrimaryZero.angles := ⟨by linarith,hφ.2⟩
      have hzstate := LPrimaryZero.physical hangle
      have hz := NegativeTwo.source_mem hzstate
      have hzunit : LPrimaryZero.b φ≤EdgeThreeAligned.B1 :=
        (EdgeThreeAligned.unit_target_cut hzstate).1 (by linarith [(LPrimaryZero.U_bounds hangle).1])
      have haz := (ShortOuterOne.SameContact.actual_arc hzstate).1
      by_cases hzsmall : LPrimaryZero.b φ≤13/20
      · have ha := ShortOuterOne.SameContact.arc_antitone (outer_domain hz) (outer_domain h65) hzsmall
        rw [haz] at ha
        have hs0 : 0 ≤ source (13/20) φ := div_nonneg (by linarith) (by linarith [(lower_trig hφ).1])
        have hd := small_direct hs0 (show (13/20:ℝ)∈Icc (0:ℝ) (13/20) by norm_num) (by linarith : (73/50:ℝ)≤φ)
        have hleft : γ<H (13/20) φ := by simpa [H,value,EdgeThreeAligned.positiveCost] using hd
        exact (endpoint_lower h65 ⟨hlarge,hB.2⟩ hφ (zero_derivative h65unit hφ) hleft).trans_le hcmp
      · by_cases hbefore : B≤LPrimaryZero.b φ
        · have hL := L_monotone hB hz hbefore
          have hh := LPrimaryZero.actual_positive hzstate hangle (by ring)
          have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
          dsimp [value,EdgeThreeAligned.positiveCost,e,EdgeThreeAligned.ep,γ,EdgeThreeAligned.threshold]
          linarith
        · exact (endpoint_lower hz ⟨by linarith,hB.2⟩ hφ
            (zero_derivative ⟨by linarith,hzunit⟩ hφ) (zero_value hangle)).trans_le hcmp

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ+b*Real.sin φ+A) :
    γ<value b B φ := by
  rcases hs with ⟨rfl,hb,hbu⟩ | ⟨hb,hba,hcircle⟩
  · exact side_original hb ht hφ hsep
  · exact Corner.original (Or.inr ⟨hb,hba,hcircle⟩) hb ht hφ hsep

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Primary
end
end
end
