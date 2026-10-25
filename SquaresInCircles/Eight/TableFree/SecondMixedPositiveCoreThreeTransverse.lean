module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreThreeZeroCurve

/-!
# The three complete transverse support intervals

The early multiplier is larger than the label coefficient. Two global
tangents and the sharper initial-arc line then give unsquared circle
supports, each strictly concave on its entire angle interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle)
open MixedTransverseSupport

def early (φ : ℝ) : ℝ := lower (26/25) (779/1000) (-c-13/250) φ
def middle (φ : ℝ) : ℝ := lower g (701151/1000000) (-c-37853/500000) φ
def late (φ : ℝ) : ℝ := lower g (31/50) (-c-1109/10000) φ

private lemma reference_lower {G p C φ sl cl n : ℝ}
    (hG : 0<G) (hp : 0≤p) (hpg : p≤(4/5)*G)
    (hs : sl≤Real.sin φ) (hc : cl≤Real.cos φ) (hn : 0<n)
    (hsq : G^2+p^2-2*G*p*cl<n^2)
    (hscore : γ<φ+C+(G+p)/2+G*sl-(1979/1000)*n) :
    γ<lower G p C φ := by
  have he := lower_sq hG hp hpg φ
  have hNp : 0<lowerN G p φ := CircularNorm.norm_pos (lower_domain hG hp hpg φ)
  have hcos := mul_le_mul_of_nonneg_left hc (by positivity : 0≤2*G*p)
  have hN : lowerN G p φ<n := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 hn)
  have hsin := mul_le_mul_of_nonneg_left hs hG.le
  dsimp [lower]
  linarith

private lemma interval_lower {G p C l u φ : ℝ}
    (hG : 0<G) (hp : 0≤p) (hpg : p≤(4/5)*G)
    (hdom : Icc l u⊆Icc lowerAngle (Real.pi/2))
    (hl : γ<lower G p C l) (hu : γ<lower G p C u) (hφ : φ∈Icc l u) :
    γ<lower G p C φ := by
  have hh : ConcaveOn ℝ (Icc l u) (lower G p C) :=
    concave_of_deriv2 (fun x _ => lower_hasDerivAt hG hp hpg C x)
      (fun x _ => lowerD_hasDerivAt hG hp hpg x)
      (fun x hx => (lower_curvature hG hp hpg (hdom hx)).le)
  exact concave_gt_of_endpoints hh hφ hl hu

lemma one_trig : (8414709/10000000:ℝ)≤Real.sin 1 ∧ (5403023/10000000:ℝ)≤Real.cos 1 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma transition_trig :
    (1178111/1250000:ℝ)≤Real.sin (123/100) ∧ (3342377/10000000:ℝ)≤Real.cos (123/100) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (123/100:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (123/100:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma early_left : γ<early 1 :=
  reference_lower (n := (450827/500000:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    one_trig.1 one_trig.2 (by norm_num) (by norm_num) (by norm_num [γ,c])

lemma early_right : γ<early (123/100) :=
  reference_lower (n := (26773/25000:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    transition_trig.1 transition_trig.2 (by norm_num) (by norm_num) (by norm_num [γ,c])

lemma middle_left : γ< middle (123/100) :=
  reference_lower (n := (972847/1000000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    transition_trig.1 transition_trig.2 (by norm_num) (by norm_num [g]) (by norm_num [g,γ,c])

lemma middle_right : γ< middle (7/5) :=
  reference_lower (n := (134912/125000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    PrimaryZero.terminal_trig.1 PrimaryZero.terminal_trig.2.2.1 (by norm_num)
    (by norm_num [g]) (by norm_num [g,γ,c])

lemma late_left : γ<late (7/5) :=
  reference_lower (n := (1041071/1000000:ℝ)) (by norm_num [g]) (by norm_num) (by norm_num [g])
    PrimaryZero.terminal_trig.1 PrimaryZero.terminal_trig.2.2.1 (by norm_num)
    (by norm_num [g]) (by norm_num [g,γ,c])

lemma late_aligned : (9/10:ℝ)<late (Real.pi/2) := by
  have he := lower_sq (g := g) (p := (31/50:ℝ))
    (by norm_num [g]) (by norm_num) (by norm_num [g]) (Real.pi/2)
  have hp : 0<lowerN g (31/50) (Real.pi/2) := CircularNorm.norm_pos
    (lower_domain (by norm_num [g]) (by norm_num) (by norm_num [g]) (Real.pi/2))
  simp only [late,lower,Real.sin_pi_div_two]
  generalize lowerN g (31/50) (Real.pi/2) = n at he hp ⊢
  rw [Real.cos_pi_div_two] at he
  norm_num [g] at he
  have hN : n<(566501/500000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<566501/500000))
  dsimp [g,c]
  linarith [pi_hand_enclosure.1]

theorem early_lower {φ : ℝ} (hφ : φ∈Icc (1:ℝ) (123/100)) : γ<early φ :=
  interval_lower (by norm_num) (by norm_num) (by norm_num)
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
      by linarith [hx.2,pi_hand_enclosure.1]⟩) early_left early_right hφ

theorem middle_lower {φ : ℝ} (hφ : φ∈Icc (123/100:ℝ) (7/5)) : γ< middle φ :=
  interval_lower (by norm_num [g]) (by norm_num) (by norm_num [g])
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
      by linarith [hx.2,pi_hand_enclosure.1]⟩) middle_left middle_right hφ

theorem late_lower {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : γ<late φ :=
  interval_lower (by norm_num [g]) (by norm_num) (by norm_num [g])
    (fun x hx => ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],hx.2⟩)
    late_left ((show γ<9/10 by norm_num [γ]).trans late_aligned) hφ

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
