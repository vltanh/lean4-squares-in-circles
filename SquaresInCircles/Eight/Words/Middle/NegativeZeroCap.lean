module

public import SquaresInCircles.Eight.Words.Middle.AAdvanceContraction

/-!
# Eight squares: returning a negative hard quarter to zero at the original circle

Rotate the shifted corner `(X-1,Y-1)` about `(1,1)`.
The exact norm drop follows from sorting.  The transverse drop is bounded
by the same `21/20` demand estimate used in the positive cap construction.
This proves the finite zero-cap comparison directly, without a piecewise
negative-cap derivative, diagonal transition, or common-radius lift.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleNegativeZeroCap
open HardSplitCap MiddleAAdvanceContraction

/-- Negative signed hard contacts also make the zero cap feasible at
the same source radius.  The two cases are the sign of `Y-1`. -/
theorem feasible_zero {q D θ X Y : ℝ}
    (hq : q ≤ qCap) (hD : 2/5 ≤ D) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (hcontact : D ≤ (X-1)*Real.cos θ+(Y-1)*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) : MiddleHardCap.Feasible q D := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 < Real.cos θ := by linarith only [hc]
  have hsortprod := mul_nonneg hs (sub_nonneg.mpr hXY)
  have hU : 0 < X-1 := by
    by_contra! hn
    have hp := mul_nonpos_of_nonpos_of_nonneg hn
      (show 0 ≤ Real.cos θ+Real.sin θ by linarith only [hc,hs])
    linarith only [hcontact,hp,hsortprod,hD]
  refine ⟨hq,hD,?_⟩
  by_cases hY1 : Y ≤ 1
  · have hyprod := mul_nonpos_of_nonpos_of_nonneg (show Y-1 ≤ 0 by linarith only [hY1]) hs
    have hxprod := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hU.le
    have hDX : D+1 ≤ X := by linarith only [hcontact,hyprod,hxprod]
    have hx2 := pow_le_pow_left₀ (show 0 ≤ D+1 by linarith only [hD]) hDX 2
    have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hY 2
    linarith only [hx2,hy2,hcircle]
  · have hV : 0 ≤ Y-1 := by linarith only [hY1]
    let P := (X-1)*Real.cos θ+(Y-1)*Real.sin θ
    have hD0 : 0 ≤ D := by linarith only [hD]
    have hDP : D ≤ P := hcontact
    have hDP2 := pow_le_pow_left₀ hD0 hDP 2
    have hnorm : P^2+((X-1)*Real.sin θ-(Y-1)*Real.cos θ)^2=
        (X-1)^2+(Y-1)^2 := by
      dsimp [P]
      calc
        _ = ((X-1)^2+(Y-1)^2)*((Real.sin θ)^2+(Real.cos θ)^2) := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq,mul_one]
    have hDs : D^2 ≤ (X-1)^2+(Y-1)^2 := by
      linarith only [hDP2,hnorm,sq_nonneg ((X-1)*Real.sin θ-(Y-1)*Real.cos θ)]
    have hxprod := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hU.le
    have hyprod := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hV
    have hsum : D ≤ (X-1)+(Y-1) := by linarith only [hcontact,hxprod,hyprod]
    linarith only [hDs,hsum,hcircle]

def rotatedX (X Y θ : ℝ) : ℝ :=
  1+(X-1)*Real.cos θ+(Y-1)*Real.sin θ
def rotatedY (X Y θ : ℝ) : ℝ :=
  1-(X-1)*Real.sin θ+(Y-1)*Real.cos θ

theorem rotation_norm_strict {X Y θ : ℝ}
    (hXY : Y ≤ X) (hX : 1 < X)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hθ0 : 0 < θ) :
    (rotatedX X Y θ)^2+(rotatedY X Y θ)^2 < X^2+Y^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hθ
  have hc0 : 0 < Real.cos θ := by linarith
  have hspos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0
    (by linarith [hθ.2,Real.pi_gt_three])
  let c := Real.cos θ
  let s := Real.sin θ
  let v := 1-c
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hclt : c < 1 := by
    by_contra! hn
    have hp := mul_pos hspos hspos
    have hcs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hn 2
    nlinarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hsum : 1 < c+s := by
    by_contra! hn
    have hcs := pow_le_pow_left₀ (by dsimp [c,s]; positivity : 0 ≤ c+s) hn 2
    have hp := mul_pos hc0 hspos
    nlinarith
  have hvs : 0 < s-v := by dsimp [v]; linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hXY) hvs.le
  have hstrict := mul_pos (sub_pos.mpr hX) hv
  have hid : (rotatedX X Y θ)^2+(rotatedY X Y θ)^2-X^2-Y^2=
      -2*(X-Y)*(s-v)-4*(X-1)*v := by
    dsimp [rotatedX,rotatedY,v,c,s]
    linear_combination ((X-1)^2+(Y-1)^2)*(Real.sin_sq_add_cos_sq θ)
  linarith

/-- Finite loss bound on the original circle.  Its coefficient is
strictly dominated by the positive cap gain on the opposite anchor. -/
theorem negative_zero_loss {q D θ X Y : ℝ}
    (hq : q ≤ qCap) (hD : 2/5 ≤ D) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hθ0 : 0 < θ)
    (hcontact : D ≤ (X-1)*Real.cos θ+(Y-1)*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) :
    MiddleHardCap.Feasible q D ∧ Y < cap q D 0+(21/20)*θ := by
  have hf := feasible_zero hq hD hXY hY hθ hcontact hcircle
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hsortprod := mul_nonneg hs (sub_nonneg.mpr hXY)
  have hX1 : 1 < X := by
    by_contra! hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (show X-1 ≤ 0 by linarith only [hn])
      (show 0 ≤ Real.cos θ+Real.sin θ by linarith only [hc,hs])
    linarith only [hcontact,hp,hsortprod,hD]
  have hXu : X ≤ 383/200 := by
    by_contra! hn
    have hx2 := pow_lt_pow_left₀ hn (by norm_num : (0:ℝ) ≤ 383/200)
      (by decide : (2:ℕ)≠0)
    have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hY 2
    have hQ := hq
    dsimp [qCap] at hQ
    linarith only [hx2,hy2,hQ,hcircle]
  have hYu : Y ≤ 3/2 := by
    by_contra! hn
    have hy2 := pow_lt_pow_left₀ hn (by norm_num : (0:ℝ) ≤ 3/2)
      (by decide : (2:ℕ)≠0)
    have hx2 := pow_le_pow_left₀ (show 0 ≤ Y by linarith only [hY]) hXY 2
    have hQ := hq
    dsimp [qCap] at hQ
    linarith only [hx2,hy2,hQ,hcircle]
  let proxy : SignedPoint := ⟨X-1/2,Y-3/2⟩
  have hproxyA : proxy.a ≤ 283/200 := by dsimp [proxy]; linarith only [hXu]
  have hproxyY : proxy.y ≤ 0 := by dsimp [proxy]; linarith only [hYu]
  have hg := demand_gain hproxyA hproxyY hθ (by norm_num : (0:ℝ) ≤ 0) hθ0
  have hd0 : demand proxy 0=Y := by simp [demand,proxy]; ring
  have hdθ : demand proxy θ=rotatedY X Y θ := by dsimp [demand,proxy,rotatedY]; ring
  rw [hd0,hdθ,sub_zero] at hg
  have hnorm := rotation_norm_strict hXY hX1 hθ hθ0
  have hXrot : D+1 ≤ rotatedX X Y θ := by dsimp [rotatedX]; linarith only [hcontact]
  have hXrot2 := pow_le_pow_left₀ (show 0 ≤ D+1 by linarith only [hD]) hXrot 2
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hw := MiddleHardCap.root_pos hf hzero
  have hw2 := MiddleHardCap.root_sq hf hzero
  have hcap0 : cap q D 0=root q D 0 := by simp [cap]
  have hYrot : rotatedY X Y θ < cap q D 0 := by
    rw [hcap0]
    simp only [contact,Real.cos_zero] at hw2
    have hlt : (rotatedY X Y θ)^2<(root q D 0)^2 := by
      linarith only [hw2,hnorm,hcircle,hXrot2]
    exact lt_of_pow_lt_pow_left₀ 2 hw.le hlt
  exact ⟨hf,by linarith only [hg,hYrot]⟩

end SquaresInCircles.Eight.MiddleNegativeZeroCap
