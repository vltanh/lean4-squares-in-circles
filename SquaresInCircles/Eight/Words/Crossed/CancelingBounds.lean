module

public import SquaresInCircles.Eight.Words.Crossed.CancelingScalar
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter
public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns

/-!
# Eight squares: three H captures and the signed opposite hard contact

A contrary H/G tangent order `H.y ≤ g` forces three rational captures (`contrary_captures`). The
unchanged opposite T may have either sign: the one-tenth capture `-1/10 < T.y` suffices to bound
its hard contact on the whole interval `[0,.32]` (`signed_opposite_bound`). The original TD/HDE
budget then contradicts the contrary order (`tangent_order`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedCancelingBounds
open CrossedCancelingScalar EndpointRotationPenalty EndpointBudgetScalars

theorem support_bound {H : SignedPoint} {c k h : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hc : c∈Icc (0:ℝ) (1/4)) (hk : 0≤k) (hy : H.y≤c)
    (hroot : qCap<(k+1)^2+(c+1/2)^2) (hh : h∈Icc 0 frameCap) :
    S H h≤k*Real.sin h+(c-1/2)*Real.cos h := by
  let J := SignedPoint.outerAt qCap c
  have hqL : qLow≤qCap := by norm_num [qLow,qCap]
  have hcdiag : |c|≤diagonalCoordinate qCap := by
    rw [abs_of_nonneg hc.1]
    linarith [(uniform_circle_reserves hqL le_rfl).1,hc.2]
  obtain ⟨hJs,hJq,hJc⟩ := SignedPoint.outerAt_spec hqL hcdiag
  have hJy : J.y=c := rfl
  have hcircle : (J.a+1/2)^2+(c+1/2)^2=qCap := by
    have h1 : (J.a+1/2)^2+(|J.y|+1/2)^2=qCap := hJq
    rwa [hJy,abs_of_nonneg hc.1] at h1
  have hJa : J.a-1/2≤k := by nlinarith [hJs.1]
  have hsupport := PositiveCancelingOuter.sorted_support_mono hHs hJs hHy
    (show 0≤J.y from hc.1) (hHq.trans_eq hJq.symm) hy hh
  have hsin := mul_le_mul_of_nonneg_right hJa (transport_trig hh).2.2.1
  dsimp [S]
  change H.a*Real.sin h+H.y*Real.cos h≤J.a*Real.sin h+c*Real.cos h at hsupport
  nlinarith

/-- These comparisons use H itself, also when it lies strictly inside `qCap`; only the support
upper bound is evaluated on the circle. -/
theorem contrary_captures {H : SignedPoint} {g r : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hg : g∈Icc (0:ℝ) (26/125)) (hr : r∈Icc 0 frameCap)
    (hHG : 1/2≤g+S H r) (hbad : H.y≤g) :
    37/250<H.y ∧ 33/50<r ∧ 37/200<g := by
  have htr := trig_seven_tenths hr
  have hH : 37/250<H.y := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 37/250) (k := 87/100) (by norm_num) (by norm_num) hn
      (by norm_num [qCap]) hr
    nlinarith [hg.2,htr.1,htr.2]
  have hr' : 33/50<r := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 26/125) (k := 106/125) (by norm_num) (by norm_num)
      (hbad.trans hg.2) (by norm_num [qCap]) hr
    have ht := trig_sixty_six (show r∈Icc 0 (33/50:ℝ) from ⟨hr.1,hn⟩)
    nlinarith [hg.2,ht.1,ht.2]
  have hg' : 37/200<g := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 37/200) (k := 857/1000) (by norm_num) (by norm_num)
      (hbad.trans hn) (by norm_num [qCap]) hr
    nlinarith [htr.1,htr.2]
  exact ⟨hH,hr',hg'⟩

/-- The signed opposite estimate needs only `t > -.1`. Its Taylor polynomial on the whole domain
has a negative quadratic part. -/
theorem signed_opposite_bound {t u : ℝ}
    (ht : -(1/10:ℝ)<t) (hu : u∈Icc 0 frameCap)
    (hcontact : t+1/2<(73/100)*Real.cos u-(481/500)*Real.sin u) :
    t+charge*u<47/200 := by
  have he : (8/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have href : (73/100)*Real.cos (8/25)-(481/500)*Real.sin (8/25)<(2/5:ℝ) := by
    have hc := cos_upper_four (show (0:ℝ)≤8/25 by norm_num)
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤8/25 by norm_num)
    norm_num at hc hs
    nlinarith
  have hshort : u<8/25 := by
    by_contra! hn
    have hc := CorrelatedSameBlock.cos_anti he hu hn
    have hs := CorrelatedSameBlock.sin_mono he hu hn
    nlinarith
  have hc := cos_upper_four hu.1
  have hs := Real.sin_ge_sub_cube hu.1
  have h2 := pow_le_pow_left₀ hu.1 hshort.le 2
  have h3 := mul_le_mul_of_nonneg_right hshort.le (sq_nonneg u)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg u)
  have hpoly : t+charge*u<23/100+(1431/24500)*u-(3/10)*u^2 := by
    dsimp [charge]
    nlinarith
  have hsq := sq_nonneg (u-477/4900)
  nlinarith

theorem opposite_contact_from_circles {A B T : SignedPoint} {g u : ℝ}
    (hAy : 0≤A.y) (hBy : B.y≤0) (hBa : 0<B.a)
    (hAq : A.Contained qCap) (hBq : B.Contained qCap)
    (hsum : A.y-B.y=1) (hg : 37/200<g) (hGA : g+1≤A.a)
    (hu : u∈Icc 0 frameCap) (hBT : quarterFeasible B T (-u) 2) :
    T.y+1/2<(73/100)*Real.cos u-(481/500)*Real.sin u := by
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAq
  have hBc : (B.a+1/2)^2+(-B.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hBy] using hBq
  have hAyU : A.y<269/500 := by
    dsimp [qCap] at hAc
    nlinarith
  have hByL : 481/500< -B.y+1/2 := by linarith
  have hBaU : B.a-1/2<73/100 := by
    dsimp [qCap] at hBc
    nlinarith
  have hBTref : quarterFeasible T.reflect B.reflect (-u) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-u) 2).2 hBT
  have hbound := SignedOppositeHardEnvelope.negative_hard_contact hu hBTref
  simp only [SignedPoint.reflect,neg_neg] at hbound
  have ht := transport_trig hu
  have hp := mul_lt_mul_of_pos_right hBaU (show 0<Real.cos u by linarith [ht.1])
  have hY := mul_le_mul_of_nonneg_right hByL.le ht.2.2.1
  nlinarith

/-- The unchanged opposite budget rules out `H.y ≤ g`. The opposite T needs no normal sign. -/
theorem tangent_order {H A B T : SignedPoint} {g r u : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hAy : 0≤A.y) (hBy : B.y≤0) (hBa : 0<B.a)
    (hAq : A.Contained qCap) (hBq : B.Contained qCap)
    (hsum : A.y-B.y=1) (hg : g∈Icc (0:ℝ) (26/125))
    (hr : r∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hHG : 1/2≤g+S H r) (hGA : g+1≤A.a)
    (hBT : quarterFeasible B T (-u) 2) (hT : -(1/10:ℝ)<T.y)
    (hbudget : H.y-T.y+charge*(r-u)<1-S0) : g<H.y := by
  by_contra! hbad
  obtain ⟨hH,hr',hg'⟩ := contrary_captures hHs hHy hHq hg hr hHG hbad
  have hc := opposite_contact_from_circles hAy hBy hBa hAq hBq hsum hg' hGA hu hBT
  have hb := signed_opposite_bound hT hu hc
  have hreserve := SignedOppositeHardEnvelope.budget_reserve
  dsimp [charge] at *
  nlinarith

end SquaresInCircles.Eight.CrossedCancelingBounds
