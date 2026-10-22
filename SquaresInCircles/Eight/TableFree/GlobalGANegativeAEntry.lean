module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedASource
public import SquaresInCircles.Eight.TableFree.NegativePrimaryEntry

/-!
# The actual negative A-primary entry alternatives

Uncompiled transcription of `HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md`.
All secondary replacements are at the unchanged states and frames. The
quarter-primary comparison uses the already transcribed reflected corner
argument. Its zero-primary counterpart keeps the common original radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA
open Candidate Secondary

/-- The whole sorted outer arc lies above this endpoint chord. The
factorization is the two original circle equations at the same radius. -/
theorem outer_diagonal_chord {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (ho : P.Outer q) (hq : q≤qCap) :
    (7/5)*diagonalCoordinate q≤P.a+(2/5)*|P.y| := by
  let d := diagonalCoordinate q
  have hb := SignedPoint.outer_bounds hs ho
  have hd0 : 0≤d := (abs_nonneg P.y).trans hb.2.1
  have ha := GlobalGA.primary_upper hs ho.le hq
  have hq0 : 0≤q := by rw [← ho]; exact P.circle_nonneg
  have hroot := Real.sq_sqrt (show 0≤q/2 by positivity)
  have hdiag : 2*(d+1/2)^2=q := by dsimp [d,diagonalCoordinate]; nlinarith
  have hcircle := ho
  dsimp [SignedPoint.Outer,SignedPoint.circle] at hcircle
  have hid : (P.a-d)*(P.a+d+1)=(d-|P.y|)*(d+|P.y|+1) := by
    nlinarith only [hdiag,hcircle]
  have hcoeff : 0≤d+|P.y|+1-(2/5)*(P.a+d+1) := by
    linarith [abs_nonneg P.y]
  have hm := mul_nonneg (sub_nonneg.mpr hb.2.1) hcoeff
  have hprod : 0≤(P.a-d-(2/5)*(d-|P.y|))*(P.a+d+1) := by
    nlinarith only [hid,hm]
  have hden : 0<P.a+d+1 := by linarith [hs.1]
  have hh := (mul_nonneg_iff_of_pos_right hden).1 hprod
  change (7/5)*d≤P.a+(2/5)*|P.y|
  linarith

theorem sorted_diagonal_support {q f g : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hf : 0≤f) (hfg : f≤g) :
    f*P.a+g*|P.y|≤diagonalCoordinate q*(f+g) := by
  let d := diagonalCoordinate q
  have hq0 : 0≤q := P.circle_nonneg.trans hc
  have hr := Real.sq_sqrt (show 0≤q/2 by positivity)
  have hr0 := Real.sqrt_nonneg (q/2)
  have hcircle := hc
  dsimp [SignedPoint.Contained,SignedPoint.circle] at hcircle
  have hsum : P.a+|P.y|≤2*d := by
    dsimp [d,diagonalCoordinate]
    nlinarith [sq_nonneg (P.a-|P.y|),hs.1,abs_nonneg P.y]
  have h₁ := mul_nonneg (sub_nonneg.mpr hfg) (sub_nonneg.mpr hs.2)
  have h₂ := mul_le_mul_of_nonneg_left hsum (show 0≤f+g by linarith)
  change f*P.a+g*|P.y|≤d*(f+g)
  nlinarith only [h₁,h₂]

theorem nonpositive_outer_GA_secondary {q s : ℝ} {G A : SignedPoint}
    (hGs : G.Sorted) (hGc : G.Contained q) (hAs : A.Sorted) (hAo : A.Outer q)
    (hq : q≤qCap) (hGy : G.y≤0) (hAy : A.y≤0)
    (hs : s∈Icc 0 frameCap) (hGA : quarterFeasible G A (-s) 3) :
    quarterFeasible G A (-s) 2 := by
  have ht := transport_trig hs
  have hf : 0≤1-Real.cos s := sub_nonneg.mpr (Real.cos_le_one s)
  have hdrop := PositiveANegativeTD.one_sub_cos_upper hs
  have hsource := sorted_diagonal_support hGs hGc hf
    (show 1-Real.cos s≤Real.sin s by linarith [ht.2.2.1])
  have htarget := outer_diagonal_chord hAs hAo hq
  have hb := (SignedPoint.outer_bounds hAs hAo).2.1
  have h₁ := mul_le_mul_of_nonneg_right htarget ht.2.2.1
  have h₂ := mul_nonneg (sub_nonneg.mpr hb)
    (show 0≤(2/5)*Real.sin s-(1-Real.cos s) by linarith [ht.2.2.1])
  have hcomparison : G.a-A.a*Real.sin s+|A.y|*Real.cos s≤
      G.a*Real.cos s-|G.y|*Real.sin s+|A.y| := by
    nlinarith only [hsource,h₁,h₂]
  have hp : edgeWidth (-s)≤G.a-A.a*Real.sin s+|A.y|*Real.cos s := by
    simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg,
      abs_of_nonpos hAy] using hGA
  have hh := hp.trans hcomparison
  simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg,
    abs_of_nonpos hAy,abs_of_nonpos hGy] using hh

/-- The high-primary exceptional branch is the reflected original
negative-quarter comparison, including its sharper one-quarter cut. -/
theorem GA_entry {q s : ℝ} {G A : SignedPoint}
    (hGs : G.Sorted) (hGc : G.Contained q) (hAs : A.Sorted) (hAb : A.Boundary q)
    (hq : q≤qCap) (hGy : G.y≤0) (hAouter : A.y≤0 → A.Outer q)
    (hs : s∈Ioc 0 frameCap) (hGA : quarterFeasible G A (-s) 3) :
    quarterFeasible G A (-s) 2 ∨
      (A.a=7/12 ∧ 0<A.y ∧ A.y<39/250 ∧ s<1/4) := by
  by_cases hsecondary : quarterFeasible G A (-s) 2
  · exact Or.inl hsecondary
  right
  have hAy : 0<A.y := by
    by_contra! hh
    exact hsecondary (nonpositive_outer_GA_secondary hGs hGc hAs (hAouter hh)
      hq hGy hh ⟨hs.1.le,hs.2⟩ hGA)
  have hprimary : quarterFeasible A.reflect G.reflect (-s) 1 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect G A (-s) 3).2 hGA
  have hnot : ¬quarterFeasible A.reflect G.reflect (-s) 0 := by
    intro hh
    exact hsecondary ((quarterFeasible_reflect G A (-s) 2).1
      (by simpa [reflectedOwner] using hh))
  have hh := exceptional_negative_primary_cuts
    (G:=A.reflect) (A:=G.reflect) (by simpa using hAs) (by simpa using hGs)
    (by simpa using hAb) (by simpa using hGc) hq
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hAy.le)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    ⟨hs.1,hs.2⟩ hprimary hnot
  exact ⟨by simpa [SignedPoint.reflect] using hh.1,hAy,
    by simpa [SignedPoint.reflect,abs_of_pos hAy] using hh.2.1,hh.2.2.1⟩

theorem AB_positive_tangent {q s : ℝ} {A B : SignedPoint}
    (hAs : A.Sorted) (hBs : B.Sorted) (hBc : B.Contained q) (hq : q≤qCap)
    (hBy : B.y≤0) (hs : s∈Ioc 0 frameCap) (hAB : zeroFeasible A B (-s) 2) :
    0<A.y := by
  have hB := actual_coordinate_bounds (P:=B.reflect) (by simpa using hBs)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hBc) hq
  have ht := transport_trig ⟨hs.1.le,hs.2⟩
  have hp : edgeWidth (-s)≤ -A.a*Real.sin s+A.y*Real.cos s-B.y := by
    simpa [zeroFeasible,zeroProjection,Real.sin_neg,Real.cos_neg] using hAB
  by_contra! hh
  have h₁ := mul_nonneg hAs.1.le ht.2.2.1
  have h₂ := mul_nonpos_of_nonpos_of_nonneg hh (by linarith [ht.1] : 0≤Real.cos s)
  have hw := edgeWidth_ge_one (-s)
  dsimp [SignedPoint.reflect] at hB
  linarith [hB.2.1,diagonal_bounds.2]

theorem outer_AB_secondary {q s : ℝ} {A B : SignedPoint}
    (hAs : A.Sorted) (hAo : A.Outer q) (hBs : B.Sorted) (hBo : B.Outer q)
    (hq : q≤qCap) (hAy : 0<A.y ∧ A.y<1/2) (hBy : B.y≤0)
    (hs : s∈Ioc 0 frameCap) (hAB : zeroFeasible A B (-s) 2) :
    zeroFeasible A B (-s) 0 := by
  have ht := transport_trig ⟨hs.1.le,hs.2⟩
  have hsin : 0<Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs.1
    (by dsimp [frameCap] at hs; linarith [hs.2,Real.pi_gt_three])
  have hp : edgeWidth (-s)≤ -A.a*Real.sin s+A.y*Real.cos s-B.y := by
    simpa [zeroFeasible,zeroProjection,Real.sin_neg,Real.cos_neg] using hAB
  have hcoscost := mul_nonneg hAy.1.le (sub_nonneg.mpr (Real.cos_le_one s))
  have hstrict := mul_pos hAs.1 hsin
  have hsum : 1<A.y-B.y := by linarith [edgeWidth_ge_one (-s)]
  have hdiff : 0< -B.y-A.y := by linarith [hAy.2]
  have hAc := hAo
  have hBc := hBo
  simp only [SignedPoint.Outer,SignedPoint.circle,abs_of_pos hAy.1] at hAc
  simp only [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hBy] at hBc
  have hid : (A.a-B.a)*(A.a+B.a+1)=(-B.y-A.y)*(A.y-B.y+1) := by
    nlinarith only [hAc,hBc]
  have hden : 0<A.a+B.a+1 := by linarith [hAs.1,hBs.1]
  have hprod : 0<(A.a-B.a)*(A.a+B.a+1) := by
    rw [hid]
    exact mul_pos hdiff (by linarith)
  have hadiff : 0<A.a-B.a := (mul_pos_iff_of_pos_right hden).1 hprod
  have hdenup : A.a+B.a+1≤383/100 := by
    linarith [GlobalGA.primary_upper hAs hAo.le hq,GlobalGA.primary_upper hBs hBo.le hq]
  have hmul := mul_le_mul_of_nonneg_left hdenup hadiff.le
  have hstrict2 := mul_pos hdiff (show 0<A.y-B.y-1 by linarith)
  have hratio : (183/500)*(-B.y-A.y)<A.a-B.a := by
    nlinarith only [hid,hmul,hstrict2,hdiff]
  have hdrop := PositiveANegativeTD.one_sub_cos_upper ⟨hs.1.le,hs.2⟩
  have hdropmul := mul_le_mul_of_nonneg_left hdrop hdiff.le
  have hreserve := mul_pos (sub_pos.mpr hratio) hsin
  have hcompare : -A.a*Real.sin s+A.y*Real.cos s-B.y≤
      A.y-B.a*Real.sin s-B.y*Real.cos s := by
    nlinarith only [hdropmul,hreserve]
  simpa [zeroFeasible,zeroProjection,Real.sin_neg,Real.cos_neg] using hp.trans hcompare

theorem AB_entry {q s : ℝ} {A B : SignedPoint}
    (hAs : A.Sorted) (hAb : A.Boundary q) (hBs : B.Sorted) (hBo : B.Outer q)
    (hq : q≤qCap) (hAy : A.y<1/2) (hBy : B.y≤0)
    (hs : s∈Ioc 0 frameCap) (hAB : zeroFeasible A B (-s) 2) :
    zeroFeasible A B (-s) 0 ∨
      (A.a=7/12 ∧ 0<A.y ∧ A.y<1/2 ∧ s<19/50) := by
  have hpos := AB_positive_tangent hAs hBs hBo.le hq hBy hs hAB
  rcases hAb with hAo | hAc
  · exact Or.inl (outer_AB_secondary hAs hAo hBs hBo hq ⟨hpos,hAy⟩ hBy hs hAB)
  right
  have ha : A.a=7/12 := (SignedPoint.flat_core_iff hAs
    (by rw [abs_of_pos hpos]; exact hAy.le)).1 hAc
  have hB := actual_coordinate_bounds (P:=B.reflect) (by simpa using hBs)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hBo.le) hq
  have ht := transport_trig ⟨hs.1.le,hs.2⟩
  have hp : (1+Real.cos s+Real.sin s)/2≤
      -(7/12)*Real.sin s+A.y*Real.cos s-B.y := by
    simpa [zeroFeasible,zeroProjection,Real.sin_neg,Real.cos_neg,
      edgeWidth_negative_formula ⟨hs.1.le,hs.2⟩,ha] using hAB
  have hcost := mul_nonneg (show 0≤1/2-A.y by linarith) (by linarith [ht.1] : 0≤Real.cos s)
  have hsin : Real.sin s<24/65 := by
    dsimp [SignedPoint.reflect] at hB
    linarith [hB.2.1,diagonal_bounds.2]
  have hcut : s<19/50 := by
    by_contra! hh
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2)≤(19/50:ℝ) by linarith [Real.pi_pos])
      (show s≤Real.pi/2 by dsimp [frameCap] at hs; linarith [hs.2,Real.pi_gt_three]) hh
    have htaylor := Real.sin_ge_sub_cube (show (0:ℝ)≤19/50 by norm_num)
    norm_num at htaylor
    linarith
  exact ⟨ha,hpos,hAy,hcut⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA
