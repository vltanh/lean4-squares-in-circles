module

public import SquaresInCircles.Eight.TableFree.CrossedClampInverse
public import SquaresInCircles.Eight.TableFree.CrossedClampData

/-!
# Original-contact majorization and actual inverse-circle realization

Uncompiled source draft.  Rotating the original G corner shows that its
transverse corner is at least the explicit inverse cap.  The aligned GA
contact therefore places the original A transverse corner below the A
cap.  Conversely the inverse circle point realizes HG0 exactly at every
time of the proposed clamp, with the original H fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedClampInverse

theorem radius_eq {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    Real.sqrt (q-(D q b r)^2)=X q b r := by
  rw [show q-(D q b r)^2=(X q b r)^2 by nlinarith [norm S hr]]
  exact Real.sqrt_sq (X_pos S hr).le

theorem point_primary {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    (point q b r).a=X q b r-1/2 := by
  have hd := D_bounds S hr
  have hy : |1/2-D q b r|+1/2=D q b r := by
    rw [abs_of_nonpos (by linarith [hd.1] : 1/2-D q b r≤0)]
    ring
  simp only [point,SignedPoint.outerAt,hy,radius_eq S hr]

theorem point_transverse (q b r : ℝ) : 1/2-(point q b r).y=D q b r := by
  dsimp [point,SignedPoint.outerAt]
  ring

theorem point_properties {q r : ℝ} {H : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25)) :
    (point q H.y r).Sorted ∧ (point q H.y r).AvoidsCore ∧
      (point q H.y r).Contained q ∧ (point q H.y r).y≤0 ∧
      zeroFeasible H (point q H.y r) r 0 := by
  have hd := D_bounds S hr
  have hy : 1/2-D q H.y r≤0 := by linarith [hd.1]
  have hdiag : |1/2-D q H.y r|≤diagonalCoordinate q := by
    rw [abs_of_nonpos hy]
    linarith [hd.2,(uniform_circle_reserves S.floor S.ceiling).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec S.floor hdiag
  refine ⟨hGs,hGc,hGq.le,hy,?_⟩
  have hp := point_primary S hr
  have hc := contact q H.y r
  rw [zeroFeasible,edgeWidth_positive_formula (trig hr).1]
  simp only [zeroProjection,Matrix.cons_val_zero,hp]
  change (1+Real.cos r+Real.sin r)/2≤
    H.y+(X q H.y r-1/2)*Real.sin r-(1/2-D q H.y r)*Real.cos r
  dsimp [M] at hc
  nlinarith

theorem original_transverse_lower {q r : ℝ} {H G : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (hHG : zeroFeasible H G r 0) : D q H.y r≤1/2-G.y := by
  let P := (G.a+1/2)*Real.sin r+(1/2-G.y)*Real.cos r
  let R := (G.a+1/2)*Real.cos r-(1/2-G.y)*Real.sin r
  have ht := transport_trig (trig hr).1
  have hsort : 1/2-G.y≤G.a+1/2 := by
    have hh := hGs.2
    rw [abs_of_nonpos hGy] at hh
    linarith
  have hR0 : 0≤R := by
    have hp := mul_nonneg (show 0≤G.a+G.y by linarith)
      (show 0≤Real.cos r by linarith [ht.1])
    have hq := mul_nonneg (show 0≤1/2-G.y by linarith)
      (show 0≤Real.cos r-Real.sin r by linarith [ht.2.2.2.2])
    dsimp [R]
    nlinarith
  have hP : M H.y r≤P := by
    rw [zeroFeasible,edgeWidth_positive_formula (trig hr).1] at hHG
    simp only [zeroProjection,Matrix.cons_val_zero] at hHG
    dsimp [M,P]
    linarith
  have hrot : P^2+R^2=G.circle := by
    dsimp [P,R,SignedPoint.circle]
    rw [abs_of_nonpos hGy]
    linear_combination (((G.a+1/2)^2+(1/2-G.y)^2)*Real.sin_sq_add_cos_sq r)
  have hP2 := pow_le_pow_left₀ (show 0≤M H.y r by linarith [(M_bounds S hr).1]) hP 2
  have hw := W_bounds S hr
  have hc : G.circle≤q := hGq
  have hRW2 : R^2≤(W q H.y r)^2 := by rw [hw.2]; linarith
  have hR : R≤W q H.y r := le_of_pow_le_pow_left₀ (by norm_num) (by linarith [hw.1.1]) hRW2
  have hback : P*Real.cos r-R*Real.sin r=1/2-G.y := by
    dsimp [P,R]
    linear_combination (1/2-G.y)*Real.sin_sq_add_cos_sq r
  have hPc := mul_le_mul_of_nonneg_right hP (show 0≤Real.cos r by linarith [ht.1])
  have hRs := mul_le_mul_of_nonneg_right hR ht.2.2.1
  dsimp [D]
  linarith

theorem original_middle_cap {q r : ℝ} {H G A : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (hAq : A.Contained q) (hAy : 0≤A.y)
    (hHG : zeroFeasible H G r 0) (hGA : quarterFeasible G A 0 0) :
    A.y+1/2≤cap q H.y r := by
  have hd := original_transverse_lower S hr hGs hGq hGy hHG
  have hga : 1≤G.y+A.a := by simpa [quarterFeasible,quarterProjection] using hGA
  have hprimary : D q H.y r+1≤A.a+1/2 := by linarith
  have hp2 := pow_le_pow_left₀ (show 0≤D q H.y r+1 by linarith [(D_bounds S hr).1]) hprimary 2
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAq
  have hc := cap_bounds S hr
  nlinarith [hc.1,hc.2.2.2]

theorem realize {q r u : ℝ} {H T : SignedPoint}
    (S : Domain q H.y) (hr : r∈Icc (0:ℝ) (1/25))
    (hB : MiddleHardCap.Feasible q (1/2+T.y)) (hu : u∈Icc 0 frameCap)
    (hLB : 1/2≤HardSplitCap.cap q (1/2+T.y) u)
    (hsum : 2<cap q H.y r+HardSplitCap.cap q (1/2+T.y) u) :
    Nonempty (CrossedClampData q H T r u) := by
  obtain ⟨hGs,hGc,hGq,hGy,hHG⟩ := point_properties S hr
  have hA : MiddleHardCap.Feasible q (1/2-(point q H.y r).y) := by
    rw [point_transverse]
    exact feasible S hr
  have hLA : 1/2≤HardSplitCap.cap q (1/2-(point q H.y r).y) 0 := by
    rw [point_transverse,←cap_eq_hard_cap]
    linarith [(cap_bounds S hr).1]
  have hsum' : 2<HardSplitCap.cap q (1/2-(point q H.y r).y) 0+
      HardSplitCap.cap q (1/2+T.y) u := by
    rwa [point_transverse,←cap_eq_hard_cap]
  obtain ⟨O,_⟩ := CrossedClampConstruction.actual_data_of_caps
    hGs hGc hGq hGy hHG hA hB hu hLA hLB hsum'
  exact ⟨O⟩

end SquaresInCircles.Eight.TableFree.CrossedClampInverse
