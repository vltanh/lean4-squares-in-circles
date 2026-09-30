module
public import SquaresInCircles.Six.Normalization.ActualMarkers

@[expose] public section

/-!
# Side-nearestness as an actual point-set statement

N17's numerical transverse bound is connected here to the geometric nearest
point, rather than merely described in a comment. The foot has first local
coordinate -1/2 and transverse coordinate strictly between the edge endpoints.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

def nearFoot (t a : ℝ) : Point := ((a-1/2)*Real.cos t,(a-1/2)*Real.sin t)

lemma nearFoot_localX (t a b : ℝ) : localX (orientedSquare t a b) (nearFoot t a) = -1/2 := by
  rw [orientedSquare_localX]
  dsimp [nearFoot]
  linear_combination (a-1/2)*(Real.sin_sq_add_cos_sq t)

lemma nearFoot_localY (t a b : ℝ) : localY (orientedSquare t a b) (nearFoot t a) = -b := by
  rw [orientedSquare_localY]
  dsimp [nearFoot]
  ring

lemma nearFoot_normSq (t a : ℝ) : normSq (nearFoot t a)=(a-1/2)^2 := by
  dsimp [normSq,nearFoot]
  linear_combination (a-1/2)^2*(Real.sin_sq_add_cos_sq t)

lemma localX_frame_origin (t a b : ℝ) (p : Point) :
    localX (orientedSquare t a b) p = frameX (orientedSquare t a b) p-a := by
  simp only [orientedSquare_localX,frameX,orientedSquare]
  ring

/-- The point realizing minimum distance is strictly inside the near edge. -/
theorem side_nearest {t a b : ℝ} (ha : 1/2 ≤ a) (hb : |b| < 1/2) :
    closedSquare (orientedSquare t a b) (nearFoot t a) ∧
      localX (orientedSquare t a b) (nearFoot t a) = -1/2 ∧
      |localY (orientedSquare t a b) (nearFoot t a)| < 1/2 ∧
      (∀ p, closedSquare (orientedSquare t a b) p →
        normSq (nearFoot t a) ≤ normSq p) := by
  have hx := nearFoot_localX t a b
  have hy := nearFoot_localY t a b
  refine ⟨?_,hx,?_,?_⟩
  · constructor
    · rw [hx]
      norm_num
    · simpa only [hy,abs_neg] using hb.le
  · simpa only [hy,abs_neg] using hb
  · intro p hp
    have hlow := (abs_le.mp hp.1).1
    rw [localX_frame_origin] at hlow
    have hq : 0 ≤ a-1/2 := by linarith
    have hpq : a-1/2 ≤ frameX (orientedSquare t a b) p := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hpq)
      (show 0 ≤ frameX (orientedSquare t a b) p+(a-1/2) by linarith)
    have hnorm := frame_norm (orientedSquare t a b) p
    rw [nearFoot_normSq]
    nlinarith [sq_nonneg (frameY (orientedSquare t a b) p)]

theorem PinPacking.side_nearest {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    closedSquare (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (nearFoot (P.phase i) (P.radial i)) ∧
      localX (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (nearFoot (P.phase i) (P.radial i)) = -1/2 ∧
      |localY (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
        (nearFoot (P.phase i) (P.radial i))| < 1/2 ∧
      (∀ p, closedSquare (orientedSquare (P.phase i) (P.radial i) (P.transverse i)) p →
        normSq (nearFoot (P.phase i) (P.radial i)) ≤ normSq p) :=
  Normalization.side_nearest (P.contained i).half_le
    ((P.contained i).u_lt_half (P.avoidsCore i))

end SquaresInCircles.Six.Normalization
