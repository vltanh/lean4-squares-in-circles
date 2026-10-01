import SquaresInCircles.Six.Stress.Reverse

/-!
# Directed axes of a pair of squares

Along each of the eight directed axes `±e₁`, `±e₂` of two squares S and T, the
half-widths of S and T add up to the separating-axis threshold of the pair. So
an axis along which the centre difference reaches the threshold separates the
open squares, and every chord from a point of S to a point of T has a positive
projection on it. Conversely, a chord with a positive projection directs an
undirected separation along the axis.
-/

noncomputable section
namespace SquaresInCircles.Six

lemma width_scale_neg (S : UnitSquare) (v : Point) :
    width S (scale (-1) v)=width S v := by
  have hx : frameX S (scale (-1) v)=-frameX S v := by dsimp [frameX,scale]; ring
  have hy : frameY S (scale (-1) v)=-frameY S v := by dsimp [frameY,scale]; ring
  simp only [width,hx,hy,abs_neg]

lemma dot_scale_neg (v p : Point) : dot (scale (-1) v) p = -dot v p := by
  dsimp [dot,scale]
  ring

lemma normalX_norm (S : UnitSquare) : normSq (normalX S)=1 := by
  simpa [normSq,normalX] using S.unit

lemma normalY_norm (S : UnitSquare) : normSq (normalY S)=1 := by
  simpa [normSq,normalY,add_comm] using S.unit

lemma normalX_ne (S : UnitSquare) : normalX S ≠ (0,0) := by
  intro h
  have hh := normalX_norm S
  rw [h] at hh
  norm_num [normSq] at hh

lemma normalY_ne (S : UnitSquare) : normalY S ≠ (0,0) := by
  intro h
  have hh := normalY_norm S
  rw [h] at hh
  norm_num [normSq] at hh

lemma neg_normal_ne {v : Point} (hv : v ≠ (0,0)) : scale (-1) v ≠ (0,0) := by
  intro h
  apply hv
  apply Prod.ext
  · have hh := congrArg Prod.fst h
    dsimp [scale] at hh
    linarith
  · have hh := congrArg Prod.snd h
    dsimp [scale] at hh
    linarith

lemma relativeC_symm (S T : UnitSquare) : relativeC S T=relativeC T S := by
  dsimp [relativeC]
  ring

lemma relativeS_antisymm (S T : UnitSquare) : relativeS S T= -relativeS T S := by
  dsimp [relativeS]
  ring

lemma threshold_symm (S T : UnitSquare) : Seven.SAT.threshold S T=Seven.SAT.threshold T S := by
  rw [Seven.SAT.threshold,Seven.SAT.threshold,relativeC_symm S T,
    relativeS_antisymm S T,abs_neg]

lemma self_width_normalX (S : UnitSquare) : width S (normalX S)=1/2 := by
  have hx : frameX S (normalX S)=1 := by
    dsimp [frameX,normalX]
    linear_combination S.unit
  have hy : frameY S (normalX S)=0 := by dsimp [frameY,normalX]; ring
  norm_num [width,hx,hy]

lemma self_width_normalY (S : UnitSquare) : width S (normalY S)=1/2 := by
  have hx : frameX S (normalY S)=0 := by dsimp [frameX,normalY]; ring
  have hy : frameY S (normalY S)=1 := by
    dsimp [frameY,normalY]
    nlinarith [S.unit]
  norm_num [width,hx,hy]

lemma cross_width_normalX (S T : UnitSquare) :
    width T (normalX S)=(|relativeC S T|+|relativeS S T|)/2 := by
  have hx : frameX T (normalX S)=relativeC S T := by dsimp [frameX,normalX,relativeC]; ring
  have hy : frameY T (normalX S)= -relativeS S T := by dsimp [frameY,normalX,relativeS]; ring
  simp only [width,hx,hy,abs_neg]

lemma cross_width_normalY (S T : UnitSquare) :
    width T (normalY S)=(|relativeC S T|+|relativeS S T|)/2 := by
  have hx : frameX T (normalY S)=relativeS S T := by dsimp [frameX,normalY,relativeS]; ring
  have hy : frameY T (normalY S)=relativeC S T := by dsimp [frameY,normalY,relativeC]; ring
  simp only [width,hx,hy]
  ring

lemma pairNormal_ne (S T : UnitSquare) (i : Fin 8) : Stress.pairNormal i S T ≠ (0,0) := by
  fin_cases i
  · exact normalX_ne S
  · exact neg_normal_ne (normalX_ne S)
  · exact normalY_ne S
  · exact neg_normal_ne (normalY_ne S)
  · exact normalX_ne T
  · exact neg_normal_ne (normalX_ne T)
  · exact normalY_ne T
  · exact neg_normal_ne (normalY_ne T)

/-- Along each directed axis of the pair, the two half-widths add up to the
threshold. -/
lemma pairNormal_widths (S T : UnitSquare) (i : Fin 8) :
    width S (Stress.pairNormal i S T)+width T (Stress.pairNormal i S T)=
      Seven.SAT.threshold S T := by
  have hS : width S (normalX S)+width T (normalX S)=Seven.SAT.threshold S T := by
    rw [self_width_normalX,cross_width_normalX,Seven.SAT.threshold]
    ring
  have hSY : width S (normalY S)+width T (normalY S)=Seven.SAT.threshold S T := by
    rw [self_width_normalY,cross_width_normalY,Seven.SAT.threshold]
    ring
  have hT : width S (normalX T)+width T (normalX T)=Seven.SAT.threshold S T := by
    rw [self_width_normalX,cross_width_normalX,threshold_symm,Seven.SAT.threshold]
    ring
  have hTY : width S (normalY T)+width T (normalY T)=Seven.SAT.threshold S T := by
    rw [self_width_normalY,cross_width_normalY,threshold_symm,Seven.SAT.threshold]
    ring
  fin_cases i
  · exact hS
  · show width S (scale (-1) (normalX S))+width T (scale (-1) (normalX S))=_
    rw [width_scale_neg,width_scale_neg]
    exact hS
  · exact hSY
  · show width S (scale (-1) (normalY S))+width T (scale (-1) (normalY S))=_
    rw [width_scale_neg,width_scale_neg]
    exact hSY
  · exact hT
  · show width S (scale (-1) (normalX T))+width T (scale (-1) (normalX T))=_
    rw [width_scale_neg,width_scale_neg]
    exact hT
  · exact hTY
  · show width S (scale (-1) (normalY T))+width T (scale (-1) (normalY T))=_
    rw [width_scale_neg,width_scale_neg]
    exact hTY

/-- A separating directed axis has a positive inner product with every chord from
a point of the open square S to a point of the open square T. -/
theorem selected_axis_points_to_pin (S T : UnitSquare) {p q : Point}
    (hp : openSquare S p) (hq : openSquare T q) (i : Fin 8)
    (hsep : Seven.SAT.threshold S T ≤
      dot (Stress.pairNormal i S T) (sub T.center S.center)) :
    0 < dot (Stress.pairNormal i S T) (sub q p) := by
  have h := separator_orients_pins (pairNormal_ne S T i) hp hq
    (by simpa only [pairNormal_widths] using hsep)
  rw [dot_sub_right]
  linarith

/-- A separation along `±n` is a separation along `n` if some chord from S to T
has a positive inner product with `n`. -/
lemma orient_axis_from_pins {S T : UnitSquare} {n p q : Point}
    (hn : n≠(0,0)) (hp : openSquare S p) (hq : openSquare T q)
    (hchord : 0 < dot n (sub q p))
    (hsep : width S n+width T n ≤ |dot n (sub T.center S.center)|) :
    width S n+width T n ≤ dot n (sub T.center S.center) := by
  by_cases h : 0 ≤ dot n (sub T.center S.center)
  · simpa only [abs_of_nonneg h] using hsep
  · rw [abs_of_neg (lt_of_not_ge h),dot_sub_right] at hsep
    have hs := open_projection_bounds S hn hp
    have ht := open_projection_bounds T hn hq
    rw [dot_sub_right] at hchord
    linarith [hs.1,ht.2]

end SquaresInCircles.Six
