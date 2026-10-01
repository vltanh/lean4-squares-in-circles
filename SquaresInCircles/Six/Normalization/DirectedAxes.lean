import SquaresInCircles.Six.Normalization.Basic

/-!
# Directed axes of a pair of squares

Two squares S and T with disjoint interiors are separated along one of the
eight directed axes `±e₁`, `±e₂` of the pair (`directed_pair_separator`). Along
each of them the half-widths of S and T add up to the separating-axis threshold
of the pair. So an axis along which the centre difference reaches the threshold
separates the open squares, and every chord from a point of S to a point of T
has a positive projection on it. Conversely, if the four axes of the pair,
directed by a table of signs, all have positive projection on such a chord,
then one of them separates the squares.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- The eight directed axes of a pair of squares: each frame axis of `S` and of
`T`, in both directions. -/
def pairNormal (i : Fin 8) (S T : UnitSquare) : Point :=
  ![normalX S,scale (-1) (normalX S),normalY S,scale (-1) (normalY S),
    normalX T,scale (-1) (normalX T),normalY T,scale (-1) (normalY T)] i

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

lemma threshold_symm (S T : UnitSquare) : SAT.threshold S T=SAT.threshold T S := by
  rw [SAT.threshold,SAT.threshold,relativeC_symm S T,
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

lemma pairNormal_ne (S T : UnitSquare) (i : Fin 8) : pairNormal i S T ≠ (0,0) := by
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
    width S (pairNormal i S T)+width T (pairNormal i S T)=
      SAT.threshold S T := by
  have hS : width S (normalX S)+width T (normalX S)=SAT.threshold S T := by
    rw [self_width_normalX,cross_width_normalX,SAT.threshold]
    ring
  have hSY : width S (normalY S)+width T (normalY S)=SAT.threshold S T := by
    rw [self_width_normalY,cross_width_normalY,SAT.threshold]
    ring
  have hT : width S (normalX T)+width T (normalX T)=SAT.threshold S T := by
    rw [self_width_normalX,cross_width_normalX,threshold_symm,SAT.threshold]
    ring
  have hTY : width S (normalY T)+width T (normalY T)=SAT.threshold S T := by
    rw [self_width_normalY,cross_width_normalY,threshold_symm,SAT.threshold]
    ring
  fin_cases i
  · exact hS
  · show width S (scale (-1) (normalX S))+width T (scale (-1) (normalX S))=_
    rw [width_neg,width_neg]
    exact hS
  · exact hSY
  · show width S (scale (-1) (normalY S))+width T (scale (-1) (normalY S))=_
    rw [width_neg,width_neg]
    exact hSY
  · exact hT
  · show width S (scale (-1) (normalX T))+width T (scale (-1) (normalX T))=_
    rw [width_neg,width_neg]
    exact hT
  · exact hTY
  · show width S (scale (-1) (normalY T))+width T (scale (-1) (normalY T))=_
    rw [width_neg,width_neg]
    exact hTY

/-- A separating directed axis has a positive inner product with every chord from
a point of the open square S to a point of the open square T. -/
theorem axis_points_to_pin (S T : UnitSquare) {p q : Point}
    (hp : openSquare S p) (hq : openSquare T q) (i : Fin 8)
    (hsep : SAT.threshold S T ≤
      dot (pairNormal i S T) (sub T.center S.center)) :
    0 < dot (pairNormal i S T) (sub q p) := by
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

/-- The four axes of a pair: the two axes of `S`, then those of `T`. -/
def unsignedPairAxis (S T : UnitSquare) (i : Fin 4) : Point :=
  ![normalX S,normalY S,normalX T,normalY T] i

/-- The axes of the pair, negated where `sign` is false. -/
def preferredPairAxis (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) : Point :=
  if sign i then unsignedPairAxis S T i else scale (-1) (unsignedPairAxis S T i)

lemma preferred_is_pairNormal (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) :
    ∃ j : Fin 8, preferredPairAxis sign S T i=pairNormal j S T := by
  fin_cases i
  · by_cases h : sign 0=true
    · exact ⟨0,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
    · exact ⟨1,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
  · by_cases h : sign 1=true
    · exact ⟨2,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
    · exact ⟨3,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
  · by_cases h : sign 2=true
    · exact ⟨4,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
    · exact ⟨5,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
  · by_cases h : sign 3=true
    · exact ⟨6,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩
    · exact ⟨7,by simp [preferredPairAxis,unsignedPairAxis,pairNormal,h]⟩

lemma preferred_abs_dot (sign : Fin 4 → Bool) (S T : UnitSquare) (i : Fin 4) (v : Point) :
    |dot (preferredPairAxis sign S T i) v|=|dot (unsignedPairAxis S T i) v| := by
  unfold preferredPairAxis
  split_ifs <;> simp only [dot_scale_neg,abs_neg]

lemma unsigned_separators_complete (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    ∃ i : Fin 4, SAT.threshold S T ≤
      |dot (unsignedPairAxis S T i) (sub T.center S.center)| := by
  have h := SAT.separating_axes S T hd
  rcases h with h | h | h | h
  · exact ⟨0,by simpa [unsignedPairAxis,normalX,frameX,dot] using h⟩
  · exact ⟨1,by simpa [unsignedPairAxis,normalY,frameY,dot] using h⟩
  · exact ⟨2,by simpa [unsignedPairAxis,normalX,frameX,dot] using h⟩
  · exact ⟨3,by simpa [unsignedPairAxis,normalY,frameY,dot] using h⟩

/-- Two squares with disjoint interiors are separated along one of the eight
directed axes of the pair. -/
lemma directed_pair_separator (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    ∃ i : Fin 8, SAT.threshold S T ≤ dot (pairNormal i S T) (sub T.center S.center) := by
  obtain ⟨i,hi⟩ := unsigned_separators_complete S T hd
  rcases le_abs'.mp hi with h | h
  · obtain ⟨j,hj⟩ := preferred_is_pairNormal (fun _ => false) S T i
    refine ⟨j,?_⟩
    simp only [← hj,preferredPairAxis,Bool.false_eq_true,ite_false,dot_scale_neg]
    linarith
  · obtain ⟨j,hj⟩ := preferred_is_pairNormal (fun _ => true) S T i
    exact ⟨j,by simpa only [← hj,preferredPairAxis,ite_true] using h⟩

/-- If every directed axis has positive projection on `q - p`, with `p` in the
first open square and `q` in the second, one of them separates the squares. -/
theorem preferred_separators_complete (sign : Fin 4 → Bool) (S T : UnitSquare)
    {p q : Point} (hp : openSquare S p) (hq : openSquare T q)
    (hpos : ∀ i, 0 < dot (preferredPairAxis sign S T i) (sub q p))
    (hd : ∀ z, ¬ (openSquare S z ∧ openSquare T z)) :
    ∃ i : Fin 4, SAT.threshold S T ≤
      dot (preferredPairAxis sign S T i) (sub T.center S.center) := by
  obtain ⟨i,hi⟩ := unsigned_separators_complete S T hd
  obtain ⟨j,hj⟩ := preferred_is_pairNormal sign S T i
  have hn : preferredPairAxis sign S T i≠(0,0) := by rw [hj]; exact pairNormal_ne S T j
  have hw : width S (preferredPairAxis sign S T i)+width T (preferredPairAxis sign S T i)=
      SAT.threshold S T := by rw [hj]; exact pairNormal_widths S T j
  have h := orient_axis_from_pins hn hp hq (hpos i)
    (by rw [hw,preferred_abs_dot]; exact hi)
  exact ⟨i,by simpa only [hw] using h⟩

end SquaresInCircles.Six
