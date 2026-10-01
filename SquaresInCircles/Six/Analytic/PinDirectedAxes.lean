import SquaresInCircles.Six.Analytic.PairCoordinates

/-!
# Interior pins determine the direction of a separator

If p is in S and q is in T and n.p < n.q, the reverse direction of n cannot
separate the squares. The proof uses strict open-square projection bounds.
The two secondary-axis threshold identities then permit the same argument
on either square's own transverse axis.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma separator_forward_of_pin_order {S T : UnitSquare} {n p q : Point}
    (hn : n ≠ (0,0)) (hp : openSquare S p) (hq : openSquare T q)
    (horder : dot n p < dot n q)
    (hsep : width S n+width T n ≤ |dot n (sub T.center S.center)|) :
    width S n+width T n ≤ dot n (sub T.center S.center) := by
  by_cases hpos : 0 ≤ dot n (sub T.center S.center)
  · simpa only [abs_of_nonneg hpos] using hsep
  · rw [abs_of_neg (lt_of_not_ge hpos)] at hsep
    have hreverse : width T n+width S n ≤ dot n (sub S.center T.center) := by
      rw [dot_sub_right] at hsep ⊢
      linarith
    have hbad := Six.separator_orients_pins hn hq hp hreverse
    linarith

lemma normalY_ne_zero (S : UnitSquare) : normalY S ≠ (0,0) := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [normalY] at hx hy
  nlinarith [S.unit]

lemma dot_normalY (S : UnitSquare) (v : Point) : dot (normalY S) v=frameY S v := by
  dsimp [dot,normalY,frameY]

lemma threshold_secondary_left (S T : UnitSquare) :
    Seven.SAT.threshold S T = width S (normalY S)+width T (normalY S) := by
  have hxx : frameX S (normalY S)=0 := by dsimp [frameX,normalY]; ring
  have hxy : frameY S (normalY S)=1 := by dsimp [frameY,normalY]; nlinarith [S.unit]
  have hyx : frameX T (normalY S)=relativeS S T := by
    dsimp [frameX,normalY,relativeS]
    ring
  have hyy : frameY T (normalY S)=relativeC S T := by
    dsimp [frameY,normalY,relativeC]
    ring
  rw [width,width,hxx,hxy,hyx,hyy]
  simp only [abs_zero,abs_one,Seven.SAT.threshold]
  ring

lemma threshold_secondary_right (S T : UnitSquare) :
    Seven.SAT.threshold S T = width S (normalY T)+width T (normalY T) := by
  have hc : relativeC T S=relativeC S T := by dsimp [relativeC]; ring
  have hs : relativeS T S= -relativeS S T := by dsimp [relativeS]; ring
  have he : Seven.SAT.threshold T S=Seven.SAT.threshold S T := by
    simp only [Seven.SAT.threshold,hc,hs,abs_neg]
  rw [← he,threshold_secondary_left]
  ring

lemma left_secondary_forward {S T : UnitSquare} {p q : Point}
    (hp : openSquare S p) (hq : openSquare T q)
    (horder : dot (normalY S) p < dot (normalY S) q)
    (hsep : Seven.SAT.threshold S T ≤ |frameY S (sub T.center S.center)|) :
    Seven.SAT.threshold S T ≤ frameY S (sub T.center S.center) := by
  rw [threshold_secondary_left] at hsep ⊢
  have hs : width S (normalY S)+width T (normalY S) ≤
      |dot (normalY S) (sub T.center S.center)| := by
    simpa only [dot_normalY] using hsep
  simpa only [dot_normalY] using
    separator_forward_of_pin_order (normalY_ne_zero S) hp hq horder hs

lemma right_secondary_forward {S T : UnitSquare} {p q : Point}
    (hp : openSquare S p) (hq : openSquare T q)
    (horder : dot (normalY T) p < dot (normalY T) q)
    (hsep : Seven.SAT.threshold S T ≤ |frameY T (sub T.center S.center)|) :
    Seven.SAT.threshold S T ≤ frameY T (sub T.center S.center) := by
  rw [threshold_secondary_right] at hsep ⊢
  have hs : width S (normalY T)+width T (normalY T) ≤
      |dot (normalY T) (sub T.center S.center)| := by
    simpa only [dot_normalY] using hsep
  simpa only [dot_normalY] using
    separator_forward_of_pin_order (normalY_ne_zero T) hp hq horder hs

end SquaresInCircles.Six.Analytic
