import SquaresInCircles.Six.Stress.Support

/-!
# Exact cap/vertex center support

This is the support formula used by the repaired A2 stresses. The radius is a
parameter, so it can be instantiated at the exact candidate radius rather than
silently replacing it by Q0. A cap branch is selected only after proving its
slope condition from 2 R V <= sqrt(U^2+V^2). Coordinate dominance alone does
not select that branch.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

def rhoAt (R : ℝ) : ℝ := Real.sqrt (R^2-1/4)-1/2

def orderedSupport (R U V : ℝ) : ℝ :=
  if 2*R*V ≤ Real.sqrt (U^2+V^2) then rhoAt R*U
  else R*Real.sqrt (U^2+V^2)-(U+V)/2

def scalarSupport (R x y : ℝ) : ℝ :=
  if |y| ≤ |x| then orderedSupport R |x| |y| else orderedSupport R |y| |x|

def exactSupport (R : ℝ) (S : UnitSquare) (g : Point) : ℝ :=
  scalarSupport R (frameX S g) (frameY S g)

private lemma corner_support {A B a b c s q : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hc : 0 ≤ c)
    (hcircle : a^2+b^2=q) (hbox : A^2+B^2 ≤ q)
    (hslope : a*s ≤ b*c) : A*c+B*s ≤ a*c+b*s := by
  have ht : a*(A-a)+b*(B-b) ≤ 0 := by
    nlinarith [sq_nonneg (A-a),sq_nonneg (B-b)]
  have hct := mul_nonpos_of_nonneg_of_nonpos hc ht
  have hsl := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hp : a*(A*c+B*s-(a*c+b*s)) ≤ 0 := by nlinarith
  by_contra! h
  have hpos := mul_pos ha (sub_pos.mpr h)
  linarith

private lemma cap_slope {R U V : ℝ} (hR : 1/2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : 2*R*V ≤ Real.sqrt (U^2+V^2)) :
    Real.sqrt (R^2-1/4)*V ≤ U/2 := by
  have hrad : 0 ≤ R^2-1/4 := by nlinarith [sq_nonneg (R-1/2)]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sq_sqrt (show 0 ≤ U^2+V^2 by positivity)
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ Real.sqrt (U^2+V^2)+2*R*V by
      positivity)
  have hmul := congrArg (fun z : ℝ => z*V^2) hs
  have hsquare : (2*Real.sqrt (R^2-1/4)*V)^2 ≤ U^2 := by nlinarith
  have hnn : 0 ≤ 2*Real.sqrt (R^2-1/4)*V := by positivity
  by_contra! hbad
  have ht := mul_pos
    (show 0 < 2*Real.sqrt (R^2-1/4)*V-U by linarith)
    (show 0 < 2*Real.sqrt (R^2-1/4)*V+U by linarith)
  nlinarith

lemma ordered_center_support {R a b U V : ℝ}
    (hR : 1/2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ R^2) :
    |a|*U+|b|*V ≤ orderedSupport R U V := by
  unfold orderedSupport
  split_ifs with hswitch
  · have hrad : 0 < R^2-1/4 := by nlinarith [sq_nonneg (R-1/2)]
    have ha0 := Real.sqrt_pos.mpr hrad
    have hid := Real.sq_sqrt hrad.le
    have hslope := cap_slope hR hU hV hswitch
    have hcorner := corner_support
      (A := |a|+1/2) (B := |b|+1/2)
      (a := Real.sqrt (R^2-1/4)) (b := (1:ℝ)/2) (c := U) (s := V)
      ha0 (by linarith [abs_nonneg b]) hU (by nlinarith) hbox (by linarith)
    dsimp [rhoAt]
    nlinarith
  · have hround := dot_le_radius (v := (U,V)) (p := (|a|+1/2,|b|+1/2))
      (by linarith : 0 ≤ R) hbox
    dsimp [dot,vectorLength,normSq] at hround
    nlinarith

/-- The scalar support bound in an arbitrary side frame, with sign and axis
sorting handled explicitly. -/
theorem scalar_center_support {R a b x y : ℝ}
    (hR : 1/2 < R) (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ R^2) :
    x*a+y*b ≤ scalarSupport R x y := by
  have hx : x*a ≤ |a|*|x| := by
    simpa only [abs_mul,mul_comm] using le_abs_self (x*a)
  have hy : y*b ≤ |b|*|y| := by
    simpa only [abs_mul,mul_comm] using le_abs_self (y*b)
  unfold scalarSupport
  split_ifs
  · have hh := ordered_center_support hR (abs_nonneg x) (abs_nonneg y) hbox
    linarith
  · have hbox' : (|b|+1/2)^2+(|a|+1/2)^2 ≤ R^2 := by linarith
    have hh := ordered_center_support hR (abs_nonneg y) (abs_nonneg x) hbox'
    linarith

lemma alpha_frame_center (S : UnitSquare) : alpha S (0,0)=|frameX S S.center| := by
  have h : localX S (0,0) = -frameX S S.center := by
    dsimp [localX,frameX]
    ring
  simp only [alpha,h,abs_neg]

lemma beta_frame_center (S : UnitSquare) : beta S (0,0)=|frameY S S.center| := by
  have h : localY S (0,0) = -frameY S S.center := by
    dsimp [localY,frameY]
    ring
  simp only [beta,h,abs_neg]

/-- The exact support is a proved upper bound on an actual contained center. -/
theorem center_le_exactSupport {S : UnitSquare} {R : ℝ}
    (hR : 1/2 < R) (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p) (g : Point) :
    dot g S.center ≤ exactSupport R S g := by
  have hc := phi_le_of_contained S (0,0) R hcontain
  rw [alpha_frame_center,beta_frame_center] at hc
  have hh := scalar_center_support (x := frameX S g) (y := frameY S g) hR hc
  rw [frame_dot] at hh
  exact hh

end SquaresInCircles.Six.Stress
