import SquaresInCircles.Six.Normalization.PairOrder
import SquaresInCircles.Six.Normalization.CapPiercing
import SquaresInCircles.Six.Construction

/-!
# Squares beyond a side of the central square

In the frame turned to a side of the central square, a nonnegative margin along
that side says that the square lies beyond the line of the side, at distance
`cardinalDepth` from the origin (`cardinal_margin_local`). Such a square
contains in its interior the point of the axis half a unit beyond that line
(`PinPacking.cardinal_piercing`). Hence two exterior squares with the same
matching side, W and D, are not both separated along it
(`PinPacking.one_helper_per_side`), and the depth of the side is at most the
cap depth at the angle of the square (`PinPacking.cardinal_cap_depth`).
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

/-- The four sides of the central square among the seven axes. -/
def IsCardinal (k : CentralAxis) : Prop :=
  k=.east ∨ k=.north ∨ k=.west ∨ k=.south

/-- The distance from the origin to the line of a side of the central square
centred at `c`. -/
def cardinalDepth (c : Point) : CentralAxis → ℝ
  | .east => 1/2+c.1
  | .north => 1/2+c.2
  | .west => 1/2-c.1
  | .south => 1/2-c.2
  | _ => 0

/-- The point of the axis through the origin half a unit beyond a side of the
central square. -/
def cardinalPiercingPoint (c : Point) : CentralAxis → Point
  | .east => (1+c.1,0)
  | .north => (0,1+c.2)
  | .west => (c.1-1,0)
  | .south => (0,c.2-1)
  | _ => (0,0)

lemma matchingCardinal_isCardinal (i : Fin 5) : IsCardinal (matchingCardinal i) := by
  fin_cases i <;> simp [matchingCardinal,IsCardinal]

/-- The case of `PinPacking.cardinal_angle` for each exterior square and its
matching side. -/
def matchingCase : Fin 5 → Fin 6 := ![0,1,2,3,5]

@[simp] lemma matchingCase_pin (i : Fin 5) : cardinalCasePin (matchingCase i) = i := by
  fin_cases i <;> rfl

@[simp] lemma matchingCase_axis (i : Fin 5) : cardinalCaseAxis (matchingCase i) = matchingCardinal i := by
  fin_cases i <;> rfl

lemma PinPacking.matching_cardinal_angle {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    |P.phase i-cardinalCenter (matchingCardinal i)| < 2/5 := by
  have h := P.cardinal_angle (matchingCase i)
  simp only [matchingCase_pin,matchingCase_axis] at h
  exact h hi

lemma south_sin : Real.sin (3*Real.pi/2) = -1 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
  simp

lemma south_cos : Real.cos (3*Real.pi/2) = 0 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
  simp

lemma cardinal_margin_local (k : CentralAxis) (hk : IsCardinal k) (c : Point) (t a b : ℝ) :
    centralMargin k t a b c.1 c.2 =
      centerX (t-cardinalCenter k) a b-angularWidth (t-cardinalCenter k)-cardinalDepth c k := by
  rcases hk with rfl | rfl | rfl | rfl
  all_goals simp only [centralMargin,cardinalCenter,cardinalDepth,centerX,centerY,angularWidth,
    Real.cos_sub,Real.sin_sub,Real.cos_pi,Real.sin_pi,
    Real.cos_pi_div_two,Real.sin_pi_div_two,south_sin,south_cos,abs_neg,
    mul_zero,mul_one,mul_neg_one,zero_add,add_zero,sub_zero,
    zero_sub,neg_neg]
  all_goals ring

lemma cardinal_piercing_coordinates (k : CentralAxis) (hk : IsCardinal k)
    (c : Point) (t a b : ℝ) :
    localX (orientedSquare (t-cardinalCenter k) a b) (cardinalDepth c k+1/2,0) =
        localX (orientedSquare t a b) (cardinalPiercingPoint c k) ∧
      localY (orientedSquare (t-cardinalCenter k) a b) (cardinalDepth c k+1/2,0) =
        localY (orientedSquare t a b) (cardinalPiercingPoint c k) := by
  rcases hk with rfl | rfl | rfl | rfl
  all_goals constructor <;> simp only [orientedSquare_localX,orientedSquare_localY,
    cardinalCenter,cardinalDepth,cardinalPiercingPoint,Real.cos_sub,Real.sin_sub,
    Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,
    Real.sin_pi_div_two,south_sin,south_cos,mul_zero,mul_one,mul_neg_one,zero_mul,
    zero_add,add_zero,sub_zero,zero_sub,neg_neg]
  all_goals ring

lemma cardinal_depth_bounds {c : Point}
    (hc : (0 ≤ c.1 ∧ c.1 ≤ c0) ∧ (0 ≤ c.2 ∧ c.2 ≤ c0))
    (k : CentralAxis) (hk : IsCardinal k) :
    coreRadius ≤ cardinalDepth c k ∧ cardinalDepth c k ≤ rho0-1/2 := by
  have hid := c0_add_coreRadius
  rcases hk with rfl | rfl | rfl | rfl <;> dsimp [cardinalDepth] <;>
    constructor <;> dsimp [c0,coreRadius] at * <;>
    linarith [hc.1.1,hc.1.2,hc.2.1,hc.2.2,rho0_gt_one]

lemma oriented_contained_of_chart {t a b : ℝ} (hc : ContainedChart a |b|) :
    ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0,0) R0 p := by
  intro p hp
  apply Six.inDisk_of_phi_le (S := orientedSquare t a b) (o := (0,0)) (R := R0) _ hp
  rw [orientedSquare_alpha,orientedSquare_beta,R0_sq]
  simpa [phi,abs_of_nonneg (show 0 ≤ a by linarith [hc.half_le])] using hc.containment

lemma local_cap_of_cardinal_margin {t a b : ℝ} {c : Point} {k : CentralAxis}
    (hk : IsCardinal k) (hm : 0 ≤ centralMargin k t a b c.1 c.2) :
    ∀ p, closedSquare (orientedSquare (t-cardinalCenter k) a b) p → cardinalDepth c k ≤ p.1 := by
  rw [cardinal_margin_local k hk c t a b] at hm
  intro p hp
  have hb := (closed_center_coordinate_bounds hp).1.1
  linarith

/-- A square separated from the central square along the matching side contains
the point half a unit beyond that side. -/
theorem PinPacking.cardinal_piercing {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    openSquare (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
      (cardinalPiercingPoint P.center (matchingCardinal i)) := by
  let k := matchingCardinal i
  have hk : IsCardinal k := matchingCardinal_isCardinal i
  have ht := P.matching_cardinal_angle i hi
  have hangle : |P.phase i-cardinalCenter k| ≤ Real.pi/4 := by linarith [Real.pi_gt_d2]
  have hh := (cardinal_depth_bounds P.box k hk).1
  have hp := cap_piercing hangle hh (oriented_contained_of_chart (P.contained i))
    (local_cap_of_cardinal_margin hk hi)
  have hcoords := cardinal_piercing_coordinates k hk P.center (P.phase i) (P.radial i) (P.transverse i)
  simpa only [openSquare,hcoords.1,hcoords.2] using hp

/-- Two exterior squares with the same matching side, such as W and D, are not
both separated along it. -/
theorem PinPacking.one_helper_per_side {R : ℝ} (P : PinPacking R) (i j : Fin 5)
    (hside : matchingCardinal i=matchingCardinal j)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2)
    (hj : 0 ≤ centralMargin (matchingCardinal j) (P.phase j) (P.radial j) (P.transverse j)
      P.center.1 P.center.2) : i=j := by
  by_contra hij
  have hpi := P.cardinal_piercing i hi
  have hpj := P.cardinal_piercing j hj
  rw [← hside] at hpj
  exact P.exterior_disjoint i j hij _ ⟨hpi,hpj⟩

/-- The depth of the matching side is at most the cap depth at the angle of the
square. -/
theorem PinPacking.cardinal_cap_depth {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    cardinalDepth P.center (matchingCardinal i) ≤
      capDepth |P.phase i-cardinalCenter (matchingCardinal i)| := by
  have hangle := P.matching_cardinal_angle i hi
  have hm := hi
  rw [cardinal_margin_local _ (matchingCardinal_isCardinal i)] at hm
  apply cap_support_bound_signed (a := P.radial i) (b := P.transverse i)
    (by linarith [Real.pi_gt_d2])
  · simpa [phi,abs_of_nonneg (show 0 ≤ P.radial i by linarith [(P.contained i).half_le])]
      using (P.contained i).containment
  · dsimp [centerX,angularWidth] at hm
    linarith

end SquaresInCircles.Six.Normalization
