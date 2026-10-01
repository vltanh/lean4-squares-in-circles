import SquaresInCircles.Six.Normalization.PairOrder
import SquaresInCircles.Six.Normalization.CapPiercing
import SquaresInCircles.Six.Construction

/-!
# N22, N25 and N26 in the actual labelled frame

The local cap lemmas are transported by exact cardinal-coordinate identities.
Both opposite-cardinal hypotheses are retained in N26. Uniqueness uses a point
in both OPEN squares, not disjoint bounding boxes or disjoint closed squares.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates

def IsCardinal (k : CentralAxis) : Prop :=
  k=.east ∨ k=.north ∨ k=.west ∨ k=.south

def cardinalDepth (c : Point) : CentralAxis → ℝ
  | .east => 1/2+c.1
  | .north => 1/2+c.2
  | .west => 1/2-c.1
  | .south => 1/2-c.2
  | _ => 0

def cardinalPiercingPoint (c : Point) : CentralAxis → Point
  | .east => (1+c.1,0)
  | .north => (0,1+c.2)
  | .west => (c.1-1,0)
  | .south => (0,c.2-1)
  | _ => (0,0)

lemma matchingCardinal_isCardinal (i : Fin 5) : IsCardinal (matchingCardinal i) := by
  fin_cases i <;> simp [matchingCardinal,IsCardinal]

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
    Real.cos_sub,Real.sin_sub,Real.cos_zero,Real.sin_zero,Real.cos_pi,Real.sin_pi,
    Real.cos_pi_div_two,Real.sin_pi_div_two,south_sin,south_cos,abs_neg,
    mul_zero,mul_one,mul_neg_one,zero_mul,one_mul,zero_add,add_zero,sub_zero,
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
    Real.cos_zero,Real.sin_zero,Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,
    Real.sin_pi_div_two,south_sin,south_cos,mul_zero,mul_one,mul_neg_one,zero_mul,
    one_mul,zero_add,add_zero,sub_zero,zero_sub,neg_neg]
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

/-- K4 transported to the original cardinal direction. -/
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

/-- N22 for all matching cardinal sides, including the possible W/D collision. -/
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

/-- The local cap support inequality with its actual global depth. -/
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

/-- N26 east/west, with BOTH cardinal assumptions. -/
theorem PinPacking.east_west_budget {R : ℝ} (P : PinPacking R)
    (hE : 0 ≤ centralMargin .east (P.phase 0) (P.radial 0) (P.transverse 0) P.center.1 P.center.2)
    (hW : 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2) P.center.1 P.center.2) :
    |P.phase 0|+|P.phase 2-Real.pi| < 4*c0 := by
  have he := P.cardinal_cap_depth 0 hE
  have hw := P.cardinal_cap_depth 2 hW
  have hae := P.matching_cardinal_angle 0 hE
  have haw := P.matching_cardinal_angle 2 hW
  have h0 : matchingCardinal 0 = .east := rfl
  have h2 : matchingCardinal 2 = .west := rfl
  rw [h0] at he hae
  rw [h2] at hw haw
  simp only [cardinalCenter,cardinalDepth,sub_zero] at he hw hae haw
  exact opposite_cardinal_angle_budget_of_caps he hw hae.le haw.le

/-- N26 north/south, again only for two cardinal helpers. -/
theorem PinPacking.north_south_budget {R : ℝ} (P : PinPacking R)
    (hN : 0 ≤ centralMargin .north (P.phase 1) (P.radial 1) (P.transverse 1) P.center.1 P.center.2)
    (hS : 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4) P.center.1 P.center.2) :
    |P.phase 1-Real.pi/2|+|P.phase 4-3*Real.pi/2| < 4*c0 := by
  have hn := P.cardinal_cap_depth 1 hN
  have hs := P.cardinal_cap_depth 4 hS
  have han := P.matching_cardinal_angle 1 hN
  have has := P.matching_cardinal_angle 4 hS
  simp only [matchingCardinal,cardinalCenter,cardinalDepth] at hn hs han has
  exact opposite_cardinal_angle_budget_of_caps hn hs han.le has.le

end SquaresInCircles.Six.Normalization
