import SquaresInCircles.Common.Contacts

/-!
# The square in the middle

A unit square that contains the origin, and whose points in the band `|y| < 1`
all have `|x| ≤ 1/2`, is axis-parallel and centred on `x = 0`: a tilted square
has a section through its centre longer than 1. The four side squares block the
band `|y| ≤ 1` beyond `|x| = 1/2`, so the square that contains the disk centre
stays in the strip between them. Its height is left free.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- `(x, y)` lies in the open unit square with centre `(X, Y)` and axes `(c, s)`
and `(-s, c)`. -/
def sectionOpen (c s X Y x y : ℝ) : Prop :=
  |c*(x-X)+s*(y-Y)| < 1/2 ∧ |-s*(x-X)+c*(y-Y)| < 1/2

lemma center_section_forces_cardinal {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (hY : |Y| < 1)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    c = 0 ∨ s = 0 := by
  by_contra hn
  obtain ⟨hc,hs⟩ := not_or.mp hn
  have hc1 : |c| < 1 := (sq_lt_one_iff_abs_lt_one c).mp (by linarith [sq_pos_of_ne_zero hs])
  have hs1 : |s| < 1 := (sq_lt_one_iff_abs_lt_one s).mp (by linarith [sq_pos_of_ne_zero hc])
  let m := max |c| |s|
  let q := 1/2+(1-m)/4
  have hm1 : m < 1 := max_lt hc1 hs1
  have hq : 1/2 < q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hqm : m*q < 1/2 := by
    have hp := mul_pos (sub_pos.2 hm1) (show 0 < 2-m by linarith)
    dsimp [q]
    linarith
  have hcq : |c| * q < 1/2 := (mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le).trans_lt hqm
  have hsq : |s| * q < 1/2 := (mul_le_mul_of_nonneg_right (le_max_right _ _) hq0.le).trans_lt hqm
  have hin (d : ℝ) (hd : |d| = q) : |X+d| ≤ 1/2 :=
    hstrip _ Y (by simpa [sectionOpen,abs_mul,hd] using And.intro hcq hsq) hY
  linarith [(abs_le.mp (hin q (abs_of_pos hq0))).2,
    (abs_le.mp (hin (-q) (by rw [abs_neg,abs_of_pos hq0]))).1]

/-- A unit square whose open section contains the origin, and whose points in
the band `|y| < 1` all have `|x| ≤ 1/2`, is axis-parallel and centred at
`(0, Y)` with `|Y| < 1/2`. -/
theorem section_strip_rigidity {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (h0 : sectionOpen c s X Y 0 0)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    |Y| < 1/2 ∧ ∀ x y, sectionOpen c s X Y x y ↔ openAxisSquare (0,Y) x y := by
  have hid : (c*(0-X)+s*(0-Y))^2+(-s*(0-X)+c*(0-Y))^2 = X^2+Y^2 := by
    linear_combination (X^2+Y^2)*hunit
  have h1 := sq_lt_sq' (abs_lt.mp h0.1).1 (abs_lt.mp h0.1).2
  have h2 := sq_lt_sq' (abs_lt.mp h0.2).1 (abs_lt.mp h0.2).2
  have hY : |Y| < 1 := (sq_lt_one_iff_abs_lt_one Y).mp (by linarith [sq_nonneg X])
  have hrect (x y : ℝ) : sectionOpen c s X Y x y ↔ |x-X| < 1/2 ∧ |y-Y| < 1/2 :=
    cardinal_box hunit (center_section_forces_cardinal hunit hY hstrip)
  have hin (x : ℝ) (hx : |x-X| < 1/2) : |x| ≤ 1/2 :=
    hstrip x Y ((hrect x Y).mpr ⟨hx,by simp⟩) hY
  have hxpos : X+1/2 ≤ 1/2 := affine_endpoint_le (A := X) fun t ht0 ht1 => by
    linarith [(abs_le.mp (hin (X+t/2) (abs_lt.mpr ⟨by linarith,by linarith⟩))).2]
  have hxneg : -X+1/2 ≤ 1/2 := affine_endpoint_le (A := -X) fun t ht0 ht1 => by
    linarith [(abs_le.mp (hin (X-t/2) (abs_lt.mpr ⟨by linarith,by linarith⟩))).1]
  obtain rfl : X = 0 := by linarith
  exact ⟨by simpa using ((hrect 0 0).mp h0).2,hrect⟩

def sideCenters : Fin 4 → Point :=
  ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2)]

lemma side_barriers_cover {x y : ℝ} (hx : |x| = 1/2) (hy : |y| ≤ 1) :
    ∃ i : Fin 4, closedAxisSquare (sideCenters i) x y := by
  rw [abs_le] at hy
  rcases (abs_eq (by norm_num)).mp hx with rfl | rfl <;> rcases le_total 0 y with h | h <;>
    [exists 1; exists 0; exists 3; exists 2] <;>
    exact ⟨by norm_num [sideCenters],
      abs_le.mpr ⟨by simp [sideCenters]; linarith,by simp [sideCenters]; linarith⟩⟩

lemma central_strip {S : UnitSquare} {B : Fin 4 → UnitSquare} {o : Point} {φ : Direction}
    (h0 : openSquare S o) (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∀ x y, openSquare S (pointInDirection o φ x y) → |y| < 1 → |x| ≤ 1/2 := by
  intro x y hp hy
  by_contra! hx
  set t := 1/(2*|x|)
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : (1-t) • o+t • pointInDirection o φ x y = pointInDirection o φ (t*x) (t*y) := by
    ext <;> simp [pointInDirection] <;> ring
  have hp' : openSquare S (pointInDirection o φ (t*x) (t*y)) :=
    he ▸ openSquare_convex S h0 hp (by linarith) ht0.le (by ring)
  have htx : |t*x| = 1/2 := by rw [abs_mul,abs_of_pos ht0]; simp only [t]; field_simp
  have hty : |t*y| ≤ 1 := by
    rw [abs_mul,abs_of_pos ht0]
    exact (mul_le_of_le_one_left (abs_nonneg y) ht1.le).trans hy.le
  obtain ⟨i,hi⟩ := side_barriers_cover htx hty
  exact closed_open_disjoint (B i) S (hd i) (((hrep i).closed _ _).mpr hi) hp'

/-- The open square `S` read in the frame of `o` and `φ`. -/
lemma square_section (S : UnitSquare) (o : Point) (φ : Direction) (x y : ℝ) :
    openSquare S (pointInDirection o φ x y) ↔
    sectionOpen (relativeC (modelSquare o φ 0) S) (relativeS (modelSquare o φ 0) S)
      (frameX (modelSquare o φ 0) (sub S.center o))
      (frameY (modelSquare o φ 0) (sub S.center o)) x y := by
  have hu := Real.Angle.cos_sq_add_sin_sq φ
  simp only [openSquare,sectionOpen]
  congr! 3 <;>
    dsimp [localX,localY,pointInDirection,relativeC,relativeS,frameX,frameY,sub,modelSquare]
  · linear_combination (S.cosine*(S.center.1-o.1)+S.sine*(S.center.2-o.2))*hu
  · linear_combination (S.cosine*(S.center.2-o.2)-S.sine*(S.center.1-o.1))*hu

/-- The square that contains the disk centre sits at `(0, z)`, with
`|z| < 1/2`, in the frame of the four side squares. -/
theorem central_square_represents {S : UnitSquare} {B : Fin 4 → UnitSquare}
    {o : Point} {φ : Direction} (h0 : openSquare S o)
    (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∃ z : ℝ, |z| < 1/2 ∧ Represents S o φ (0,z) := by
  have hs := square_section S o φ
  obtain ⟨hz,hr⟩ := section_strip_rigidity (relative_unit _ S)
    ((hs 0 0).mp (by simpa [pointInDirection] using h0))
    (fun x y hxy hy => central_strip h0 hrep hd x y ((hs x y).mpr hxy) hy)
  exact ⟨_,hz,fun x y => (hs x y).trans (hr x y)⟩

end SquaresInCircles.Seven
