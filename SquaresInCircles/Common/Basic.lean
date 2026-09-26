import SquaresInCircles.Geometry

/-!
# Frames, interior-disjointness and the farthest-vertex bound

Vector operations, a square's frame and vertices, and the squared distance
`phi` from a point to the farthest vertex of a square. Distances always use
`normSq`, not the product-space norm on `ℝ × ℝ` (which is the maximum norm).
-/
noncomputable section
namespace SquaresInCircles

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)

lemma normSq_nonneg (p : Point) : 0 ≤ normSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma normSq_pos_of_ne {v : Point} (hv : v ≠ (0,0)) : 0 < normSq v := by
  rcases v with ⟨x,y⟩
  have h : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! h
    exact hv (by rw [h.1,h.2])
  unfold normSq
  rcases h with h | h <;> positivity

lemma sub_ne_origin {p q : Point} (h : p ≠ q) : sub p q ≠ (0,0) := fun hh =>
  h (Prod.ext (sub_eq_zero.mp (congrArg Prod.fst hh)) (sub_eq_zero.mp (congrArg Prod.snd hh)))

lemma dot_add_right (v p q : Point) : dot v (add p q) = dot v p + dot v q := by
  dsimp [dot, add]; ring
lemma dot_sub_right (v p q : Point) : dot v (sub p q) = dot v p - dot v q := by
  dsimp [dot, sub]; ring
lemma dot_scale_right (v : Point) (t : ℝ) (p : Point) :
    dot v (scale t p) = t * dot v p := by dsimp [dot, scale]; ring

/-- Non-overlap, without a containing disk or any lower-bound assumption. -/
def InteriorDisjoint {ι : Type*} (S : ι → UnitSquare) : Prop :=
  ∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p)

lemma Packing.disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : InteriorDisjoint S := hp.2.2

lemma InteriorDisjoint.pairwise {ι : Type*} {S : ι → UnitSquare}
    (hd : InteriorDisjoint S) :
    Pairwise (fun i j => Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p}) :=
  fun i j hij => Set.disjoint_left.mpr fun p hi hj => hd i j hij p ⟨hi,hj⟩

/-- The coordinates of a vector in a square's frame; `localX S p` is
`frameX S (sub p S.center)`. -/
def frameX (S : UnitSquare) (v : Point) : ℝ := S.cosine*v.1 + S.sine*v.2
def frameY (S : UnitSquare) (v : Point) : ℝ := -S.sine*v.1 + S.cosine*v.2

lemma frame_norm (S : UnitSquare) (v : Point) :
    (frameX S v)^2 + (frameY S v)^2 = normSq v := by
  simp only [frameX,frameY,normSq]; linear_combination (v.1^2+v.2^2)*S.unit

lemma frame_dot (S : UnitSquare) (v w : Point) :
    frameX S v * frameX S w + frameY S v * frameY S w = dot v w := by
  simp only [frameX,frameY,dot]; linear_combination (v.1*w.1+v.2*w.2)*S.unit

lemma frame_distance (S : UnitSquare) (p o : Point) :
    (localX S p - localX S o)^2 + (localY S p - localY S o)^2 = normSq (sub p o) := by
  rw [← frame_norm]; simp only [localX,localY,frameX,frameY,sub]; ring

/-- The vector with coordinates `p` in the frame of `S`. -/
def rotate (S : UnitSquare) (p : Point) : Point :=
  (S.cosine * p.1 - S.sine * p.2,
   S.sine * p.1 + S.cosine * p.2)

lemma localX_rotated (S : UnitSquare) (p : Point) :
    localX S (add S.center (rotate S p)) = p.1 := by
  simp only [localX,add,rotate]; linear_combination p.1*S.unit

lemma localY_rotated (S : UnitSquare) (p : Point) :
    localY S (add S.center (rotate S p)) = p.2 := by
  simp only [localY,add,rotate]; linear_combination p.2*S.unit

/-- Nonnegative absolute coordinates of the tested point in a square's frame. -/
def alpha (S : UnitSquare) (o : Point) : ℝ := |localX S o|
def beta (S : UnitSquare) (o : Point) : ℝ := |localY S o|

lemma alpha_nonneg (S : UnitSquare) (o : Point) : 0 ≤ alpha S o := abs_nonneg _
lemma beta_nonneg (S : UnitSquare) (o : Point) : 0 ≤ beta S o := abs_nonneg _

lemma abs_frame_centerX (S : UnitSquare) (o : Point) :
    |frameX S (sub S.center o)| = alpha S o := by
  rw [alpha,← abs_neg]; congr 1; simp only [frameX,sub,localX]; ring

lemma abs_frame_centerY (S : UnitSquare) (o : Point) :
    |frameY S (sub S.center o)| = beta S o := by
  rw [beta,← abs_neg]; congr 1; simp only [frameY,sub,localY]; ring

lemma local_center_norm (S : UnitSquare) (o : Point) :
    normSq (sub S.center o)=(alpha S o)^2+(beta S o)^2 := by
  rw [← frame_norm,← abs_frame_centerX,← abs_frame_centerY,sq_abs,sq_abs]

/-- Squared distance to the farthest vertex in local absolute coordinates. -/
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

/-- A number of absolute value `c` with the sign of `x`. -/
lemma exists_signed (x : ℝ) {c : ℝ} (hc : 0 ≤ c) : ∃ u : ℝ, |u|=c ∧ x*u=c*|x| := by
  rcases abs_cases x with ⟨hx,-⟩ | ⟨hx,-⟩
  · exact ⟨c,abs_of_nonneg hc,by rw [hx]; ring⟩
  · exact ⟨-c,by rw [abs_neg,abs_of_nonneg hc],by rw [hx]; ring⟩

/-- The vertex across both axes from `o` is at squared distance `phi` from it. -/
lemma phi_le_of_contained (S : UnitSquare) (o : Point) (R : ℝ)
    (h : ∀ p, closedSquare S p → inDisk o R p) :
    phi (alpha S o) (beta S o) ≤ R^2 := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (localX S o) (c := 1/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (localY S o) (c := 1/2) (by norm_num)
  have hh := h (add S.center (rotate S (-u,-v))) (by
    simp only [closedSquare,localX_rotated,localY_rotated,abs_neg,hu,hv,le_refl,and_self])
  rw [inDisk,← frame_distance S,localX_rotated,localY_rotated] at hh
  have hu2 : u^2=1/4 := by rw [← sq_abs,hu]; norm_num
  have hv2 : v^2=1/4 := by rw [← sq_abs,hv]; norm_num
  unfold phi alpha beta
  nlinarith [sq_abs (localX S o),sq_abs (localY S o)]

lemma Packing.phi_le {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (i : Fin n) :
    phi (alpha (S i) o) (beta (S i) o) ≤ R^2 :=
  phi_le_of_contained _ _ _ (hp.2.1 i)

/-- The disk given by the nearer side of a containing square is really inside it. -/
lemma inscribed_disk_mem (S : UnitSquare) (o : Point) {a p : ℝ}
    (hp : 0 < p) (hpa : a+p=1/2)
    (hx : alpha S o ≤ a) (hy : beta S o ≤ a) {z : Point}
    (hz : normSq (sub z o) < p^2) : openSquare S z := by
  have hu := frame_norm S (sub z o)
  have hX := abs_lt_of_sq_lt_sq (a := frameX S (sub z o))
    (by nlinarith [sq_nonneg (frameY S (sub z o))]) hp.le
  have hY := abs_lt_of_sq_lt_sq (a := frameY S (sub z o))
    (by nlinarith [sq_nonneg (frameX S (sub z o))]) hp.le
  have heX : localX S z=frameX S (sub z o)+localX S o := by simp only [localX,frameX,sub]; ring
  have heY : localY S z=frameY S (sub z o)+localY S o := by simp only [localY,frameY,sub]; ring
  exact ⟨by rw [heX]; linarith [abs_add_le (frameX S (sub z o)) (localX S o),
      show |localX S o| ≤ a from hx],
    by rw [heY]; linarith [abs_add_le (frameY S (sub z o)) (localY S o),
      show |localY S o| ≤ a from hy]⟩

lemma small_disk_in_openSquare (S : UnitSquare) {p : Point}
    (hp : normSq (sub p S.center) < 1/4) : openSquare S p :=
  inscribed_disk_mem S S.center (a := 0) (p := 1/2) (by norm_num) (by norm_num)
    (by simp [alpha,localX]) (by simp [beta,localY]) (by linarith)

def halfDiagonal : ℝ := Real.sqrt 2/2

lemma halfDiagonal_pos : 0 < halfDiagonal := by unfold halfDiagonal; positivity
lemma halfDiagonal_sq : halfDiagonal^2=1/2 := by
  rw [halfDiagonal,div_pow,Real.sq_sqrt (by norm_num)]; norm_num
lemma halfDiagonal_gt_707 : (707:ℝ)/1000 < halfDiagonal := by
  nlinarith [halfDiagonal_sq,halfDiagonal_pos]

end SquaresInCircles
