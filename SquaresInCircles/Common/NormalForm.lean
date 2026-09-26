import SquaresInCircles.Common.Coordinates
import SquaresInCircles.Common.Constructions

/-!
# Geometric normal forms, not equality of frame records

A normal form specifies both the open and the closed point set of every square
in one Euclidean frame centred at the disk centre, up to a permutation of the
squares. It does not equate `UnitSquare` records: a quarter-turn of a frame
describes the same square.
-/
noncomputable section
namespace SquaresInCircles

/-- The actual square, expressed in one common positively oriented frame. -/
def Represents (S : UnitSquare) (o : Point) (φ : Direction) (c : Point) : Prop :=
  ∀ x y, openSquare S (pointInDirection o φ x y) ↔ openAxisSquare c x y

/-- A rigid motion with its inverse written in coordinates. -/
def frameEquiv (o : Point) (φ : Direction) : Point ≃ Point where
  toFun p := pointInDirection o φ p.1 p.2
  invFun p := (φ.cos*(p.1-o.1)+φ.sin*(p.2-o.2),
    -φ.sin*(p.1-o.1)+φ.cos*(p.2-o.2))
  left_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection]
    · linear_combination p.1*hu
    · linear_combination p.2*hu
  right_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection]
    · linear_combination (p.1-o.1)*hu
    · linear_combination (p.2-o.2)*hu

@[simp] lemma frameEquiv_apply (o : Point) (φ : Direction) (p : Point) :
    frameEquiv o φ p = pointInDirection o φ p.1 p.2 := rfl

lemma frameEquiv_zero (o : Point) (φ : Direction) : frameEquiv o φ (0,0)=o := by
  simp [pointInDirection]

lemma frameEquiv_distance (o : Point) (φ : Direction) (p q : Point) :
    normSq (sub (frameEquiv o φ p) (frameEquiv o φ q))=normSq (sub p q) := by
  simp only [frameEquiv_apply,pointInDirection,normSq,sub]
  linear_combination ((p.1-q.1)^2+(p.2-q.2)^2)*Real.Angle.cos_sq_add_sin_sq φ

lemma abs_endpoint_le {A B : ℝ} (h : ∀ t : ℝ, 0 ≤ t → t < 1 → |(1-t)*A+t*B| < 1/2) :
    |B| ≤ 1/2 := by
  refine abs_le.mpr ⟨?_,affine_endpoint_le fun t h0 h1 => (abs_lt.mp (h t h0 h1)).2.le⟩
  have := affine_endpoint_le (A := -A) (B := -B) (D := 1/2) fun t h0 h1 => by
    linarith [(abs_lt.mp (h t h0 h1)).1]
  linarith

/-- Equality of open squares implies equality of their closed square sets. -/
lemma same_open_same_closed (S T : UnitSquare)
    (h : ∀ p, openSquare S p ↔ openSquare T p) :
    ∀ p, closedSquare S p ↔ closedSquare T p := by
  have oneWay (S T : UnitSquare) (hh : ∀ p, openSquare S p → openSquare T p)
      (p : Point) (hp : closedSquare S p) : closedSquare T p := by
    have hm (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) := hh _ (shrink_open S hp h0 h1)
    have he (t : ℝ) := local_affine T S.center p (sub_add_cancel 1 t)
    exact ⟨abs_endpoint_le fun t h0 h1 => (he t).1 ▸ (hm t h0 h1).1,
      abs_endpoint_le fun t h0 h1 => (he t).2 ▸ (hm t h0 h1).2⟩
  exact fun p => ⟨oneWay S T (fun q => (h q).mp) p,oneWay T S (fun q => (h q).mpr) p⟩

def modelSquare (o : Point) (φ : Direction) (c : Point) : UnitSquare where
  center := pointInDirection o φ c.1 c.2
  cosine := φ.cos
  sine := φ.sin
  unit := Real.Angle.cos_sq_add_sin_sq φ

lemma modelSquare_local (o : Point) (φ : Direction) (c : Point) (x y : ℝ) :
    localX (modelSquare o φ c) (pointInDirection o φ x y)=x-c.1 ∧
    localY (modelSquare o φ c) (pointInDirection o φ x y)=y-c.2 := by
  have hu := Real.Angle.cos_sq_add_sin_sq φ
  constructor <;> dsimp [localX,localY,modelSquare,pointInDirection]
  · linear_combination (x-c.1)*hu
  · linear_combination (y-c.2)*hu

lemma Represents.closed {S : UnitSquare} {o : Point} {φ : Direction} {c : Point}
    (h : Represents S o φ c) (x y : ℝ) :
    closedSquare S (pointInDirection o φ x y) ↔ closedAxisSquare c x y := by
  have hopen : ∀ p, openSquare S p ↔ openSquare (modelSquare o φ c) p := by
    intro p
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    have hm := modelSquare_local o φ c q.1 q.2
    rw [frameEquiv_apply]
    simp only [openSquare,hm.1,hm.2]
    exact h q.1 q.2
  have hc := same_open_same_closed S (modelSquare o φ c) hopen
  simpa only [closedSquare,(modelSquare_local o φ c x y).1,
    (modelSquare_local o φ c x y).2] using hc (pointInDirection o φ x y)

/-- Non-overlap turns any assignment to the model's slots into a permutation. -/
lemma normal_form_of_slots {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {φ : Direction} {c : Fin n → Point} (hd : InteriorDisjoint S)
    (h : ∀ i, ∃ j, Represents (S i) o φ (c j)) : HasNormalForm S o c := by
  classical
  choose f hf using h
  have hi : Function.Injective f := by
    intro i j hij
    by_contra hne
    let z := pointInDirection o φ (c (f i)).1 (c (f i)).2
    have hz₁ : openSquare (S i) z := (hf i _ _).mpr (by simp [openAxisSquare])
    have hz₂ : openSquare (S j) z := (hf j _ _).mpr (by rw [← hij]; simp [openAxisSquare])
    exact hd i j hne z ⟨hz₁,hz₂⟩
  let e := Equiv.ofBijective f hi.bijective_of_finite
  refine ⟨φ,e.symm,?_⟩
  intro i x y
  have hh : Represents (S (e.symm i)) o φ (c i) := by
    simpa only [show f (e.symm i)=i from e.apply_symm_apply i] using hf (e.symm i)
  exact ⟨hh x y,hh.closed x y⟩

/-- If the axis-parallel squares at `c` pack the disk of radius `R` about the
origin, every packing with the normal form of `c` packs the disk of radius `R`
about its centre. -/
theorem HasNormalForm.packing {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {c : Fin n → Point} {R : ℝ} (h : HasNormalForm S o c)
    (hc : Packing (fun i => axisSquare (c i)) (0,0) R) : Packing S o R := by
  obtain ⟨φ,σ,hφ⟩ := h
  refine ⟨hc.1,fun j p hj => ?_,fun j k hjk p hp => ?_⟩
  · obtain ⟨i,rfl⟩ := σ.surjective j
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    have hd := frameEquiv_distance o φ q (0,0)
    rw [frameEquiv_zero] at hd
    change normSq _ ≤ R^2
    rw [hd]
    exact hc.2.1 i q ((axisSquare_closed _ _).mpr ((hφ i q.1 q.2).2.mp hj))
  · obtain ⟨i,rfl⟩ := σ.surjective j
    obtain ⟨l,rfl⟩ := σ.surjective k
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    exact hc.2.2 i l (fun h => hjk (by rw [h])) q
      ⟨(axisSquare_open _ _).mpr ((hφ i q.1 q.2).1.mp hp.1),
        (axisSquare_open _ _).mpr ((hφ l q.1 q.2).1.mp hp.2)⟩

/-- The normal form, with its frame replaced by an explicit isometry of the plane. -/
lemma HasNormalForm.rigid_witness {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {c : Fin n → Point} (h : HasNormalForm S o c) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openAxisSquare (c i) p.1 p.2) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedAxisSquare (c i) p.1 p.2)) := by
  obtain ⟨φ,σ,hφ⟩ := h
  exact ⟨frameEquiv o φ,σ,frameEquiv_zero o φ,frameEquiv_distance o φ,
    fun i p => hφ i p.1 p.2⟩

lemma chart_represents {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    Represents S o C.phase (C.a,C.signedB) := C.cartesian

end SquaresInCircles
