module

public import SquaresInCircles.Common.Contacts
public import SquaresInCircles.Common.Angles

/-!
# Changes of frame

`pullSquare o φ S` is the square `S` read in the frame `φ` at `o`: a packing
about `o`, read in a frame at `o`, is a packing about the origin. Packings stay
packings under a relabelling and under the reflection in the diagonal, and
congruences compose. A packing with a square that contains the disk centre is
congruent to one about the origin whose square `0` is axis-parallel, contains
the origin and has its centre in `[0, 1/2)²` (`normalize_with_containing`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-! ### A square read in another frame -/

/-- The square `S` read in the frame `φ` at `o`: its inverse image under the
frame map. -/
def pullSquare (o : Point) (φ : Direction) (S : UnitSquare) : UnitSquare where
  center := (frameEquiv o φ).symm S.center
  cosine := φ.cos*S.cosine+φ.sin*S.sine
  sine := -φ.sin*S.cosine+φ.cos*S.sine
  unit := by
    linear_combination (S.cosine^2+S.sine^2)*Real.Angle.cos_sq_add_sin_sq φ + S.unit

lemma pullSquare_localX (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    localX (pullSquare o φ S) p = localX S (frameEquiv o φ p) := by
  simp only [localX,pullSquare,frameEquiv,pointInDirection,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk]
  linear_combination
    -(S.cosine*(S.center.1-o.1)+S.sine*(S.center.2-o.2))*Real.Angle.cos_sq_add_sin_sq φ

lemma pullSquare_localY (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    localY (pullSquare o φ S) p = localY S (frameEquiv o φ p) := by
  simp only [localY,pullSquare,frameEquiv,pointInDirection,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk]
  linear_combination
    -(-S.sine*(S.center.1-o.1)+S.cosine*(S.center.2-o.2))*Real.Angle.cos_sq_add_sin_sq φ

lemma pullSquare_open (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    openSquare (pullSquare o φ S) p ↔ openSquare S (frameEquiv o φ p) := by
  simp only [openSquare,pullSquare_localX,pullSquare_localY]

lemma pullSquare_closed (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    closedSquare (pullSquare o φ S) p ↔ closedSquare S (frameEquiv o φ p) := by
  simp only [closedSquare,pullSquare_localX,pullSquare_localY]

lemma packing_pull {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (φ : Direction) :
    Packing (fun i => pullSquare o φ (S i)) (0,0) R := by
  refine ⟨hp.1,?_,?_⟩
  · intro i p hi
    have hm := hp.2.1 i _ ((pullSquare_closed o φ (S i) p).mp hi)
    have hd := frameEquiv_distance o φ p (0,0)
    rw [frameEquiv_zero] at hd
    change normSq (sub p (0,0)) ≤ R^2
    rw [← hd]
    exact hm
  · intro i j hij p hi
    exact hp.disjoint i j hij _
      ⟨(pullSquare_open o φ (S i) p).mp hi.1,
       (pullSquare_open o φ (S j) p).mp hi.2⟩

lemma packing_relabel {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (σ : Equiv.Perm (Fin n)) :
    Packing (fun i => S (σ i)) o R :=
  ⟨hp.1,fun i => hp.2.1 (σ i),fun _ _ hij => hp.disjoint _ _ (σ.injective.ne hij)⟩

lemma packing_of_same_sets {n : ℕ} {S T : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R)
    (hopen : ∀ i p, openSquare (T i) p ↔ openSquare (S i) p)
    (hclosed : ∀ i p, closedSquare (T i) p ↔ closedSquare (S i) p) :
    Packing T o R := by
  refine ⟨hp.1,fun i p hi => hp.2.1 i p ((hclosed i p).mp hi),?_⟩
  intro i j hij p hi
  exact hp.disjoint i j hij p ⟨(hopen i p).mp hi.1,(hopen j p).mp hi.2⟩

/-! ### Composing congruences -/

lemma pointInDirection_comp (o : Point) (φ ψ : Direction) (p : Point) :
    pointInDirection o φ (pointInDirection (0,0) ψ p.1 p.2).1
      (pointInDirection (0,0) ψ p.1 p.2).2 =
      pointInDirection o (φ+ψ) p.1 p.2 := by
  apply Prod.ext <;> simp only [pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add,
    zero_add] <;> ring

lemma congruent_trans {n : ℕ} {S M N : Fin n → UnitSquare} {o : Point}
    (hS : Congruent S o M) (hM : Congruent M (0,0) N) : Congruent S o N := by
  obtain ⟨φ,σ,hφ⟩ := hS
  obtain ⟨ψ,τ,hψ⟩ := hM
  refine ⟨φ+ψ,τ.trans σ,?_⟩
  intro i p
  have h1 := hφ (τ i) (pointInDirection (0,0) ψ p.1 p.2)
  have h2 := hψ i p
  rw [pointInDirection_comp] at h1
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

lemma congruent_refl {n : ℕ} (M : Fin n → UnitSquare) : Congruent M (0,0) M := by
  refine ⟨0,Equiv.refl _,?_⟩
  intro i p
  simp [pointInDirection]

/-- A relabelling of the squares `1, …, n`, extended by fixing the square `0`. -/
def extendExteriorPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] lemma extendExteriorPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    extendExteriorPerm σ 0 = 0 := rfl

lemma congruent_of_origin_sets {n : ℕ} {S M : Fin n → UnitSquare}
    (σ : Equiv.Perm (Fin n))
    (ho : ∀ i p, openSquare (S (σ i)) p ↔ openSquare (M i) p)
    (hc : ∀ i p, closedSquare (S (σ i)) p ↔ closedSquare (M i) p) :
    Congruent S (0,0) M := by
  refine ⟨0,σ,?_⟩
  intro i p
  simpa [pointInDirection] using And.intro (ho i p) (hc i p)

/-! ### The frame of a containing square -/

/-- A frame at `o` along the axes of `C` in which the centre of `C` has
nonnegative coordinates. -/
lemma containing_frame (C : UnitSquare) (o : Point) :
    ∃ (φ : Direction) (c : Point), Represents C o φ c ∧ 0 ≤ c.1 ∧ 0 ≤ c.2 := by
  obtain ⟨θ,hcos,hsin⟩ := frame_angle C
  let φ0 : Direction := (θ : Direction)
  let c : Point := (frameX C (sub C.center o),frameY C (sub C.center o))
  have hrep : Represents C o φ0 c := self_represents C o φ0
    (by simpa [φ0] using hcos) (by simpa [φ0] using hsin)
  obtain ⟨k,hk⟩ := quarter_nonnegative c
  let φ := φ0-quarterShift k
  have hrep' : Represents C o (φ+quarterShift k) c := by
    simpa [φ] using hrep
  exact ⟨φ,turnPoint k c,represents_quarter k hrep',hk.1,hk.2⟩

/-- A copy of the packing, congruent to it, in the disk about the origin, whose
square of index `0` is axis-parallel, contains the origin, and has its centre
in `[0, 1/2)²`. -/
structure NormalizedFrame {n : ℕ} (S : Fin (n+1) → UnitSquare) (o : Point) (R : ℝ) where
  squares : Fin (n+1) → UnitSquare
  center : Point
  packing : Packing squares (0,0) R
  central_eq : squares 0 = axisSquare center
  central_inside : openSquare (squares 0) (0,0)
  cx_nonneg : 0 ≤ center.1
  cy_nonneg : 0 ≤ center.2
  cx_lt_half : center.1 < 1/2
  cy_lt_half : center.2 < 1/2
  congruent : Congruent S o squares

/-- A packing with a square that contains the disk centre has a normalized
frame. -/
theorem normalize_with_containing {n : ℕ} {S : Fin (n+1) → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) {k : Fin (n+1)} (hk : openSquare (S k) o) :
    Nonempty (NormalizedFrame S o R) := by
  classical
  obtain ⟨φ,c,hrep,hcx,hcy⟩ := containing_frame (S k) o
  let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 k
  have hσ : σ 0 = k := by simp [σ]
  let Q : Fin (n+1) → UnitSquare := fun i => pullSquare o φ (S (σ i))
  have hQ : Packing Q (0,0) R := packing_pull (packing_relabel hp σ) φ
  have hQ0 : ∀ p, openSquare (Q 0) p ↔ openSquare (axisSquare c) p := by
    intro p
    rw [show Q 0 = pullSquare o φ (S k) by simp [Q,hσ],pullSquare_open,
      frameEquiv_apply,axisSquare_open]
    exact hrep p.1 p.2
  let N : Fin (n+1) → UnitSquare := fun i => if i=0 then axisSquare c else Q i
  have hN0 : N 0 = axisSquare c := by simp [N]
  have hopen (i : Fin (n+1)) (p : Point) : openSquare (N i) p ↔ openSquare (Q i) p := by
    by_cases hi : i=0
    · subst i
      simpa [N] using (hQ0 p).symm
    · simp [N,hi]
  have hclosed (i : Fin (n+1)) (p : Point) : closedSquare (N i) p ↔ closedSquare (Q i) p :=
    same_open_same_closed (N i) (Q i) (hopen i) p
  have hpacking : Packing N (0,0) R := packing_of_same_sets hQ hopen hclosed
  have hinsideQ : openSquare (Q 0) (0,0) := by
    rw [show Q 0 = pullSquare o φ (S k) by simp [Q,hσ],pullSquare_open,frameEquiv_zero]
    exact hk
  have hinside := (hopen 0 (0,0)).mpr hinsideQ
  have hbounds : |c.1| < 1/2 ∧ |c.2| < 1/2 := by
    simpa [hN0,axisSquare_open,openAxisSquare,abs_neg] using hinside
  have hcong : Congruent S o N := by
    refine ⟨φ,σ,?_⟩
    intro i p
    have ho := (pullSquare_open o φ (S (σ i)) p).symm.trans (hopen i p).symm
    have hc := (pullSquare_closed o φ (S (σ i)) p).symm.trans (hclosed i p).symm
    exact ⟨ho,hc⟩
  exact ⟨⟨N,c,hpacking,hN0,hinside,hcx,hcy,
    lt_of_le_of_lt (le_abs_self c.1) hbounds.1,
    lt_of_le_of_lt (le_abs_self c.2) hbounds.2,hcong⟩⟩

/-! ### The reflection in the diagonal -/

/-- The reflection `(x, y) ↦ (y, x)` in the diagonal. -/
def diagonalPoint (p : Point) : Point := (p.2,p.1)

/-- The reflection of a square in the diagonal. -/
def reflectDiagonalSquare (S : UnitSquare) : UnitSquare where
  center := diagonalPoint S.center
  cosine := S.sine
  sine := S.cosine
  unit := by linarith [S.unit]

@[simp] lemma diagonalPoint_involutive (p : Point) : diagonalPoint (diagonalPoint p) = p := by
  cases p
  rfl

lemma reflectDiagonal_localX (S : UnitSquare) (p : Point) :
    localX (reflectDiagonalSquare S) p = localX S (diagonalPoint p) := by
  dsimp [localX,reflectDiagonalSquare,diagonalPoint]
  ring

lemma reflectDiagonal_localY (S : UnitSquare) (p : Point) :
    localY (reflectDiagonalSquare S) p = -localY S (diagonalPoint p) := by
  dsimp [localY,reflectDiagonalSquare,diagonalPoint]
  ring

lemma reflectDiagonal_open (S : UnitSquare) (p : Point) :
    openSquare (reflectDiagonalSquare S) p ↔ openSquare S (diagonalPoint p) := by
  simp only [openSquare,reflectDiagonal_localX,reflectDiagonal_localY,abs_neg]

lemma reflectDiagonal_closed (S : UnitSquare) (p : Point) :
    closedSquare (reflectDiagonalSquare S) p ↔ closedSquare S (diagonalPoint p) := by
  simp only [closedSquare,reflectDiagonal_localX,reflectDiagonal_localY,abs_neg]

lemma diagonalPoint_inDisk (p : Point) (R : ℝ) :
    inDisk (0,0) R (diagonalPoint p) ↔ inDisk (0,0) R p := by
  simp [inDisk,normSq,sub,diagonalPoint,add_comm]

lemma packing_reflectDiagonal {n : ℕ} {S : Fin n → UnitSquare} {R : ℝ}
    (hp : Packing S (0,0) R) : Packing (fun i => reflectDiagonalSquare (S i)) (0,0) R := by
  refine ⟨hp.1,?_,?_⟩
  · intro i p hi
    exact (diagonalPoint_inDisk p R).mp
      (hp.2.1 i _ ((reflectDiagonal_closed (S i) p).mp hi))
  · intro i j hij p hi
    exact hp.disjoint i j hij _
      ⟨(reflectDiagonal_open (S i) p).mp hi.1,(reflectDiagonal_open (S j) p).mp hi.2⟩

lemma diagonal_axis_open (c p : Point) :
    openSquare (axisSquare c) (diagonalPoint p) ↔
      openSquare (axisSquare (diagonalPoint c)) p := by
  simp [axisSquare_open,openAxisSquare,diagonalPoint,and_comm]

lemma reflected_central_axis {S : UnitSquare} {c : Point}
    (h : ∀ p, openSquare S p ↔ openSquare (axisSquare c) p) :
    ∀ p, openSquare (reflectDiagonalSquare S) p ↔
      openSquare (axisSquare (diagonalPoint c)) p := by
  intro p
  exact (reflectDiagonal_open S p).trans ((h _).trans (diagonal_axis_open c p))

lemma diagonal_conjugates_rotation (φ : Direction) (p : Point) :
    diagonalPoint (pointInDirection (0,0) (-φ) p.1 p.2) =
      pointInDirection (0,0) φ (diagonalPoint p).1 (diagonalPoint p).2 := by
  apply Prod.ext <;>
    simp only [diagonalPoint,pointInDirection,Real.Angle.cos_neg,Real.Angle.sin_neg,zero_add] <;>
    ring

/-- Reflecting both sides of a congruence gives a congruence, with the opposite
rotation. -/
theorem congruent_diagonal {n : ℕ} {S T : Fin n → UnitSquare}
    (h : Congruent S (0,0) T) :
    Congruent (fun i => reflectDiagonalSquare (S i)) (0,0)
      (fun i => reflectDiagonalSquare (T i)) := by
  obtain ⟨φ,σ,hφ⟩ := h
  refine ⟨-φ,σ,fun i p => ?_⟩
  have hh := hφ i (diagonalPoint p)
  constructor
  · rw [reflectDiagonal_open,diagonal_conjugates_rotation,reflectDiagonal_open]
    exact hh.1
  · rw [reflectDiagonal_closed,diagonal_conjugates_rotation,reflectDiagonal_closed]
    exact hh.2

/-- Congruent to `M`, or to the reflection of `M` in the diagonal. -/
def CongruentOrDiagonal {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (M : Fin n → UnitSquare) : Prop :=
  Congruent S o M ∨ Congruent S o (fun i => reflectDiagonalSquare (M i))

end SquaresInCircles
