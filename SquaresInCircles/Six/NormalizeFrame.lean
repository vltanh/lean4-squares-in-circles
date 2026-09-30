module
public import SquaresInCircles.Six.Containing
public import SquaresInCircles.Common.Contacts
public import SquaresInCircles.Common.Angles

@[expose] public section

/-!
# Initial normalization of an arbitrary packing

Translate the disk center to zero, align with the containing square, and use
only a quarter-turn to put its center in the nonnegative quadrant. This stage
uses no reflection. The square at index zero is replaced by an axisSquare
with exactly the same open and closed point sets, not a bounding-box surrogate.
-/

noncomputable section
namespace SquaresInCircles.Six

/-- The exact inverse image of a square under a positively oriented rigid frame. -/
def pullSquare (o : Point) (φ : Direction) (S : UnitSquare) : UnitSquare where
  center := (frameEquiv o φ).symm S.center
  cosine := φ.cos*S.cosine+φ.sin*S.sine
  sine := -φ.sin*S.cosine+φ.cos*S.sine
  unit := by
    linear_combination (S.cosine^2+S.sine^2)*Real.Angle.cos_sq_add_sin_sq φ + S.unit

lemma pullSquare_localX (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    localX (pullSquare o φ S) p = localX S (frameEquiv o φ p) := by
  dsimp [localX,pullSquare,frameEquiv,pointInDirection]
  linear_combination
    -(S.cosine*(S.center.1-o.1)+S.sine*(S.center.2-o.2))*Real.Angle.cos_sq_add_sin_sq φ

lemma pullSquare_localY (o : Point) (φ : Direction) (S : UnitSquare) (p : Point) :
    localY (pullSquare o φ S) p = localY S (frameEquiv o φ p) := by
  dsimp [localY,pullSquare,frameEquiv,pointInDirection]
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
  ⟨hp.1,fun i => hp.2.1 (σ i),fun i j hij => hp.disjoint _ _ (σ.injective.ne hij)⟩

lemma packing_of_same_sets {n : ℕ} {S T : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R)
    (hopen : ∀ i p, openSquare (T i) p ↔ openSquare (S i) p)
    (hclosed : ∀ i p, closedSquare (T i) p ↔ closedSquare (S i) p) :
    Packing T o R := by
  refine ⟨hp.1,fun i p hi => hp.2.1 i p ((hclosed i p).mp hi),?_⟩
  intro i j hij p hi
  exact hp.disjoint i j hij p ⟨(hopen i p).mp hi.1,(hopen j p).mp hi.2⟩

lemma quarter_nonnegative (c : Point) :
    ∃ k : Fin 4, 0 ≤ (turnPoint k c).1 ∧ 0 ≤ (turnPoint k c).2 := by
  rcases le_or_gt 0 c.1 with hx | hx <;> rcases le_or_gt 0 c.2 with hy | hy
  · exact ⟨0,by simpa [turnPoint] using And.intro hx hy⟩
  · exact ⟨1,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hy.le) hx⟩
  · exact ⟨3,by simpa [turnPoint] using And.intro hy (neg_nonneg.mpr hx.le)⟩
  · exact ⟨2,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hx.le) (neg_nonneg.mpr hy.le)⟩

/-- Aligning and quarter-turning the containing square needs no reflection. -/
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

structure NormalizedFrame (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ) where
  squares : Fin 6 → UnitSquare
  center : Point
  packing : Packing squares (0,0) R
  central_eq : squares 0 = axisSquare center
  central_inside : openSquare (squares 0) (0,0)
  cx_nonneg : 0 ≤ center.1
  cy_nonneg : 0 ≤ center.2
  cx_lt_half : center.1 < 1/2
  cy_lt_half : center.2 < 1/2
  congruent : Congruent S o squares

/-- The starting geometric normalization, from an actual containing square. -/
theorem normalize_with_containing {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) {k : Fin 6} (hk : openSquare (S k) o) :
    Nonempty (NormalizedFrame S o R) := by
  classical
  obtain ⟨φ,c,hrep,hcx,hcy⟩ := containing_frame (S k) o
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 0 k
  have hσ : σ 0 = k := by simp [σ]
  let Q : Fin 6 → UnitSquare := fun i => pullSquare o φ (S (σ i))
  have hQ : Packing Q (0,0) R := packing_pull (packing_relabel hp σ) φ
  have hQ0 : ∀ p, openSquare (Q 0) p ↔ openSquare (axisSquare c) p := by
    intro p
    rw [show Q 0 = pullSquare o φ (S k) by simp [Q,hσ],pullSquare_open,
      frameEquiv_apply,axisSquare_open]
    exact hrep p.1 p.2
  have hQ0closed := same_open_same_closed (Q 0) (axisSquare c) hQ0
  let N : Fin 6 → UnitSquare := fun i => if i=0 then axisSquare c else Q i
  have hN0 : N 0 = axisSquare c := by simp [N]
  have hopen (i : Fin 6) (p : Point) : openSquare (N i) p ↔ openSquare (Q i) p := by
    by_cases hi : i=0
    · subst i
      simpa [N] using (hQ0 p).symm
    · simp [N,hi]
  have hclosed (i : Fin 6) (p : Point) : closedSquare (N i) p ↔ closedSquare (Q i) p :=
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

/-- Every candidate-sized packing admits the initial nonnegative central frame. -/
theorem normalize_frame_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R^2 ≤ Normalization.Q0) :
    Nonempty (NormalizedFrame S o R) := by
  obtain ⟨k,hk,_⟩ := exists_unique_containing_of_ceiling hp hR
  exact normalize_with_containing hp hk

end SquaresInCircles.Six
