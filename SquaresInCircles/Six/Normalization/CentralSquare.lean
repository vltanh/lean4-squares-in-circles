import SquaresInCircles.Common.ArcBudget
import SquaresInCircles.Common.RectangleArcs
import SquaresInCircles.Common.ElementaryTrig
import SquaresInCircles.Common.Analysis
import SquaresInCircles.Six.Normalization.Basic
import SquaresInCircles.Common.Angles

/-!
# The central square

A packing is read in the frame of a square that contains the disk centre: the
disk centre moves to the origin and the frame turns to the axes of that square,
and by a further quarter turn its centre gets nonnegative coordinates
(`normalize_with_containing`). Congruences compose, and the reflection in the
diagonal maps packings about the origin to packings. Six squares in a disk of
squared radius at most `Q0` are read on the circle of radius `9/10` about the
disk centre. An exterior square holds an open arc of it of half-width more than
`14/25 > π/6`: the circle crosses its near edge at the chart angles `± A` and its
lower and upper edges at `-V` and `U`, and each of `2A`, `A + U`, `A + V` and
`U + V` exceeds `28/25`, by arcsine bounds on the region
`(a + 1/2)² + (b + 1/2)² ≤ Q0`. Six such arcs would overlap, so exactly one
square contains the disk centre (`exists_unique_containing`). In a frame of that
square C, with centre `(cx, cy) ∈ [0, 1/2)²` and `cy ≤ cx` after a diagonal
reflection, suppose `cx > c0`. Every other square lies beyond a side of C or
beyond a support line of C along one of its own axes, and such a support line
is at distance at most `ρ0 - 1/2` from the origin. The lines at that distance
miss an arc of length `7/10` east of C (`shallow_support`): the chart angles
`(-1/4, 9/20)` if `cy ≤ c0` and `(0, 7/10)` otherwise. With the five arcs of the
other squares this exceeds the circle, so `c ∈ [0, c0]²` (`central_box`).
-/

noncomputable section
open Set
namespace SquaresInCircles.Six
open Normalization

/-! ### The frame of a containing square -/

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

lemma quarter_nonnegative (c : Point) :
    ∃ k : Fin 4, 0 ≤ (turnPoint k c).1 ∧ 0 ≤ (turnPoint k c).2 := by
  rcases le_or_gt 0 c.1 with hx | hx <;> rcases le_or_gt 0 c.2 with hy | hy
  · exact ⟨0,by simpa [turnPoint] using And.intro hx hy⟩
  · exact ⟨1,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hy.le) hx⟩
  · exact ⟨3,by simpa [turnPoint] using And.intro hy (neg_nonneg.mpr hx.le)⟩
  · exact ⟨2,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hx.le) (neg_nonneg.mpr hy.le)⟩

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

/-- A packing with a square that contains the disk centre has a normalized
frame. -/
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

/-- A relabelling of the five exterior squares, extended by fixing the central
square `0`. -/
def extendExteriorPerm (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 6) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] lemma extendExteriorPerm_zero (σ : Equiv.Perm (Fin 5)) :
    extendExteriorPerm σ 0 = 0 := rfl

lemma congruent_of_origin_sets {n : ℕ} {S M : Fin n → UnitSquare}
    (σ : Equiv.Perm (Fin n))
    (ho : ∀ i p, openSquare (S (σ i)) p ↔ openSquare (M i) p)
    (hc : ∀ i p, closedSquare (S (σ i)) p ↔ closedSquare (M i) p) :
    Congruent S (0,0) M := by
  refine ⟨0,σ,?_⟩
  intro i p
  simpa [pointInDirection] using And.intro (ho i p) (hc i p)

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

/-! ### Arcs of exterior squares -/

/-- Two crossings above the centre line: with `x = (a - 1/2)/(9/10)` and
`y = (b - 1/2)/(9/10)`, the cubic bound on the arcsine gives
`arcsin x + arcsin y ≤ 9/20` on the disk. -/
private lemma arcsin_pair_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 3 / 5)
    (hy1 : y ≤ 3 / 5) (hQ : (9 / 10 * x + 1) ^ 2 + (9 / 10 * y + 1) ^ 2 ≤ Q0) :
    Real.arcsin x + Real.arcsin y ≤ 9 / 20 := by
  have hX := arcsin_le_cubic hx hx1
  have hY := arcsin_le_cubic hy hy1
  have hxy := mul_nonneg hx hy
  norm_num [Q0] at hQ
  nlinarith [mul_nonneg hxy (add_nonneg hx hy), sq_nonneg (x - y)]

/-- The circle of radius `9/10` crosses the near edge of a square with
`a ≤ 119/100` at chart angles beyond `± 3/5`. -/
private lemma capA_gt {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 119 / 100) :
    3 / 5 < capA (9 / 10) a := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := 3 / 5)
  calc (3 : ℝ) / 5 = Real.arccos (Real.cos (3 / 5)) :=
        (Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])).symm
    _ < capA (9 / 10) a := Real.arccos_lt_arccos
        (by rw [le_div_iff₀ (by norm_num)]; linarith)
        (by rw [div_lt_iff₀ (by norm_num)]; nlinarith) (Real.cos_le_one _)

/-- The circle of radius `9/10` crosses the upper edge beyond the chart angle
`5/9`. -/
private lemma capU_ge {b : ℝ} (hb : 0 ≤ b) : 5 / 9 ≤ capU (9 / 10) b := by
  rcases le_total 1 ((b + 1 / 2) / (9 / 10)) with h | h
  · rw [capU, Real.arcsin_of_one_le h]
    linarith [Real.pi_gt_three]
  · calc (5 : ℝ) / 9 ≤ (b + 1 / 2) / (9 / 10) := by
          rw [le_div_iff₀ (by norm_num)]; linarith
      _ ≤ capU (9 / 10) b := arcsin_ge_self (by positivity) h

/-- The lower and upper edges: `U + V > 28/25` for `0 ≤ b ≤ 7/10`. -/
private lemma capUV_gt {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 7 / 10) :
    28 / 25 < capU (9 / 10) b + capV (9 / 10) b := by
  rcases le_total (9 / 10) (b + 1 / 2) with h | h
  · have hU1 : capU (9 / 10) b = Real.pi / 2 :=
      Real.arcsin_of_one_le ((le_div_iff₀ (by norm_num)).mpr (by linarith))
    have hm := arcsin_le_cubic (x := 1 / 4) (by norm_num) (by norm_num)
    have hmono := Real.arcsin_le_arcsin (show -(1 / 4 : ℝ) ≤ (1 / 2 - b) / (9 / 10) by
      rw [le_div_iff₀ (by norm_num)]; linarith)
    rw [Real.arcsin_neg] at hmono
    rw [hU1]
    unfold capV
    linarith [Real.pi_gt_d2]
  · have hs := sin_upper_five (x := 14 / 25) (by norm_num)
    have hh := arcsin_sum_gt_of_sin_lt (u := (b + 1 / 2) / (9 / 10))
      (v := (1 / 2 - b) / (9 / 10)) (θ := 14 / 25)
      ⟨by positivity, (div_le_one (by norm_num)).mpr h⟩
      ⟨by rw [le_div_iff₀ (by norm_num)]; linarith,
        (div_le_one (by norm_num)).mpr (by linarith)⟩
      ⟨by norm_num, by linarith [Real.pi_gt_three]⟩ (by
        rw [show ((b + 1 / 2) / (9 / 10) + (1 / 2 - b) / (9 / 10)) / 2 = 5 / 9 by ring]
        norm_num at hs ⊢
        linarith)
    unfold capU capV
    linarith

/-- The near and lower edges of a square above the centre line, `b ≥ 1/2`. -/
private lemma capAV_high {a b : ℝ} (hb2 : 1 / 2 ≤ b) (hsort : b ≤ a)
    (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
  have hV : capV (9 / 10) b = -Real.arcsin ((b - 1 / 2) / (9 / 10)) := by
    rw [capV, ← Real.arcsin_neg]
    congr 1
    ring
  rw [hV, sub_neg_eq_add]
  norm_num [Q0] at hQ
  apply arcsin_pair_le (by apply div_nonneg <;> linarith) (by apply div_nonneg <;> linarith)
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · norm_num [Q0]; linarith

/-- The near and lower edges of a square below the centre line, `b ≤ 1/2`. -/
private lemma capAV_low {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2)
    (ha1 : a ≤ 1113 / 1000) (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
  norm_num [Q0] at hQ
  have hV : (1 / 2 - b) / (9 / 10) ≤ capV (9 / 10) b :=
    arcsin_ge_self (by apply div_nonneg <;> linarith)
      (by rw [div_le_one (by norm_num)]; linarith)
  rcases le_total a (1 / 2 + 27 / 50) with ha2 | ha2
  · have hX := arcsin_le_cubic (x := (a - 1 / 2) / (9 / 10)) (by apply div_nonneg <;> linarith)
      (by rw [div_le_iff₀ (by norm_num)]; linarith)
    have hx0 : 0 ≤ a - 1 / 2 := by linarith
    have hx2 : (a - 1 / 2) ^ 2 ≤ (27 / 50) ^ 2 := by nlinarith
    have hx3 : (a - 1 / 2) ^ 3 ≤ (27 / 50) ^ 2 * (a - 1 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hx2 hx0]
    -- `1.09 (a + 1/2) + (b + 1/2) ≤ 2.495` on the disk below `b = 1/2`
    have hlin : 109 / 100 * (a + 1 / 2) + (b + 1 / 2) ≤ 2495 / 1000 := by
      nlinarith [sq_nonneg (109 / 100 * (a + 1 / 2) - 2495 / 1000 + (b + 1 / 2))]
    have hX' : Real.arcsin ((a - 1 / 2) / (9 / 10)) ≤
        (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) := by
      have he : ((a - 1 / 2) / (9 / 10)) ^ 3 / 4 = (a - 1 / 2) ^ 3 / (4 * (9 / 10) ^ 3) := by
        ring
      rw [he] at hX
      have hd : (a - 1 / 2) ^ 3 / (4 * (9 / 10) ^ 3) ≤
          (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) :=
        div_le_div_of_nonneg_right hx3 (by norm_num)
      linarith
    have hval : (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) -
        (1 / 2 - b) / (9 / 10) ≤ 9 / 20 := by
      rw [show (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) -
          (1 / 2 - b) / (9 / 10) = (1090 * (a - 1 / 2) - 1000 * (1 / 2 - b)) / 900 by ring]
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  · -- a far square sits low: `b + 1/2 < 0.6926`
    have hlow : b + 1 / 2 ≤ 6926 / 10000 := by nlinarith
    have hvlow : 3415 / 10000 ≤ (1 / 2 - b) / (9 / 10) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have hasin : Real.arcsin ((a - 1 / 2) / (9 / 10)) ≤ 77 / 100 := by
      have hs := Real.sin_ge_sub_cube (x := 77 / 100) (by norm_num)
      rw [Real.arcsin_le_iff_le_sin
        ⟨by rw [le_div_iff₀ (by norm_num)]; linarith, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
        ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩]
      norm_num at hs
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith

/-- On the circle of radius `9/10`, the chart angles held by an exterior square
with `(a + 1/2)² + (b + 1/2)² ≤ Q0` span more than `28/25`. -/
lemma arc_length {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 0 ≤ b) (hsort : b ≤ a)
    (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    28 / 25 < min (capA (9 / 10) a) (capU (9 / 10) b) +
      min (capA (9 / 10) a) (capV (9 / 10) b) := by
  have hrho := rho0_bounds
  have harho : a ≤ rho0 := by
    have hs : (a + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by nlinarith
    have hr := Real.le_sqrt_of_sq_le hs
    dsimp [rho0]
    linarith
  have hA35 := capA_gt ha (by linarith)
  have hU := capU_ge hb
  have hUV := capUV_gt hb (by norm_num [Q0] at hQ; nlinarith)
  have hAV : 28 / 25 < capA (9 / 10) a + capV (9 / 10) b := by
    rw [capA, Real.arccos_eq_pi_div_two_sub_arcsin]
    have h : Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
      rcases le_total (1 / 2) b with hb2 | hb2
      · exact capAV_high hb2 hsort hQ
      · exact capAV_low ha hb hb2 (by linarith) hQ
    linarith [Real.pi_gt_d4]
  rcases min_cases (capA (9 / 10) a) (capU (9 / 10) b) with ⟨hu, -⟩ | ⟨hu, -⟩ <;>
    rcases min_cases (capA (9 / 10) a) (capV (9 / 10) b) with ⟨hv, -⟩ | ⟨hv, -⟩ <;>
    rw [hu, hv] <;> linarith

/-- An exterior square in the disk of squared radius `Q0` holds an arc of the
circle of radius `9/10` of half-width more than `14/25`. -/
theorem exterior_arc (S : UnitSquare) (o : Point) (hQ : phi (alpha S o) (beta S o) ≤ Q0)
    (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o (9 / 10) {p | openSquare S p}, 14 / 25 < A.halfWidth := by
  obtain ⟨C, hsort⟩ := sorted_square_chart S o
  have ha := C.exterior hsort hout
  have hC : (C.a + 1 / 2) ^ 2 + (C.b + 1 / 2) ^ 2 ≤ Q0 := chart_phi C hQ
  have hlen := arc_length ha C.nonneg.2 hsort hC
  have ha1 : C.a ≤ 7 / 5 := by norm_num [Q0] at hC; nlinarith [C.nonneg.2]
  obtain ⟨A, hA, -⟩ := C.edge_arc (r := 9 / 10) (by norm_num) ha (by linarith) (by linarith)
    (by linarith)
  exact ⟨A, by rw [hA]; linarith⟩

/-- In a disk of squared radius at most `Q0`, one of six disjoint squares
contains the disk centre: otherwise their six arcs, each of half-width more
than `π/6`, would overlap. -/
theorem exists_containing {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R ^ 2 ≤ Q0) : ∃ i, openSquare (S i) o := by
  by_contra! hext
  choose A hA using fun i => exterior_arc (S i) o ((hp.phi_le i).trans hR) (hext i)
  have hpi : Real.pi / ((6 : ℕ) : ℝ) < 14 / 25 := by
    norm_num
    linarith [Real.pi_lt_d2]
  exact uniform_arc_excess A hp.disjoint.pairwise (fun i => (hpi.trans (hA i)).le)
    ⟨0, hpi.trans (hA 0)⟩

/-- Interior-disjointness makes the containing square unique. -/
theorem exists_unique_containing {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R ^ 2 ≤ Q0) : ∃! i, openSquare (S i) o := by
  obtain ⟨i, hi⟩ := exists_containing hp hR
  exact ⟨i, hi, fun j hj => by_contra fun hji => hp.disjoint j i hji o ⟨hj, hi⟩⟩

namespace Normalization

/-- A packing in a disk of squared radius at most `Q0` has a normalized
frame. -/
theorem normalize_frame_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R ^ 2 ≤ Q0) : Nonempty (Six.NormalizedFrame S o R) := by
  obtain ⟨k, hk, _⟩ := Six.exists_unique_containing hp hR
  exact Six.normalize_with_containing hp hk

/-! ### The central box -/

section Shallow
variable {L X Y q1 q2 x w : ℝ}

/-- With `X > L`, a unit vector `(x, w)` of the first quadrant with
`X x + w/2 ≤ L` has `x ≤ 21/100`: a support line at the north-east corner within
`L ≈ 0.613` of the origin is nearly horizontal. -/
private lemma first_quadrant_steep (hL : 6128 / 10000 < L) (hL' : L < 6129 / 10000)
    (hX : L < X) (hx : 0 ≤ x) (hw : 0 ≤ w) (hn : x ^ 2 + w ^ 2 = 1)
    (h : X * x + w / 2 ≤ L) : x ≤ 21 / 100 := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]; norm_num
  have h1 : 0 < 1 - x := by nlinarith [mul_pos (sub_pos.mpr hX) hx0]
  have hw2 : w ≤ 2 * L * (1 - x) := by nlinarith [mul_pos (sub_pos.mpr hX) hx0]
  have hsq : w ^ 2 ≤ (2 * L * (1 - x)) ^ 2 := pow_le_pow_left₀ hw hw2 2
  have hfac : (1 - x) * (1 + x) ≤ (1 - x) * (4 * L ^ 2 * (1 - x)) := by nlinarith
  have hlin := le_of_mul_le_mul_left hfac h1
  nlinarith

/-- With `X > L` and `Y ≥ 1 - L`, a unit vector `(x, w)` with
`X x + Y w ≤ L` has `x ≤ 43/100`: the same at the south-east corner `(X, -Y)`. -/
private lemma fourth_quadrant_steep (hL : 6128 / 10000 < L) (hL' : L < 6129 / 10000)
    (hX : L < X) (hY : 1 - L ≤ Y) (hx : 0 ≤ x) (hw : 0 ≤ w) (hn : x ^ 2 + w ^ 2 = 1)
    (h : X * x + Y * w ≤ L) : x ≤ 43 / 100 := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]; norm_num
  have hYw : (1 - L) * w ≤ Y * w := mul_le_mul_of_nonneg_right hY hw
  have h1 : 0 < 1 - x := by nlinarith [mul_pos (sub_pos.mpr hX) hx0]
  have hw2 : (1 - L) * w ≤ L * (1 - x) := by nlinarith [mul_pos (sub_pos.mpr hX) hx0]
  have hsq : ((1 - L) * w) ^ 2 ≤ (L * (1 - x)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hw) hw2 2
  have hfac : (1 - x) * ((1 - L) ^ 2 * (1 + x)) ≤ (1 - x) * (L ^ 2 * (1 - x)) := by
    nlinarith
  have hlin := le_of_mul_le_mul_left hfac h1
  nlinarith

/-- At the south-east corner `(X, -Y)` with `X ≥ 1 - Y` and `0 ≤ Y < 1 - L`,
the support line along a unit normal `(x, -w)` with `w < x` is farther than `L`
from the origin. -/
private lemma fourth_quadrant_flat (hY0 : 0 ≤ Y) (hY : Y < 1 - L) (hL : L < 7 / 10)
    (hXY : 1 - Y ≤ X) (hw : 0 ≤ w) (hwx : w < x) (hn : x ^ 2 + w ^ 2 = 1) :
    L < X * x + Y * w := by
  have hx : 0 < x := hw.trans_lt hwx
  have hsum : 1 ≤ x + w := by nlinarith
  have hdiff : x - w ≤ 2 * x ^ 2 - 1 := by nlinarith
  have h2 : 0 < 2 * x ^ 2 - 1 := by nlinarith
  have hx7 : 7 / 10 ≤ x := by nlinarith
  have hx1 : x ≤ 1 := by nlinarith
  have hfac : 0 ≤ (1 - x) * (2 * (1 - L) * x + 1 - 2 * L) :=
    mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right hXY hx.le, mul_lt_mul_of_pos_right hY h2,
    mul_le_mul_of_nonneg_left hdiff hY0]

end Shallow

/-- The two regimes of a free point `(q1, q2)` east of the central square: with
`cy ≤ c0` it has `-9/40 ≤ q2 ≤ 2/5`, and with `cy > c0` it has `0 ≤ q2 ≤ 3/5`. -/
def FreeRegime (cy q2 : ℝ) : Prop :=
  (cy ≤ c0 ∧ -9 / 40 ≤ q2 ∧ q2 ≤ 2 / 5) ∨ (c0 < cy ∧ 0 ≤ q2 ∧ q2 ≤ 3 / 5)

/-- A support line of the central square `Q(cx, cy)`, with `cx > c0`, at distance
at most `ρ0 - 1/2` from the origin does not separate a free point from it: along
a unit normal `(x, y)` the point projects below the support
`cx x + cy y + (|x| + |y|)/2`. -/
lemma shallow_support {cx cy q1 q2 x y : ℝ} (hcx : c0 < cx) (hcx1 : cx < 1 / 2)
    (hcy : 0 ≤ cy) (hcyx : cy ≤ cx) (hq1 : 0 < q1) (hq1' : q1 ≤ 9 / 10)
    (hq : FreeRegime cy q2) (hn : x ^ 2 + y ^ 2 = 1)
    (hsh : cx * x + cy * y + (|x| + |y|) / 2 ≤ rho0 - 1 / 2) :
    q1 * x + q2 * y ≤ cx * x + cy * y + (|x| + |y|) / 2 := by
  obtain ⟨hρ, hρ'⟩ := rho0_bounds
  have hc0 : c0 = rho0 - 1 := rfl
  rw [hc0] at hcx
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy] at hsh ⊢
    rcases hq with ⟨hcy0, hq2, hq2'⟩ | ⟨hcy0, hq2, hq2'⟩
    · have hxs := first_quadrant_steep (L := rho0 - 1 / 2) (X := cx + 1 / 2)
        (by linarith) (by linarith) (by linarith) hx hy hn
        (by nlinarith [mul_nonneg hy hcy])
      have hy9 : 9 / 10 ≤ y := by nlinarith
      nlinarith [mul_nonneg hx (show 0 ≤ cx + 1 / 2 - q1 + 3 / 10 by linarith),
        mul_nonneg hy (show 0 ≤ cy + 1 / 2 - q2 - 1 / 10 by linarith)]
    · rw [hc0] at hcy0
      have hsum : 1 ≤ x + y := by nlinarith
      nlinarith [mul_nonneg hx (show 0 ≤ cx + 1 / 2 - (rho0 - 1 / 2) by linarith),
        mul_nonneg hy (show 0 ≤ cy + 1 / 2 - (rho0 - 1 / 2) by linarith)]
  · rw [abs_of_nonneg hx, abs_of_nonpos hy] at hsh ⊢
    have hw : 0 ≤ -y := by linarith
    have hn' : x ^ 2 + (-y) ^ 2 = 1 := by rw [neg_sq]; exact hn
    rcases hq with ⟨hcy0, hq2, hq2'⟩ | ⟨hcy0, hq2, hq2'⟩
    · rw [hc0] at hcy0
      have hxs := fourth_quadrant_steep (L := rho0 - 1 / 2) (X := cx + 1 / 2)
        (Y := 1 / 2 - cy) (by linarith) (by linarith) (by linarith) (by linarith) hx hw hn'
        (by nlinarith)
      have hw9 : 9 / 10 ≤ -y := by nlinarith
      nlinarith [mul_nonneg hx (show 0 ≤ cx + 1 / 2 - q1 + 2873 / 10000 by linarith),
        mul_nonneg hw (show 0 ≤ q2 + 1 / 2 - cy - 1621 / 10000 by linarith)]
    · rw [hc0] at hcy0
      rcases lt_or_ge (-y) x with hwx | hwx
      · have hflat := fourth_quadrant_flat (L := rho0 - 1 / 2) (X := cx + 1 / 2)
          (Y := 1 / 2 - cy) (by linarith) (by linarith) (by linarith) (by linarith) hw hwx hn'
        nlinarith
      · nlinarith [mul_nonneg hx (show 0 ≤ 1 - q1 by linarith),
          mul_nonneg hw (show 0 ≤ q2 by linarith),
          mul_le_mul_of_nonneg_left hwx (show 0 ≤ 1 / 2 - cy by linarith),
          mul_nonneg hx (show 0 ≤ cx - cy by linarith)]
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]
    have hq2 : q2 ≤ cy + 1 / 2 := by
      rcases hq with ⟨-, -, h⟩ | ⟨h1, -, h⟩ <;> [linarith; (rw [hc0] at h1; linarith)]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (show 0 ≤ q1 - cx + 1 / 2 by linarith),
      mul_nonneg hy (show 0 ≤ cy + 1 / 2 - q2 by linarith)]
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]
    have hq2 : cy - 1 / 2 ≤ q2 := by
      rcases hq with ⟨h1, h, -⟩ | ⟨-, h, -⟩ <;> [(rw [hc0] at h1; linarith); linarith]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (show 0 ≤ q1 - cx + 1 / 2 by linarith),
      mul_nonneg (neg_nonneg.mpr hy) (show 0 ≤ q2 - cy + 1 / 2 by linarith)]

/-- A free point lies in no square of a contained chart that is separated from
the central square: along a side of C it stays inside the strip of C, the east
side is too deep for a square, and along an axis of the square the support line
is shallow. -/
lemma free_point_outside {t a b cx cy q1 q2 : ℝ} (hc : ContainedChart a |b|)
    (hcx : c0 < cx) (hcx1 : cx < 1 / 2) (hcy : 0 ≤ cy) (hcyx : cy ≤ cx)
    (hq1 : 0 < q1) (hq1' : q1 ≤ 9 / 10) (hq : FreeRegime cy q2) {k : CentralAxis}
    (hk : 0 ≤ centralMargin k t a b cx cy) :
    ¬ openSquare (orientedSquare t a b) (q1, q2) := by
  intro hin
  have hX := abs_lt.mp hin.1
  have hY := abs_lt.mp hin.2
  rw [orientedSquare_localX] at hX
  rw [orientedSquare_localY] at hY
  dsimp only at hX hY
  have ha := hc.a_le_rho0
  have hba : |b| ≤ a := hc.u_le
  have hb := neg_abs_le b
  have hb' := le_abs_self b
  have hsc := Real.sin_sq_add_cos_sq t
  have hc0 : c0 = rho0 - 1 := rfl
  have hclosed : closedSquare (orientedSquare t a b) (q1, q2) := ⟨hin.1.le, hin.2.le⟩
  cases k with
  | own =>
    have h := shallow_support (x := Real.cos t) (y := Real.sin t) hcx hcx1 hcy hcyx hq1 hq1' hq
      (by linarith) (by dsimp [centralMargin, centralNormal, angularWidth] at hk; linarith)
    dsimp [centralMargin, centralNormal, angularWidth] at hk
    linarith
  | secPlus =>
    have h := shallow_support (x := -Real.sin t) (y := Real.cos t) hcx hcx1 hcy hcyx hq1 hq1'
      hq (by rw [neg_sq]; linarith) (by
        dsimp [centralMargin, centralTransverse, angularWidth] at hk
        rw [abs_neg]
        linarith)
    dsimp [centralMargin, centralTransverse, angularWidth] at hk
    rw [abs_neg] at h
    linarith
  | secMinus =>
    have h := shallow_support (x := Real.sin t) (y := -Real.cos t) hcx hcx1 hcy hcyx hq1 hq1'
      hq (by rw [neg_sq]; linarith) (by
        dsimp [centralMargin, centralTransverse, angularWidth] at hk
        rw [abs_neg]
        linarith)
    dsimp [centralMargin, centralTransverse, angularWidth] at hk
    rw [abs_neg] at h
    linarith
  | east =>
    have h := east_separator_negative (t := t) hc hcx
    dsimp [centralMargin, centerX, angularWidth] at hk
    linarith
  | west =>
    have h := west_margin_cap hk (q1, q2) hclosed
    dsimp only at h
    linarith
  | north =>
    have h := north_margin_cap hk (q1, q2) hclosed
    dsimp only at h
    rcases hq with ⟨-, -, h'⟩ | ⟨h1, -, h'⟩
    · linarith
    · rw [hc0] at h1; linarith [rho0_bounds.1]
  | south =>
    have h := south_margin_cap hk (q1, q2) hclosed
    dsimp only at h
    rcases hq with ⟨h1, h', -⟩ | ⟨-, h', -⟩
    · rw [hc0] at h1; linarith [rho0_bounds.2]
    · linarith

/-- The free arc: on the circle of radius `9/10`, the chart angles in
`(-1/4, 9/20)` if `cy ≤ c0`, and in `(0, 7/10)` otherwise, give free points. -/
private lemma free_interval (cy : ℝ) :
    ∃ l u, u - l = 7 / 10 ∧ ∀ t ∈ Ioo l u, 0 < 9 / 10 * Real.cos t ∧
      9 / 10 * Real.cos t ≤ 9 / 10 ∧ FreeRegime cy (9 / 10 * Real.sin t) := by
  have hpi := Real.pi_gt_three
  have hcos (t : ℝ) (ht : |t| < 1) : 0 < 9 / 10 * Real.cos t := by
    have := Real.cos_pos_of_mem_Ioo (x := t) ⟨by linarith [(abs_lt.mp ht).1],
      by linarith [(abs_lt.mp ht).2]⟩
    positivity
  rcases le_or_gt cy c0 with hcy | hcy
  · refine ⟨-1 / 4, 9 / 20, by norm_num, fun t ht => ⟨hcos t (abs_lt.mpr ⟨by linarith [ht.1],
      by linarith [ht.2]⟩), by nlinarith [Real.cos_le_one t], Or.inl ⟨hcy, ?_, ?_⟩⟩⟩
    · rcases le_total t 0 with h | h
      · nlinarith [Real.le_sin h, ht.1]
      · nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [ht.2])]
    · have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (x := t) (y := 9 / 20)
        (by linarith [ht.1]) (by linarith) ht.2.le
      have hu := sin_upper_five (x := 9 / 20) (by norm_num)
      norm_num at hu
      linarith
  · refine ⟨0, 7 / 10, by norm_num, fun t ht => ⟨hcos t (abs_lt.mpr ⟨by linarith [ht.1],
      by linarith [ht.2]⟩), by nlinarith [Real.cos_le_one t], Or.inr ⟨hcy, ?_, ?_⟩⟩⟩
    · nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2])]
    · have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (x := t) (y := 7 / 10)
        (by linarith [ht.1]) (by linarith) ht.2.le
      have hu := sin_upper_five (x := 7 / 10) (by norm_num)
      norm_num at hu
      linarith

/-- An arc in a set disjoint from `n` disjoint sets, each holding an arc of the
same circle: the half-widths add up to at most `π`. -/
lemma arc_budget_cons {n : ℕ} {o : Point} {r : ℝ} {V : Set Point} {U : Fin n → Set Point}
    (B : OpenArc o r V) (A : ∀ i, OpenArc o r (U i))
    (hV : ∀ i, Disjoint V (U i)) (hU : Pairwise fun i j => Disjoint (U i) (U j)) :
    B.halfWidth + ∑ i, (A i).halfWidth ≤ Real.pi := by
  have h := open_arc_budget (U := Fin.cons V U) (Fin.cons B A) (by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hV j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hV i).symm
      | succ j => exact hU (fun h => hij (congrArg Fin.succ h)))
  rw [Fin.sum_univ_succ] at h
  exact h

/-- If the square containing the origin is `Q(cx, cy)` with `c0 < cx < 1/2` and
`0 ≤ cy ≤ cx`, the five arcs of the other squares and the free arc east of it
exceed the circle of radius `9/10`. -/
private theorem east_center_impossible {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0, 0) R) (hQ : R ^ 2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx, cy)) p)
    (hx : c0 < cx) (hx1 : cx < 1 / 2) (hy0 : 0 ≤ cy) (hy : cy ≤ cx) : False := by
  have hx0 : 0 ≤ cx := (c0_pos.trans hx).le
  have hy1 : cy < 1 / 2 := hy.trans_lt hx1
  have hzero : openSquare (S 0) (0, 0) := by
    apply (hcentral (0, 0)).mpr
    simpa [axisSquare_open, openAxisSquare, abs_neg, abs_of_nonneg hx0, abs_of_nonneg hy0]
      using And.intro hx1 hy1
  have hne (i : Fin 5) : (0 : Fin 6) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hout (i : Fin 5) : ¬ openSquare (S i.succ) (0, 0) :=
    fun h => hp.disjoint _ _ (hne i).symm (0, 0) ⟨h, hzero⟩
  choose A hA using fun i : Fin 5 =>
    exterior_arc (S i.succ) (0, 0) ((hp.phi_le i.succ).trans hQ) (hout i)
  obtain ⟨l, u, hlen, hfree⟩ := free_interval cy
  have hmem : ∀ t ∈ Ioo l u, circlePoint (0, 0) (9 / 10) ((0 : Direction) + (t : Direction)) ∈
      {p | ∀ i : Fin 5, ¬ openSquare (S i.succ) p} := by
    intro t ht i hin
    obtain ⟨C, hsort⟩ := sorted_square_chart (S i.succ) (0, 0)
    have hs : (C.phase.toReal : Direction) = C.phase := Real.Angle.coe_toReal _
    have hcc := chart_signed_containment C hsort (hout i) ((hp.phi_le i.succ).trans hQ)
    obtain ⟨k, hk⟩ := central_separators_complete hcc.half_le hx0 hy0 hx1.le hy1.le
      (fun p hh => hp.disjoint 0 i.succ (hne i) p
        ⟨(hcentral p).mpr hh.1, (chart_same_open_oriented C hs p).mpr hh.2⟩)
    obtain ⟨hq1, hq1', hq⟩ := hfree t ht
    apply free_point_outside hcc hx hx1 hy0 hy hq1 hq1' hq hk
    rw [← chart_same_open_oriented C hs]
    simpa [circlePoint] using hin
  let B := arcOfInterval (0, 0) (9 / 10) _ 0 l u (by linarith) (by linarith [Real.pi_gt_three])
    hmem
  have hbudget := arc_budget_cons B A (fun i => Set.disjoint_left.mpr fun p hp' hq' => hp' i hq')
    (fun i j hij => Set.disjoint_left.mpr fun p hi hj =>
      hp.disjoint i.succ j.succ ((Fin.succ_injective _).ne hij) p ⟨hi, hj⟩)
  have hB : B.halfWidth = 7 / 20 := by
    simp only [B, arcOfInterval]
    linarith
  have hsum : ∑ _i : Fin 5, (14 / 25 : ℝ) < ∑ i, (A i).halfWidth :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hA i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith [Real.pi_lt_d2]

/-- If the square containing the origin is axis-parallel, with centre in
`[0, 1/2)²`, then its centre lies in `[0, c0]²`. -/
theorem central_box {S : Fin 6 → UnitSquare} {R cx cy : ℝ}
    (hp : Packing S (0, 0) R) (hQ : R ^ 2 ≤ Q0)
    (hcentral : ∀ p, openSquare (S 0) p ↔ openSquare (axisSquare (cx, cy)) p)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx1 : cx < 1 / 2) (hy1 : cy < 1 / 2) :
    cx ≤ c0 ∧ cy ≤ c0 := by
  by_contra! hbad
  rcases le_total cy cx with horder | horder
  · have hx : c0 < cx := by
      by_contra! h
      linarith [hbad h]
    exact east_center_impossible hp hQ hcentral hx hx1 hy0 horder
  · have hy : c0 < cy := by
      by_contra! h
      linarith [hbad (by linarith)]
    exact east_center_impossible (Six.packing_reflectDiagonal hp) hQ
      (Six.reflected_central_axis hcentral) hy hy1 hx0 horder

end Normalization
end SquaresInCircles.Six
