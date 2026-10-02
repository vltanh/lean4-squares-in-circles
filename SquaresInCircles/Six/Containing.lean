module

public import SquaresInCircles.Six.Exterior
public import SquaresInCircles.Six.Normalization.Basic
public import SquaresInCircles.Common.Sweep
public import SquaresInCircles.Common.Frames

/-!
# Six squares: the containing square

Six arcs of half-width more than `π/6` on the circle of radius `9/10` do not
fit, so in a disk of squared radius at most `Q0` exactly one square C contains
the disk centre (`exists_unique_containing`), and the packing is read in a frame
of C (`normalize_frame_of_ceiling`). In that frame the centre `(cx, cy)` of C
lies in `[0, 1/2)²`, and `cy ≤ cx` after a diagonal reflection; suppose
`cx > c0`. Every other square lies beyond a side of C or beyond a support line
of C along one of its own axes, and such a support line is at distance at most
`ρ0 - 1/2` from the origin. The lines at that distance miss an arc of length
`7/10` east of C (`shallow_support`): the chart angles `(-1/4, 9/20)` if
`cy ≤ c0` and `(0, 7/10)` otherwise. With the five arcs of the other squares
this exceeds the circle, so the centre of C lies in `[0, c0]²` (`central_box`).
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles.Six
open Normalization

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
    (hp : Packing S o R) (hR : R ^ 2 ≤ Q0) : Nonempty (NormalizedFrame S o R) := by
  obtain ⟨k, hk, _⟩ := Six.exists_unique_containing hp hR
  exact normalize_with_containing hp hk

/-! ### The central box -/

section Shallow
variable {L X Y q1 q2 x w : ℝ}

/-- With `X > L`, a unit vector `(x, w)` of the first quadrant with
`X x + w/2 ≤ L` has `x ≤ 21/100`: a support line at the north-east corner within
`L ≈ 0.613` of the origin is nearly horizontal. -/
private lemma first_quadrant_steep (hL : 1 / 2 < L) (hL' : L < 0.6129)
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
private lemma fourth_quadrant_steep (hL : 1 / 2 < L) (hL' : L < 0.6129)
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
      nlinarith [mul_nonneg hx (show 0 ≤ cx + 1 / 2 - q1 + 3 / 10 by linarith),
        mul_nonneg hw (show 0 ≤ q2 + 1 / 2 - cy - 3 / 20 by linarith)]
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
    have hcc := C.exteriorChart_signed hsort (hout i) ((hp.phi_le i.succ).trans hQ)
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
    exact east_center_impossible (packing_reflectDiagonal hp) hQ
      (reflected_central_axis hcentral) hy hy1 hx0 horder

end Normalization

end SquaresInCircles.Six
