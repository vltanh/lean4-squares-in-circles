import SquaresInCircles.Common.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Angular budget on the genuine circle

We use Haar measure on `Real.Angle = AddCircle (2*pi)`.  Its total mass is
`2*pi`; a closed metric ball of radius `w ≤ pi` has mass `2*w`.

Witnesses below consist of actual arcs in planar regions.  Angular shadows
are not used.  Open arcs are handled by shrinking every half-width by the
same factor and using `bound_from_shrinks`; thus no assertion about polygon
boundary measures is needed.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace SquaresInCircles

local instance : Fact (0 < (2*Real.pi : ℝ)) := ⟨by positivity⟩

def circlePoint (o : Point) (r : ℝ) (θ : Direction) : Point :=
  (o.1+r*θ.cos, o.2+r*θ.sin)

lemma direction_norm (θ : Direction) : ‖θ‖ = |θ.toReal| := by
  conv_lhs => rw [← Real.Angle.coe_toReal θ]
  apply (AddCircle.norm_coe_eq_abs_iff (2*Real.pi) (by positivity)).2
  simpa only [abs_of_pos (show 0 < 2*Real.pi by positivity), mul_div_cancel_left₀ _
    (show (2:ℝ) ≠ 0 by norm_num)] using θ.abs_toReal_le_pi

lemma direction_dist (θ φ : Direction) : dist θ φ = |(θ-φ).toReal| := by
  rw [dist_eq_norm,direction_norm]

lemma direction_offset (θ φ : Direction) : θ = φ+((θ-φ).toReal : Direction) := by
  rw [Real.Angle.coe_toReal]
  abel

/-- A certified open angular interval contained in an actual planar region. -/
structure OpenArc (o : Point) (r : ℝ) (U : Set Point) where
  center : Direction
  halfWidth : ℝ
  positive : 0 < halfWidth
  atMostPi : halfWidth ≤ Real.pi
  inside : ∀ θ, dist θ center < halfWidth → circlePoint o r θ ∈ U

/-- The measure-theoretic core, independent of squares and their orientations.
It is stated on `AddCircle (2*pi)`, which carries the Haar measure; `Direction`
is definitionally the same circle with the same metric. -/
theorem closed_arc_budget {n : ℕ} (c : Fin n → AddCircle (2*Real.pi)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Real.pi)
    (hd : Pairwise (fun i j => Disjoint
      (Metric.closedBall (c i) (w i)) (Metric.closedBall (c j) (w j)))) :
    ∑ i, w i ≤ Real.pi := by
  have hmu := sum_measure_le_measure_univ (μ := (volume : Measure (AddCircle (2*Real.pi))))
    (s := Finset.univ) (fun i _ => measurableSet_closedBall.nullMeasurableSet)
    (fun i _ j _ hij => (hd hij).aedisjoint)
  have hvol (i : Fin n) : volume (Metric.closedBall (c i) (w i))=ENNReal.ofReal (2*w i) := by
    rw [AddCircle.volume_closedBall,min_eq_right (by linarith [(hw i).2])]
  simp only [hvol,AddCircle.measure_univ] at hmu
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by linarith [(hw i).1]),
    ENNReal.ofReal_le_ofReal_iff (by positivity),← Finset.mul_sum] at hmu
  linarith

/-- The same budget for open arc witnesses, without boundary-measure assumptions:
shrink every arc by the same factor `t < 1` and close it. -/
theorem open_arc_budget {n : ℕ} {o : Point} {r : ℝ} {U : Fin n → Set Point}
    (A : ∀ i, OpenArc o r (U i)) (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∑ i, (A i).halfWidth ≤ Real.pi := by
  refine bound_from_shrinks fun t ht0 ht1 => ?_
  have hw (i : Fin n) : t*(A i).halfWidth < (A i).halfWidth :=
    mul_lt_of_lt_one_left (A i).positive ht1
  rw [Finset.mul_sum]
  exact closed_arc_budget (fun i => (A i).center) _
    (fun i => ⟨mul_nonneg ht0 (A i).positive.le,(hw i).le.trans (A i).atMostPi⟩)
    fun i j hij => Set.disjoint_left.mpr fun θ hi hj => Set.disjoint_left.mp (hd hij)
      ((A i).inside θ (lt_of_le_of_lt hi (hw i))) ((A j).inside θ (lt_of_le_of_lt hj (hw j)))

/-- Arcs of half-width at least `π/n` on one circle, one of them more, cannot
belong to `n` disjoint sets. -/
theorem uniform_arc_excess {n : ℕ} {o : Point} {r : ℝ}
    {U : Fin n → Set Point} (A : ∀ i, OpenArc o r (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hle : ∀ i, Real.pi/n ≤ (A i).halfWidth)
    (hlt : ∃ i, Real.pi/n < (A i).halfWidth) : False := by
  obtain ⟨i,hi⟩ := hlt
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hle j) ⟨i,Finset.mem_univ _,hi⟩
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_div_cancel₀ _ hn] at hsum
  exact (open_arc_budget A hd).not_gt hsum

/-- Convert a real parameter interval to an arc on the quotient circle.
The hypotheses contain *strict* planar membership throughout the interval. -/
def arcOfInterval (o : Point) (r : ℝ) (U : Set Point) (phase : Direction)
    (l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u, circlePoint o r (phase+(t:Direction)) ∈ U) :
    OpenArc o r U where
  center := phase+(((l+u)/2 : ℝ) : Direction)
  halfWidth := (u-l)/2
  positive := by linarith
  atMostPi := by linarith
  inside := by
    intro θ hθ
    let s : ℝ := (θ-(phase+(((l+u)/2 : ℝ) : Direction))).toReal
    have hs : |s| < (u-l)/2 := by simpa only [direction_dist] using hθ
    have ht : (l+u)/2+s ∈ Ioo l u := by
      rcases abs_lt.mp hs with ⟨hs₀,hs₁⟩
      exact ⟨by linarith,by linarith⟩
    have he : θ=phase+(((l+u)/2+s : ℝ) : Direction) := by
      rw [Real.Angle.coe_add]
      have hh := direction_offset θ (phase+(((l+u)/2 : ℝ) : Direction))
      simpa only [add_assoc] using hh
    rw [he]
    exact hmem _ ht

end SquaresInCircles
