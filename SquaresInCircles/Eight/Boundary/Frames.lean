module

public import SquaresInCircles.Eight.Boundary.Model
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: the four-type budget and the real frames

The vertices of a boundary cycle have four types, the core `C` and the three outer tangent
ranges, low `L`, middle `M` and high `H` (`Arithmetic/FourTypePairs.lean`), and an edge from a
vertex of type `s` to one of type `t` costs more than `γ(s, t)`, the entry of
`handGammaNumerator` over `10⁴`. Every closed walk of seven steps on the four types weighs at
least `62096/10⁴ = 3881/625` (`four_type_seven_walk`): an odd cycle has a
monochromatic edge, and two crossings into and out of the middle type supply
the remaining reserve. The triangle inequality bounds this cyclic variation.
With the frame charge `(9/50) hᵢ` on each edge
and markers that telescope, the gaps, which add up to `2π`, leave `∑ hᵢ < 10394/25425`
(`four_type_cycle_budget`, `physical_cycle_width_bound`).

The charge of a relative frame angle `x` is `periodicFrameCost x = (|cos x| + |sin x| - 1)/2`,
invariant under quarter turns; on `[0, π/4]` it is `frameCost x = (cos x + sin x - 1)/2`, which
is increasing, concave and subadditive (`frameCost_monotone`, `frameCost_concave`,
`frameCost_triangle`). If the charges of the steps of seven angles `φᵢ` round the cycle add up to
less than `10394/25425`, which is below `2 frameCost (7/10)`, the representatives of the steps in
`[-π/4, π/4]` (`shortestQuarter`) have no winding, and they lift the angles to real
representatives with integer quarter offsets in an interval shorter than `7/10`
(`physical_frame_lift_of_cost`, `PhysicalFrameLift`): twice the frame cost of the range of the
lift is at most the total charge (`frameCost_closed_range`). `Boundary/Actions.lean` turns this lift
into a quarter lift of the cycle (`quarterLift_of_cost`).

The file starts with sums round the cycle (`sum_next`, `angleGap_sum`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

lemma next_prev (i : Vertex) : next (prev i) = i := by
  simp [next, prev]

lemma prev_next (i : Vertex) : prev (next i) = i := by
  simp [next, prev]

def nextPerm : Equiv.Perm Vertex where
  toFun := next
  invFun := prev
  left_inv := prev_next
  right_inv := next_prev

/-- A sum over the vertices does not change when every vertex is replaced by the next. -/
lemma sum_next {α : Type*} [AddCommMonoid α] (f : Vertex → α) :
    ∑ i, f (next i) = ∑ i, f i := by
  exact Equiv.sum_comp nextPerm f

lemma cyclic_difference_sum (f : Vertex → ℝ) : ∑ i, (f (next i) - f i) = 0 := by
  rw [Finset.sum_sub_distrib, sum_next, sub_self]

/-- The seven gaps `angleGap β i` add up to `2π`, whatever the directions `β`. -/
lemma angleGap_sum (β : Vertex → ℝ) : ∑ i, angleGap β i = 2 * Real.pi := by
  simp [angleGap, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_next]

/-- Markers telescope round the cycle. -/
lemma cyclic_markers_cancel (δ w ψ : Vertex → ℝ) (b : ℝ) :
    ∑ i, (δ i - b * w i + ψ (next i) - ψ i) =
      (∑ i, δ i) - b * ∑ i, w i := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_next]
  ring

/-- Split the closed walk into the two paths joining `i` to `j`. Each path
has total variation at least `|θ j-θ i|`, by telescoping and the triangle inequality. -/
lemma closed_walk_range_bound (θ : Vertex → ℝ) (i j : Vertex) :
    2*|θ j-θ i| ≤ ∑ k, |θ (next k)-θ k| := by
  let f : ℕ → ℝ := fun k => θ (Fin.ofNat 7 k)
  let δ : ℕ → ℝ := fun k => f (k+1)-f k
  have hzero : ∑ k ∈ Finset.range 7, δ k=0 := by
    dsimp [δ]
    rw [Finset.sum_range_sub]
    norm_num [f,Fin.ofNat]
  have htotal : ∑ k ∈ Finset.range 7, |δ k| = ∑ k, |θ (next k)-θ k| := by
    norm_num [Finset.sum_range_succ,Fin.sum_univ_seven,δ,f,Fin.ofNat,next]
  have hpath (a b : Vertex) (hab : a ≤ b) :
      2*|θ b-θ a| ≤ ∑ k ∈ Finset.range 7, |δ k| := by
    let s := Finset.Ico a.val b.val
    have hsub : s ⊆ Finset.range 7 := by
      intro k hk
      have h := (Finset.mem_Ico.mp hk).2
      exact Finset.mem_range.mpr (h.trans b.isLt)
    have htel : ∑ k ∈ s, δ k=θ b-θ a := by
      dsimp [s,δ]
      rw [Finset.sum_Ico_sub f (show a.val ≤ b.val from hab)]
      simp [f]
    have hpart := Finset.sum_sdiff hsub (f := δ)
    have habs := Finset.sum_sdiff hsub (f := fun k => |δ k|)
    have h₁ := Finset.abs_sum_le_sum_abs δ s
    have h₂ := Finset.abs_sum_le_sum_abs δ (Finset.range 7 \ s)
    rw [hzero,htel] at hpart
    have he : ∑ k ∈ Finset.range 7 \ s, δ k=-(θ b-θ a) := by linarith
    rw [htel] at h₁
    rw [he,abs_neg] at h₂
    linarith
  rcases le_total i j with hij | hji
  · exact (hpath i j hij).trans_eq htotal
  · rw [abs_sub_comm]
    exact (hpath j i hji).trans_eq htotal

/-- The lower bounds `γ(s, t)` of the cost of an edge from a vertex of type `s` to one of type
`t`, times `10⁴`, for the types `C, L, M, H` in this order. -/
def handGammaNumerator : Fin 4 → Fin 4 → ℕ :=
  ![![9200, 9100, 9005, 8833],
    ![9100, 9100, 9005, 8833],
    ![9005, 9005, 8912, 8926],
    ![8833, 8833, 8926, 9099]]

/-- The bound `γ(s, t) = handGammaNumerator s t / 10⁴`. -/
def handGamma (i j : Fin 4) : ℝ := handGammaNumerator i j / 10000

/-- Indicator of the middle type. -/
private def middleIndicator (a : Fin 4) : ℝ := if a=2 then 1 else 0
/-- Color the high type one way and all the other types the other way. -/
private def highColor (a : Fin 4) : Bool := decide (a=3)
private def gammaResidual (a b : Fin 4) : ℝ := (handGammaNumerator a b : ℝ)-8833
private def middleBoundary (a b : Fin 4) : ℝ := |middleIndicator b-middleIndicator a|

/-- An odd cycle cannot alternate between two colors at every step. -/
private lemma odd_cycle_same_color (f : Vertex → Bool) : ∃ i, f i=f (next i) := by
  by_contra! hn
  have h (i : Vertex) : f (next i)=!f i := Bool.eq_not_of_ne (hn i).symm
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num [next] at h0 h1 h2 h3 h4 h5 h6
  rw [h5,h4,h3,h2,h1,h0] at h6
  exact (Bool.not_eq_self (f 0)).mp (by simpa only [Bool.not_not] using h6.symm)

/-- Crossing into or out of the middle type costs at least 93 residual units. -/
private lemma gamma_residual_boundary (a b : Fin 4) :
    93*middleBoundary a b ≤ gammaResidual a b := by
  fin_cases a <;> fin_cases b <;> norm_num [gammaResidual,middleBoundary,middleIndicator,handGammaNumerator]

/-- A monochromatic edge has another 79 units after paying for a boundary crossing. -/
private lemma same_color_surplus (a b : Fin 4) (h : highColor a=highColor b) :
    79 ≤ gammaResidual a b-93*middleBoundary a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [highColor,gammaResidual,middleBoundary,middleIndicator,handGammaNumerator] at *

/-- With no middle endpoint, a monochromatic edge alone pays the whole reserve. -/
private lemma same_color_reserve (a b : Fin 4) (ha : a≠2) (hb : b≠2)
    (h : highColor a=highColor b) : 265 ≤ gammaResidual a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [highColor,gammaResidual,handGammaNumerator] at *

private lemma gamma_residual_nonneg (a b : Fin 4) : 0 ≤ gammaResidual a b :=
  (mul_nonneg (by norm_num : (0:ℝ) ≤ 93) (abs_nonneg _)).trans (gamma_residual_boundary a b)

private lemma gamma_residual_cycle (τ : Vertex → Fin 4) :
    265 ≤ ∑ i, gammaResidual (τ i) (τ (next i)) := by
  obtain ⟨k,hk⟩ := odd_cycle_same_color (fun i => highColor (τ i))
  by_cases hnone : ∀ i, τ i≠2
  · exact (same_color_reserve _ _ (hnone k) (hnone (next k)) hk).trans
      (Finset.single_le_sum (fun i _ => gamma_residual_nonneg (τ i) (τ (next i))) (Finset.mem_univ k))
  push Not at hnone
  obtain ⟨i,hi⟩ := hnone
  by_cases hall : ∀ j, τ j=2
  · simp only [hall]
    norm_num [gammaResidual,handGammaNumerator]
  push Not at hall
  obtain ⟨j,hj⟩ := hall
  have hv : 2 ≤ ∑ a, middleBoundary (τ a) (τ (next a)) := by
    simpa [middleBoundary,middleIndicator,hi,hj] using
      closed_walk_range_bound (fun a => middleIndicator (τ a)) i j
  have hsurplus : 79 ≤ ∑ a,
      (gammaResidual (τ a) (τ (next a))-93*middleBoundary (τ a) (τ (next a))) :=
    (same_color_surplus _ _ hk).trans
      (Finset.single_le_sum (fun a _ => sub_nonneg.mpr (gamma_residual_boundary (τ a) (τ (next a))))
        (Finset.mem_univ k))
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hsurplus
  linarith

/-- Subtract 8833 from each edge weight. An odd cycle has a monochromatic edge.
If the middle type occurs together with another type, the cycle crosses its
boundary at least twice; those crossings and the monochromatic surplus pay 265.
The two constant-membership cases follow directly from the matrix. -/
theorem four_type_seven_walk_numerator :
    ∀ τ : Vertex → Fin 4, 62096 ≤ ∑ i, handGammaNumerator (τ i) (τ (next i)) := by
  intro τ
  have h := gamma_residual_cycle τ
  simp only [gammaResidual,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  norm_num at h
  have hr : (62096:ℝ) ≤ ∑ i, (handGammaNumerator (τ i) (τ (next i)) : ℝ) := by linarith
  exact_mod_cast hr

/-- Every closed walk of seven steps on the four types costs at least `3881/625`. -/
theorem four_type_seven_walk (τ : Vertex → Fin 4) :
    3881 / 625 ≤ ∑ i, handGamma (τ i) (τ (next i)) := by
  have hn := four_type_seven_walk_numerator τ
  have hr : (62096 : ℝ) ≤ ∑ i, (handGammaNumerator (τ i) (τ (next i)) : ℝ) := by
    exact_mod_cast hn
  simp only [handGamma, ← Finset.sum_div]
  nlinarith

/-- If each edge has `γ(τᵢ, τᵢ₊₁) < δᵢ - (9/50) hᵢ + ψᵢ₊₁ - ψᵢ`, with one marker `ψᵢ` at each
vertex used on both of its edges, then `3881/625 < ∑ δᵢ - (9/50) ∑ hᵢ`. -/
theorem four_type_cycle_budget (τ : Vertex → Fin 4) (δ h ψ : Vertex → ℝ)
    (hpair : ∀ i,
      handGamma (τ i) (τ (next i)) <
        δ i - (9 / 50 : ℝ) * h i + ψ (next i) - ψ i) :
    3881 / 625 < (∑ i, δ i) - (9 / 50 : ℝ) * ∑ i, h i := by
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => (hpair i).le) ⟨0, Finset.mem_univ _, hpair 0⟩
  rw [cyclic_markers_cancel] at hsum
  exact (four_type_seven_walk τ).trans_lt hsum

/-- With the gaps of the centre directions for `δ`, which add up to `2π < 710/113`, the charges add
up to less than `10394/25425`. -/
theorem physical_cycle_width_bound (τ : Vertex → Fin 4) (β h ψ : Vertex → ℝ)
    (hpair : ∀ i,
      handGamma (τ i) (τ (next i)) <
        angleGap β i - (9 / 50 : ℝ) * h i + ψ (next i) - ψ i)
    (hpi : Real.pi < 355 / 113) :
    ∑ i, h i < 10394 / 25425 := by
  have hh := four_type_cycle_budget τ (angleGap β) h ψ hpair
  rw [angleGap_sum] at hh
  linarith

/-- Half the excess over `1` of the width `cos x + sin x` of a unit square turned by `x`; on
`[0, π/4]` it is `periodicFrameCost x` (`periodicFrameCost_of_short_nonneg`). -/
def frameCost (x : ℝ) : ℝ := (Real.cos x + Real.sin x - 1) / 2

/-- The frame charge `(|cos x| + |sin x| - 1)/2` of a relative frame angle `x`, invariant under
quarter turns (`periodicFrameCost_int_quarter`). -/
def periodicFrameCost (x : ℝ) : ℝ :=
  (|Real.cos x| + |Real.sin x| - 1) / 2

lemma frameCost_zero : frameCost 0 = 0 := by norm_num [frameCost]

lemma periodicFrameCost_pi_half (x : ℝ) :
    periodicFrameCost (x + Real.pi / 2) = periodicFrameCost x := by
  simp [periodicFrameCost, Real.cos_add, Real.sin_add, abs_neg, add_comm]

lemma periodicFrameCost_neg (x : ℝ) : periodicFrameCost (-x) = periodicFrameCost x := by
  simp [periodicFrameCost, Real.cos_neg, Real.sin_neg, abs_neg]

lemma frameCost_hasDerivAt (x : ℝ) :
    HasDerivAt frameCost ((Real.cos x - Real.sin x) / 2) x := by
  convert ((((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).sub_const 1).div_const 2)
    using 1
  · rfl
  · ring

lemma frameCost_monotone : MonotoneOn frameCost (Set.Icc 0 (Real.pi / 4)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun x => (Real.cos x - Real.sin x) / 2)
  · unfold frameCost
    fun_prop
  · intro x hx
    exact (frameCost_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : 0 ≤ x ∧ x ≤ Real.pi / 4 := ⟨hx.1.le, hx.2.le⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 4 - x by linarith) (by linarith [Real.pi_pos])
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hs
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith

/-! ## The real lift of the frames -/

lemma frameCost_concave : ConcaveOn ℝ (Set.Icc 0 (Real.pi / 4)) frameCost := by
  apply concave_of_deriv2 (fun x _ => frameCost_hasDerivAt x)
    (f' := fun x => (Real.cos x - Real.sin x) / 2)
    (f'' := fun x => -(Real.sin x + Real.cos x) / 2)
  · intro x hx
    convert (((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).div_const 2) using 1
    ring
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
      (by linarith [hx.2,Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    linarith

lemma frameCost_nonneg {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi/4)) :
    0 ≤ frameCost x := by
  simpa only [frameCost_zero] using
    frameCost_monotone ⟨le_rfl,by positivity⟩ hx hx.1

lemma frameCost_at_quarter : frameCost (Real.pi/4) = (Real.sqrt 2-1)/2 := by
  rw [frameCost,Real.cos_pi_div_four,Real.sin_pi_div_four]
  ring

lemma frameCost_at_quarter_pos : 0 < frameCost (Real.pi/4) := by
  rw [frameCost_at_quarter]
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  nlinarith

/-- On `[0, π/4]` the frame cost lies above its chords from `0`: `(a/b) frameCost b ≤ frameCost a`
for `0 ≤ a ≤ b ≤ π/4`. -/
lemma frameCost_chord {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hbH : b ≤ Real.pi/4) :
    a / b * frameCost b ≤ frameCost a := by
  have ht : 0 ≤ a/b := div_nonneg ha hb.le
  have ht1 : a/b ≤ 1 := (div_le_one₀ hb).2 hab
  have h := frameCost_concave.2
    (show (0:ℝ) ∈ Set.Icc 0 (Real.pi/4) by constructor <;> positivity)
    (show b ∈ Set.Icc 0 (Real.pi/4) from ⟨hb.le,hbH⟩)
    (sub_nonneg.2 ht1) ht (by ring : (1-a/b)+a/b=1)
  have hid : (a/b)*b=a := div_mul_cancel₀ a hb.ne'
  simpa only [smul_eq_mul,hid,frameCost_zero,mul_zero,zero_add] using h

/-- The frame cost is subadditive on `[0, π/4]`: `frameCost c ≤ frameCost a + frameCost b` when
`c ≤ a + b`. -/
lemma frameCost_triangle {a b c : ℝ}
    (ha : a ∈ Set.Icc 0 (Real.pi/4))
    (hb : b ∈ Set.Icc 0 (Real.pi/4))
    (hc : c ∈ Set.Icc 0 (Real.pi/4)) (htri : c ≤ a+b) :
    frameCost c ≤ frameCost a+frameCost b := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith [ha.1,hb.1]
    have hb0 : b=0 := by linarith [ha.1,hb.1]
    have hc0 : c=0 := by linarith [hc.1,htri]
    simp [ha0,hb0,hc0,frameCost_zero]
  have hsp : 0 < a+b := lt_of_le_of_ne (add_nonneg ha.1 hb.1) (Ne.symm hs)
  by_cases hsH : a+b ≤ Real.pi/4
  · have h₁ := frameCost_chord ha.1 (by linarith [hb.1]) hsp hsH
    have h₂ := frameCost_chord hb.1 (by linarith [ha.1]) hsp hsH
    have hid : a/(a+b)*frameCost (a+b)+b/(a+b)*frameCost (a+b)=frameCost (a+b) := by
      field_simp
    have hmono := frameCost_monotone hc ⟨hsp.le,hsH⟩ htri
    linarith
  · have hH : 0 < Real.pi/4 := by positivity
    have h₁ := frameCost_chord ha.1 ha.2 hH le_rfl
    have h₂ := frameCost_chord hb.1 hb.2 hH le_rfl
    have hmono := frameCost_monotone hc ⟨hH.le,le_rfl⟩ hc.2
    have he : (a/(Real.pi/4)+b/(Real.pi/4))*frameCost (Real.pi/4) =
        a/(Real.pi/4)*frameCost (Real.pi/4)+b/(Real.pi/4)*frameCost (Real.pi/4) := by ring
    have hratio : 1 ≤ a/(Real.pi/4)+b/(Real.pi/4) := by
      rw [← add_div]
      exact (one_le_div hH).2 (le_of_not_ge hsH)
    have hh := mul_le_mul_of_nonneg_right hratio frameCost_at_quarter_pos.le
    linarith

lemma frameCost_seven_tenths :
    10394/25425 < 2*frameCost (7/10) := by
  have hc := cos_lower_six (x := (7/10:ℝ)) (by norm_num)
  have hs := sin_lower_seven (x := (7/10:ℝ)) (by norm_num)
  norm_num at hc hs
  dsimp [frameCost]
  linarith

lemma periodicFrameCost_of_short_nonneg {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi/4)) : periodicFrameCost x=frameCost x := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
  simp [periodicFrameCost,frameCost,abs_of_nonneg hs,abs_of_nonneg hc]

lemma periodicFrameCost_of_short {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    periodicFrameCost x=frameCost |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    exact periodicFrameCost_of_short_nonneg ⟨h,by simpa [abs_of_nonneg h] using hx⟩
  · rw [abs_of_nonpos h,← periodicFrameCost_neg x]
    exact periodicFrameCost_of_short_nonneg ⟨neg_nonneg.2 h,by simpa [abs_of_nonpos h] using hx⟩

lemma periodicFrameCost_int_quarter (x : ℝ) (n : ℤ) :
    periodicFrameCost (x+(n:ℝ)*(Real.pi/2))=periodicFrameCost x := by
  have hnat (k : ℕ) : ∀ x : ℝ,
      periodicFrameCost (x+(k:ℝ)*(Real.pi/2))=periodicFrameCost x := by
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        calc
          periodicFrameCost (x+(k+1:ℕ)*(Real.pi/2)) =
              periodicFrameCost ((x+(k:ℝ)*(Real.pi/2))+Real.pi/2) := by congr 1; push_cast; ring
          _ = periodicFrameCost (x+(k:ℝ)*(Real.pi/2)) := periodicFrameCost_pi_half _
          _ = periodicFrameCost x := ih x
  cases n with
  | ofNat k => simpa using hnat k x
  | negSucc k =>
      have h := hnat (k+1) (x-((k+1:ℕ):ℝ)*(Real.pi/2))
      have hid : x-((k+1:ℕ):ℝ)*(Real.pi/2)+((k+1:ℕ):ℝ)*(Real.pi/2)=x := by ring
      rw [hid] at h
      simpa only [Int.cast_negSucc,sub_eq_add_neg,neg_mul] using h.symm

/-- The integer nearest to `x / (π/2)`, halves rounded up. -/
def nearestQuarter (x : ℝ) : ℤ := ⌊x/(Real.pi/2)+1/2⌋

/-- The representative `x - n π/2` of `x` modulo quarter turns in `[-π/4, π/4]`
(`shortestQuarter_range`). -/
def shortestQuarter (x : ℝ) : ℝ := x-(nearestQuarter x:ℝ)*(Real.pi/2)

lemma shortestQuarter_range (x : ℝ) : |shortestQuarter x| ≤ Real.pi/4 := by
  have hT : 0 < Real.pi/2 := by positivity
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x/(Real.pi/2)+1/2)) hT.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/(Real.pi/2)+1/2)) hT
  have hid : (x/(Real.pi/2)+1/2)*(Real.pi/2)=x+Real.pi/4 := by field_simp; ring
  rw [hid] at hlo hhi
  apply abs_le.2
  dsimp [shortestQuarter,nearestQuarter]
  constructor <;> linarith

lemma shortestQuarter_cost (x : ℝ) :
    frameCost |shortestQuarter x|=periodicFrameCost x := by
  rw [← periodicFrameCost_of_short (shortestQuarter_range x)]
  have h := periodicFrameCost_int_quarter (shortestQuarter x) (nearestQuarter x)
  have hid : shortestQuarter x+(nearestQuarter x:ℝ)*(Real.pi/2)=x := by
    dsimp [shortestQuarter]
    ring
  rw [hid] at h
  exact h.symm

/-- Real representatives `theta` of the angles `φ` modulo quarter turns, with integer quarter
offsets, in an interval of length less than `7/10`. -/
structure PhysicalFrameLift (φ : Vertex → ℝ) where
  theta : Vertex → ℝ
  quarter : Vertex → ℤ
  left : ℝ
  diameter : ℝ
  small : diameter < 7/10
  theta_range : ∀ i, left ≤ theta i ∧ theta i ≤ left+diameter
  represents : ∀ i, φ i=theta i+(quarter i:ℝ)*(Real.pi/2)

/-- The sum of `m j` over the vertices `j` before `i`. -/
def quarterPrefix (m : Vertex → ℤ) (i : Vertex) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Vertex => j.val< i.val),m j

lemma quarterPrefix_difference (m : Vertex → ℤ) (hm : ∑ i,m i=0) (i : Vertex) :
    quarterPrefix m (next i)-quarterPrefix m i=m i := by
  rw [Fin.sum_univ_seven] at hm
  simp only [quarterPrefix,Finset.sum_filter,Fin.sum_univ_seven]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [next]
  omega

/-- If `θ` is least at `l` and greatest at `u`, within `π/4`, then twice the frame cost of its range
is at most the sum of the frame costs of its steps round the cycle. -/
lemma frameCost_closed_range (θ : Vertex → ℝ) {l u : Vertex}
    (hl : ∀ i,θ l ≤ θ i) (hu : ∀ i,θ i ≤ θ u)
    (hD : θ u-θ l ≤ Real.pi/4) :
    2*frameCost (θ u-θ l) ≤ ∑ i,frameCost |θ (next i)-θ i| := by
  have hrange (i j : Vertex) : |θ j-θ i| ∈ Set.Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,(abs_le.2 ⟨?_,?_⟩).trans hD⟩ <;>
      linarith [hl i,hl j,hu i,hu j]
  let r : Vertex → ℝ := fun i => frameCost |θ i-θ l|
  have hstep (i : Vertex) : |r (next i)-r i| ≤ frameCost |θ (next i)-θ i| := by
    have h₁ := frameCost_triangle (hrange l i) (hrange i (next i)) (hrange l (next i))
      (by linarith [abs_sub_le (θ (next i)) (θ i) (θ l)])
    have h₂ := frameCost_triangle (hrange l (next i)) (hrange (next i) i) (hrange l i)
      (by linarith [abs_sub_le (θ i) (θ (next i)) (θ l)])
    rw [abs_sub_comm (θ i) (θ (next i))] at h₂
    apply abs_le.2
    dsimp [r]
    constructor <;> linarith
  have hh := closed_walk_range_bound r l u
  have hr₀ : r l=0 := by simp [r,frameCost_zero]
  have hr₁ : r u=frameCost (θ u-θ l) := by
    simp [r,abs_of_nonneg (sub_nonneg.2 (hl u))]
  rw [hr₀,hr₁,sub_zero,abs_of_nonneg (frameCost_nonneg ⟨sub_nonneg.2 (hl u),hD⟩)] at hh
  exact hh.trans (Finset.sum_le_sum (fun i _ => hstep i))

/-- If the charges of the steps of `φ` round the cycle add up to less than `10394/25425`, then `φ`
has a real lift in an interval shorter than `7/10`. -/
theorem physical_frame_lift_of_cost (φ : Vertex → ℝ)
    (hcost : (∑ i,periodicFrameCost (φ (next i)-φ i)) < 10394/25425) :
    Nonempty (PhysicalFrameLift φ) := by
  let m : Vertex → ℤ := fun i => nearestQuarter (φ (next i)-φ i)
  let x : Vertex → ℝ := fun i => shortestQuarter (φ (next i)-φ i)
  let U : ℝ := ∑ i,frameCost |x i|
  let V : ℝ := ∑ i,|x i|
  have hU : U < 10394/25425 := by simpa [U,x,shortestQuarter_cost] using hcost
  have hH : 0 < Real.pi/4 := by positivity
  have hseven : (7/10:ℝ) ≤ Real.pi/4 := by linarith [Real.pi_gt_three]
  have hbig : U < 2*frameCost (Real.pi/4) :=
    hU.trans (frameCost_seven_tenths.trans_le
      (mul_le_mul_of_nonneg_left (frameCost_monotone ⟨by norm_num,hseven⟩ ⟨hH.le,le_rfl⟩ hseven)
        (by norm_num)))
  have hchord (i : Vertex) : |x i| * frameCost (Real.pi/4) ≤
      (Real.pi/4)*frameCost |x i| := by
    have h := frameCost_chord (abs_nonneg (x i))
      (shortestQuarter_range (φ (next i)-φ i)) hH le_rfl
    rw [div_mul_eq_mul_div,div_le_iff₀ hH] at h
    linarith
  have hsumchord := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hchord i)
  rw [← Finset.sum_mul,← Finset.mul_sum] at hsumchord
  have hV : V < Real.pi/2 := by
    change (∑ i,|x i|)*frameCost (Real.pi/4) ≤ (Real.pi/4)*U at hsumchord
    change ∑ i,|x i| < Real.pi/2
    nlinarith [frameCost_at_quarter_pos]
  have hxs : ∑ i,x i= -(∑ i,m i:ℤ)*(Real.pi/2) := by
    have h1 : ∑ i,x i=∑ i,(φ (next i)-φ i)-∑ i,((m i:ℝ)*(Real.pi/2)) := by
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [h1,cyclic_difference_sum,← Finset.sum_mul,Int.cast_sum]
    ring
  have habs : |∑ i,x i| < Real.pi/2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans_lt hV
  have hm : ∑ i,m i=0 := by
    by_contra hn
    have hsplit : (1:ℤ) ≤ ∑ i,m i ∨ ∑ i,m i ≤ -1 := by omega
    rw [hxs] at habs
    rcases hsplit with hp | hn
    · have hp' : (1:ℝ) ≤ (∑ i,m i:ℤ) := by exact_mod_cast hp
      have hnegative := neg_le_abs (-(∑ i,m i:ℤ)*(Real.pi/2))
      nlinarith [Real.pi_pos]
    · have hn' : (∑ i,m i:ℤ) ≤ (-1:ℝ) := by exact_mod_cast hn
      have hpositive := le_abs_self (-(∑ i,m i:ℤ)*(Real.pi/2))
      nlinarith [Real.pi_pos]
  let M : Vertex → ℤ := quarterPrefix m
  let θ : Vertex → ℝ := fun i => φ i-(M i:ℝ)*(Real.pi/2)
  have hθstep (i : Vertex) : θ (next i)-θ i=x i := by
    have hi : M (next i)-M i=m i := quarterPrefix_difference m hm i
    have hicast : (M (next i):ℝ)-(M i:ℝ)=(m i:ℝ) := by exact_mod_cast hi
    change (φ (next i)-(M (next i):ℝ)*(Real.pi/2))-(φ i-(M i:ℝ)*(Real.pi/2)) =
      φ (next i)-φ i-(m i:ℝ)*(Real.pi/2)
    linear_combination (-(Real.pi/2))*hicast
  obtain ⟨l,hlmem,hl⟩ := Finset.exists_min_image Finset.univ θ Finset.univ_nonempty
  obtain ⟨u,humem,hu⟩ := Finset.exists_max_image Finset.univ θ Finset.univ_nonempty
  have hl' (i : Vertex) : θ l ≤ θ i := hl i (Finset.mem_univ _)
  have hu' (i : Vertex) : θ i ≤ θ u := hu i (Finset.mem_univ _)
  have hd0 : 0 ≤ θ u-θ l := sub_nonneg.2 (hl' u)
  have hdH : θ u-θ l < Real.pi/4 := by
    have hh := closed_walk_range_bound θ l u
    simp only [hθstep,abs_of_nonneg hd0] at hh
    change ∑ i,|x i| < Real.pi/2 at hV
    linarith
  have hmetric := frameCost_closed_range θ hl' hu' hdH.le
  simp only [hθstep] at hmetric
  have hdsmall : θ u-θ l < 7/10 := by
    by_contra! hbad
    have hmono := frameCost_monotone ⟨by norm_num,hseven⟩ ⟨hd0,hdH.le⟩ hbad
    change ∑ i,frameCost |x i| < 10394/25425 at hU
    linarith [frameCost_seven_tenths]
  refine ⟨⟨θ,M,θ l,θ u-θ l,hdsmall,?_,?_⟩⟩
  · intro i
    exact ⟨hl' i,by linarith [hu' i]⟩
  · intro i
    change φ i=(φ i-(M i:ℝ)*(Real.pi/2))+(M i:ℝ)*(Real.pi/2)
    ring

end SquaresInCircles.Eight
