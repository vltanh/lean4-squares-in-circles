module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTiltedWeights
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveEnvelope

/-!
# Eight squares: balanced coefficient domains without assuming l is at least one

The fourth coefficient is the established
D minorant's H coefficient. All four larger coefficients are compared
against min(1,l), which may be strictly below one on the triangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Explicit
open Secondary PositiveTD PositiveAngularEnvelope

def pWeights (r : Region) (x y z : ℝ) : Fin 4→ℝ :=
  PositiveTD.pWeights (k r x y) (l r x y) (tilted r x y z)
def qWeights (r : Region) (x y z : ℝ) : Fin 4→ℝ :=
  PositiveTD.qWeights (k r x y) (l r x y) (tilted r x y z)

theorem pair_domain (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) (i : Fin 4) :
    0<pWeights r x y z i ∧ pWeights r x y z i≤qWeights r x y z i ∧
      2*qWeights r x y z i≤3*pWeights r x y z i := by
  have hb := base_bounds r hd
  have hm := tilted_ratio r hd hz
  have hm0 : 0<tilted r x y z := by nlinarith [hb.l_positive,hm.1]
  have hk0 : 0<k r x y := by linarith [hb.k_lower]
  fin_cases i
  · change 0<k r x y ∧ k r x y≤1 ∧ 2*(1:ℝ)≤3*k r x y
    exact ⟨hk0,by linarith [hb.k_upper],by linarith [hb.k_lower]⟩
  · change 0<k r x y ∧ k r x y≤l r x y ∧ 2*l r x y≤3*k r x y
    exact ⟨hk0,hb.k_le_l,by linarith [hb.l_le_three_halves_k]⟩
  · change 0< min (l r x y) (tilted r x y z) ∧
      min (l r x y) (tilted r x y z)≤ max (l r x y) (tilted r x y z) ∧
      2*max (l r x y) (tilted r x y z)≤3*min (l r x y) (tilted r x y z)
    rcases le_total (l r x y) (tilted r x y z) with hle|hle
    · rw [min_eq_left hle,max_eq_right hle]
      exact ⟨hb.l_positive,hle,by nlinarith [hm.2,hb.l_positive]⟩
    · rw [min_eq_right hle,max_eq_left hle]
      exact ⟨hm0,hle,by linarith [hm.1]⟩
  · change 0<k r x y ∧ k r x y≤1 ∧ 2*(1:ℝ)≤3*k r x y
    exact ⟨hk0,by linarith [hb.k_upper],by linarith [hb.k_lower]⟩

theorem pair_scale_bounds (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) (i : Fin 4) :
    min 1 (l r x y)≤qWeights r x y z i ∧
      qWeights r x y z i≤(6/5)*min 1 (l r x y) := by
  have hl := l_lower r hd
  have hlu := l_upper r hd
  have hm := tilted_ratio r hd hz
  have hmu := tilted_upper r hd hz
  have hfloor_one : min 1 (l r x y)≤1 := min_le_left _ _
  have hfloor_l : min 1 (l r x y)≤l r x y := min_le_right _ _
  have hceil_one : (1:ℝ)≤(6/5)*min 1 (l r x y) := by
    rcases le_total 1 (l r x y) with h|h
    · rw [min_eq_left h]
      norm_num
    · rw [min_eq_right h]
      linarith
  have hceil_l : l r x y≤(6/5)*min 1 (l r x y) := by
    rcases le_total 1 (l r x y) with h|h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith
  have hceil_m : tilted r x y z≤(6/5)*min 1 (l r x y) := by
    rcases le_total 1 (l r x y) with h|h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      nlinarith [hm.2]
  fin_cases i
  · exact ⟨hfloor_one,hceil_one⟩
  · exact ⟨hfloor_l,hceil_l⟩
  · exact ⟨hfloor_l.trans (le_max_left _ _),max_le hceil_l hceil_m⟩
  · exact ⟨hfloor_one,hceil_one⟩

theorem pairwise_ratio (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) (i j : Fin 4) :
    5*qWeights r x y z i≤6*qWeights r x y z j := by
  have hi := pair_scale_bounds r hd hz i
  have hj := pair_scale_bounds r hd hz j
  linarith

theorem coefficient_domain (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) :
    k r x y∈Icc (1/2:ℝ) (17/20) ∧
    l r x y∈Icc (k r x y) (2*k r x y) ∧
    c r x y∈Icc (k r x y) 2 ∧
    l r x y≤2*tilted r x y z ∧ tilted r x y z≤2*l r x y := by
  have hb := base_bounds r hd
  have hm := tilted_ratio r hd hz
  exact ⟨⟨by linarith [hb.k_lower],hb.k_upper⟩,
    ⟨hb.k_le_l,by linarith [hb.l_le_three_halves_k,hb.k_lower]⟩,
    ⟨hb.k_le_c,hb.c_le_two⟩,by nlinarith [hm.1,hb.l_positive],
    by nlinarith [hm.2,hb.l_positive]⟩

/-- The full concentration endpoint has the same three negative
alternatives even when the E charge changes the total angle. -/
theorem balanced_endpoint (r : Region) {x y z : ℝ} (hd : Domain r x y)
    (hz : z∈Icc 0 (theta r x y)) (i j : Fin 4) :
    TwoPositive.balancedEnvelope (k r x y) (l r x y) (tilted r x y z) (delta r x y)≤
      TwoPositive.endpoint (k r x y) (l r x y) (tilted r x y z) (delta r x y) i j := by
  exact TwoPositive.balanced_endpoint_lower
    (fun i => (pair_domain r hd hz i).1)
    (fun i => (pair_domain r hd hz i).2.1)
    (fun i => (pair_domain r hd hz i).2.2)
    (pairwise_ratio r hd hz)
    ⟨by linarith [(domains hd).2.2.1],(domains hd).2.2.2⟩ i j

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Explicit
