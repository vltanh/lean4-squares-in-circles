module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositive

/-!
# Eight squares: positive outer source and positive core target, original zero owner

The original separator forces the target onto its core side, the angle
above `.4`, and the original outer secondary coordinate above
`.828+.764 B`. A single sloping line supports the remaining outer arc.
These geometric inequalities pay all four exact label families directly;
no angle partition or target-contact minimizer is needed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.PositiveOuter

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-25648/100000,-11418/100000,-94615/100000,7943/100000]
def p : Row → ℝ := ![0,-9133/100000,51554/100000,-19335/100000]
def q : Row → ℝ := ![94766/100000,88074/100000,119909/100000,76744/100000]
def g : Row → ℝ := ![62095/100000,62095/100000,58829/100000,62750/100000]

/-- The positivity half of `CommonQuarter.zero_positive_secondary_angle` (not imported here):
the original weak separator forces a positive angle. -/
private lemma zero_positive_angle_pos {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : 0<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  by_contra! hn
  have hsin : Real.sin φ≤0 := by
    have hp := positive_trig (x := -φ) ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht'.1]) hsin
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  norm_num [forwardMargin] at hm
  nlinarith [hs'.2.2.2.2]

lemma original_cuts {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (2/5:ℝ)<φ ∧ A=7/12 ∧ (207/250:ℝ)+(191/250)*B<b := by
  have hp := zero_positive_angle_pos (source := .outer) (target := .coreSide)
    (by simpa [State] using hs) (by simpa [State] using ht) hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have ho := outer_bounds hs
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hm' : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    rw [hw] at hm
    linarith
  have hAs := mul_le_mul_of_nonneg_right hcore.2.1 tr.2.2.1
  have hc0 : 0≤Real.cos φ := (lt_trans (by norm_num) tr.1).le
  have hsmall : B<1/2 := by
    by_contra! hlarge
    have hBc := mul_le_mul_of_nonneg_right hlarge hc0
    linarith [ho.2.2.2.1,outer_endpoint_bounds.2.2.2,tr.1,tr.2.2.2.1]
  obtain ⟨hA,_⟩ := core_small_side ht hsmall
  rw [hA] at hm'
  have hBc := mul_nonneg hcore.2.2.1 hc0
  have hangle : (2/5:ℝ)<φ := by
    by_contra! hn
    have hco := Real.one_sub_sq_div_two_le_cos (x := φ)
    have hsi := Real.sin_le hx.1
    have hs2 := pow_le_pow_left₀ hx.1 hn 2
    linarith [ho.2.2.2.1,outer_endpoint_bounds.2.2.2]
  have hBc' := mul_le_mul_of_nonneg_right
    (le_trans (by norm_num : (191/250:ℝ)≤19121/25000) tr.1.le) hcore.2.2.1
  exact ⟨hangle,hA,by linarith [tr.1,tr.2.2.2.1]⟩

/-- One circle calculation gives a supporting line on the entire arc
selected by the original owner. The reference point is strictly outside
the containing circle, providing a uniform reserve. -/
lemma original_sloping_line {a b : ℝ} (hs : OuterState a b) (hb : (207/250:ℝ)≤b) :
    a+(9/10)*b<(1072/625:ℝ) := by
  have hbu : b<9/10 := (outer_bounds hs).2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  by_contra! hn
  have hl : 0≤(97/100:ℝ)-(9/10)*(b-207/250)+1/2 := by linarith
  have hsqa := pow_le_pow_left₀ hl
    (show (97/100:ℝ)-(9/10)*(b-207/250)+1/2≤a+1/2 by linarith) 2
  have hc := hs.2.2
  norm_num [Q0] at hc
  nlinarith [sq_nonneg (b-207/250)]

lemma role_comparisons (r : Row) (hr : r≠2) :
    p r≤0 ∧ 0≤q r-(9/10)*p r ∧
      0≤(191/250)*(q r-(9/10)*p r)-g r ∧
        (449/500:ℝ)<2/5+c r+(97/100)*p r+(207/250)*q r := by
  fin_cases r
  · norm_num [c,p,q,g]
  · norm_num [c,p,q,g]
  · exact absurd rfl hr
  · norm_num [c,p,q,g]

/-- The four complete positive-outer/positive-core families with their
original weak source-secondary axis and complete core state. -/
theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r+p r*a+q r*b-g r*B := by
  obtain ⟨hangle,hA,hb⟩ := original_cuts hs ht hφ hm
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
  have hb0 : (207/250:ℝ)≤b := by linarith
  by_cases hr : r=2
  · subst r
    have ha : (899/1000:ℝ)<a :=
      (by linarith [fine_diagonal_bounds.1] : (899/1000:ℝ)<outerDiagonal).trans_le
        (outer_bounds hs).1
    norm_num [c,p,q,g]
    nlinarith
  · have hline := original_sloping_line hs hb0
    have hh := role_comparisons r hr
    have hp := mul_le_mul_of_nonpos_left hline.le hh.1
    have hq := mul_le_mul_of_nonneg_left hb.le hh.2.1
    have hrem := mul_nonneg hh.2.2.1 hB
    nlinarith only [hangle,hp,hq,hrem,hh.2.2.2]

end SquaresInCircles.Eight.ShortMixedZero.PositiveOuter
