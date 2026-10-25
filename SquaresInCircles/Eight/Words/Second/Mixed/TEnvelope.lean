module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLabels
public import SquaresInCircles.Eight.Words.Second.Outer.ConcaveSlope

/-!
# Eight squares: A single affine upper bound for the actual T label

One tangent parabola controls the concave initial arc.  On the entire
remaining arc the concave derivative of the negative label makes its
minimum an endpoint value.  The result holds on the complete physical
outer circle, without an angular or radial cover.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def q : ℝ := 633/1000
def k : ℝ := 1109/10000
def difference (b : ℝ) : ℝ := q*b-T b

lemma half_mem : (1/2:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma half_references : T (1/2)<(21037/50000:ℝ) ∧
    |TLabel.d1 (1/2)-q|<(33/10000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain half_mem)
    (l := (170751281/100000000:ℝ)) (u := (85375641/50000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := TLabel.first_chart_reference (outer_domain half_mem)
    (l := (170751281/100000000:ℝ)) (u := (85375641/50000000:ℝ))
    (dlo := (6297/10000:ℝ)) (dhi := (63/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  constructor
  · dsimp [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    dsimp [U] at hr
    nlinarith [hr.1]
  · rw [abs_lt]
    norm_num [q]
    constructor <;> linarith [hd.1,hd.2]

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (q-TLabel.d1 b) b :=
  TLabel.affine_difference_hasDerivAt q (outer_domain hb)

lemma early {b : ℝ} (hb : b∈Icc (0:ℝ) (3/5)) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (0:ℝ) (3/5)) : x∈Icc 0 outerDiagonal :=
    ⟨hx.1,hx.2.trans T_six_mem.2⟩
  have ht := curvature_tangent (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (κ := (6/125:ℝ)) hb
    (show (1/2:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => by
      have hm := T_second_monotone (hdom x hx) T_six_mem hx.2
      linarith [T_six_second.2])
  have hd := abs_lt.mp half_references.2
  have hs : (q-TLabel.d1 (1/2))^2<(33/10000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((6/125)*(b-1/2)+(q-TLabel.d1 (1/2)))
  dsimp [difference,q,k] at *
  nlinarith [half_references.1]

lemma late {b : ℝ} (hb : b∈Icc (3/5:ℝ) outerDiagonal) : -k<difference b := by
  have hdom (x : ℝ) (hx : x∈Icc (3/5:ℝ) outerDiagonal) : x∈Icc 0 outerDiagonal :=
    ⟨by linarith [hx.1],hx.2⟩
  have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (f := difference) (d := fun x => q-TLabel.d1 x)
    (dd := fun x => -TLabel.d2 x) (ddd := fun x => -TLabel.d3 x) hb
    (fun x hx => difference_hasDerivAt (hdom x hx))
    (fun x hx => (TLabel.d1_hasDerivAt (outer_domain (hdom x hx))).const_sub q)
    (fun x hx => (TLabel.d2_hasDerivAt (outer_domain (hdom x hx))).neg)
    (fun x hx => by linarith [T_third_lower (hdom x hx)])
    (by norm_num [q]; linarith [T_six_first.2])
  have hl := early (show (3/5:ℝ)∈Icc (0:ℝ) (3/5) by norm_num)
  have hr : -k<difference outerDiagonal := by
    dsimp [difference,q,k]
    linarith [T_diagonal_upper,diagonal_fine.1]
  exact (lt_min hl hr).trans_le hm

theorem upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : T b<k+q*b := by
  have hh : -k<difference b := by
    by_cases he : b≤3/5
    · exact early ⟨hb.1,he⟩
    · exact late ⟨by linarith,hb.2⟩
  dsimp [difference] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedTEnvelope
