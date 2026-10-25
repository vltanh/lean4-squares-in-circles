module

public import SquaresInCircles.Eight.TableFree.SecondMixedPHeightTaylor

/-!
# The side quadratic lower bound at original physical heights

The actual outer height is always at least 1.399. On that whole
physical interval the negative P label has curvature above .78.
A single reference at 1.4 proves the rational quadratic minorant,
whose own monotonicity permits lower separator heights down to one.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.PHeightQuadratic
open CommonQuarter CorePairGeometry Arithmetic HeightLabel PHeightBounds

def c : ℝ := -158027387/200000000
def p : ℝ := 973417553/1000000000
def k : ℝ := 39/100
def poly (u : ℝ) : ℝ := c+p*(u-7/5)+k*(u-7/5)^2
def d1 (u : ℝ) : ℝ := p+2*k*(u-7/5)

lemma reference_bounds : -(395068467/500000000:ℝ)<PHeight.eval (7/5) ∧
    |PHeight.d1 (7/5)-p|<(1/2500000000:ℝ) := by
  have hu : (7/5:ℝ)∈heights := by norm_num [heights]
  have hr := root_cage (u := (7/5:ℝ))
    (l := (1398427688513/1000000000000:ℝ)) (r := (699213844257/500000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (domain hu)
  have he := PHeight.d1_mul (domain hu)
  constructor
  · norm_num [PHeight,HeightLabel.eval,Q0]
    nlinarith [hr.2]
  · rw [abs_lt]
    constructor
    · apply (mul_lt_mul_iff_left₀ hp).mp
      norm_num [PHeight,p,Q0] at he ⊢
      nlinarith [hr.1,hr.2]
    · apply (mul_lt_mul_iff_left₀ hp).mp
      norm_num [PHeight,p,Q0] at he ⊢
      nlinarith [hr.1,hr.2]

lemma poly_hasDerivAt (u : ℝ) : HasDerivAt poly (d1 u) u := by
  convert ((((hasDerivAt_id u).sub_const (7/5)).const_mul p).const_add c).add
    ((((hasDerivAt_id u).sub_const (7/5)).pow 2).const_mul k) using 1
  · funext x
    simp only [poly,Pi.add_apply,Pi.pow_apply,id]
  · dsimp [d1]
    ring

lemma poly_monotone : MonotoneOn poly heights :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (poly_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => poly_hasDerivAt u)
    (fun u hu => by dsimp [d1,p,k]; linarith [hu.1])

theorem lower {u : ℝ} (hu : u∈physicalHeights) : poly u<PHeight.eval u := by
  have hr : (7/5:ℝ)∈physicalHeights := by norm_num [physicalHeights]
  have hcurv {x : ℝ} (hx : x∈physicalHeights) : (39/50:ℝ)≤PHeight.d2 x := by
    have hm := second_monotone (physical_subset PHeightTaylor.reference_mem) (physical_subset hx) hx.1
    have hh := PHeightTaylor.reference_bounds.2.2.1
    dsimp [PHeightTaylor.c2] at hh
    linarith
  have ht := curvature_tangent (f := PHeight.eval) (d := PHeight.d1) (dd := PHeight.d2)
    (κ := (39/50:ℝ)) hu hr
    (fun _ hx => PHeight.eval_hasDerivAt (domain (physical_subset hx)))
    (fun _ hx => PHeight.d1_hasDerivAt (domain (physical_subset hx)))
    (fun _ hx => hcurv hx)
  have hd := abs_lt.mp reference_bounds.2
  have hproduct : -(3/12500000000:ℝ)≤(PHeight.d1 (7/5)-p)*(u-7/5) := by
    by_cases he : 0≤u-7/5
    · have hh := mul_le_mul_of_nonneg_right hd.1.le he
      have huHi : u-7/5≤3/5 := by linarith [hu.2]
      nlinarith
    · have hh := mul_le_mul_of_nonpos_right hd.2.le (not_le.mp he).le
      have huLo : -(3/5:ℝ)≤u-7/5 := by linarith [hu.1]
      nlinarith
  dsimp [poly,c,k]
  nlinarith [reference_bounds.1]

theorem original_lower {a b u : ℝ} (hs : OuterState a b) (hu : u∈heights) (hcut : u≤a+1/2) :
    poly u< -P b := by
  have ha := actual_height hs
  have hm := poly_monotone hu (physical_subset ha) hcut
  have hh := lower ha
  rw [PHeight_actual hs] at hh
  exact hm.trans_lt hh

end SquaresInCircles.Eight.TableFree.SecondWord.PHeightQuadratic
