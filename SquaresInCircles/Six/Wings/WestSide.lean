module

public import SquaresInCircles.Six.Wings.Chord
public import SquaresInCircles.Six.Wings.Chart
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Six.Normalization.Basic

/-!
# Six squares: W on the west side of C

When W is separated from C along the west side of C, no wing is missing. The
weights `4`, `3`, `3` on the separations of C and W, of W and D along the
secondary axis of W and of D and S along that of D give W the force
`(4 cos v, 4 sin v - 3)` and D a force of length `6 sin (q/2)`; for a missing
south wing with `s ≤ 12/25` the far-vertex supports and the box of C leave the
gap `gap w d`, concave in `d` and in `w` on each side of `w = 0`, positive at
six points. For `s ≥ 12/25`, where S is on its own axis, the weight `10` on C–S
adds the force `(10 + 3 cos r, 3 sin r)` on S, in the axial cone, whose support
is `ρ̄` times its radial component; the profile decreases in `d`, is a harmonic
with nonnegative coefficients in `s` and concave in `v` on each side of `0`. For
a missing west wing with S on the south side of C, the weights `2`, `4`, `3`,
`3` on C–W, C–S, W–D along the secondary axis of D and D–S along that of S leave
a gap concave in each angle, positive at twelve points. The radicals
`R0 √(p + q sin x)` of the far-vertex supports of W and S are concave by the
curvature criterion of `radicalTrig`. Unit forces along the secondary axes of D
and of S give D the force `(cos x, 1 - sin x)`, of length
`√2 (cos (x/2) - sin (x/2))`; the term `diagonalTerm c x` that its far vertex
leaves is concave for `c ≤ 4`, here with `c = √2 R0` and in `WestDiagonal` with
a decimal bound of it. The values at the points are bounded by squaring.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Wings.WestSide
open Normalization

/-! ### The term of the force `(4 cos x, 3 - 4 sin x)` -/

/-- The terms in `s` that the force `(4 cos s, 3 - 4 sin s)`, of length
`√(25 - 24 sin s)`, leaves in a gap after its far-vertex support. -/
def southTerm (s : ℝ) : ℝ :=
  4*Real.cos s+4*max (-Real.sin s) 0-R0*Real.sqrt (25-24*Real.sin s)

lemma cos_small {x : ℝ} (hx : -(2/5) ≤ x ∧ x ≤ 2/5) :
    23/25 ≤ Real.cos x := by
  have hp := mul_nonneg (show 0 ≤ x+2/5 by linarith [hx.1])
    (show 0 ≤ 2/5-x by linarith [hx.2])
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]

private lemma south_radical_concave {B l u : ℝ}
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hB : ∀ x ∈ Set.Icc l u, 0 ≤ B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u) (radicalTrig 4 B 25 (-24) R0) := by
  apply radicalTrig_concave R0_nonneg (by norm_num)
  · intro x _
    linarith [Real.sin_le_one x]
  · intro x hx
    have hr : 0 ≤ 25-24*Real.sin x := by linarith [Real.sin_le_one x]
    have hs := Real.sq_sqrt hr
    have hroot : Real.sqrt (25-24*Real.sin x) ≤ 7 := by
      nlinarith [Real.neg_one_le_sin x,Real.sqrt_nonneg (25-24*Real.sin x)]
    have hprod := mul_le_mul_of_nonneg_left hroot R0_nonneg
    have hc := cos_small ⟨hl.trans hx.1,hx.2.trans hu⟩
    have hb := hB x hx
    have e : (25:ℝ) + -24*Real.sin x = 25-24*Real.sin x := by ring
    rw [e]
    linarith [R0_bounds.2]

lemma southTerm_negative_concave :
    ConcaveOn ℝ (Set.Icc (-(2/5)) 0) southTerm := by
  have hsin (x : ℝ) (hx : x ∈ Set.Icc (-(2/5)) 0) : Real.sin x ≤ 0 := by
    have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := -x)
      (by linarith [hx.2]) (by linarith [hx.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at h
    linarith
  have hh := south_radical_concave (B := -4) (l := -(2/5)) (u := 0)
    le_rfl (by norm_num) (fun x hx => by linarith [hsin x hx])
  apply hh.congr
  intro x hx
  dsimp [radicalTrig,southTerm]
  rw [max_eq_left (show 0 ≤ -Real.sin x by linarith [hsin x hx])]
  ring_nf

lemma southTerm_positive_concave :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) southTerm := by
  have hh := south_radical_concave (B := 0) (l := 0) (u := 2/5)
    (by norm_num) le_rfl (fun _ _ => by simp)
  apply hh.congr
  intro x hx
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  dsimp [radicalTrig,southTerm]
  rw [max_eq_right (show -Real.sin x ≤ 0 by linarith)]
  ring_nf

/-! ### The term of the force `(cos x, 1 - sin x)`

Unit forces along the secondary axes of D and of S give D the force
`(cos x, 1 - sin x)`, of length `√2 · halfDifference x` (`norm_identity`). With
`c` for `√2` times the radius, its far-vertex support leaves the term
`diagonalTerm c x`; `diagonalFirst` and `diagonalSecond` are its derivatives. -/

def halfDifference (x : ℝ) : ℝ := Real.cos (x/2)-Real.sin (x/2)

def diagonalTerm (c x : ℝ) : ℝ := Real.cos x-c*Real.cos (x/2)+c*Real.sin (x/2)
def diagonalFirst (c x : ℝ) : ℝ := -Real.sin x+(c/2)*(Real.sin (x/2)+Real.cos (x/2))
def diagonalSecond (c x : ℝ) : ℝ := -Real.cos x+(c/4)*halfDifference x

lemma half_difference_lower {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 6/5) :
    0 ≤ halfDifference x := by
  have h := sin_le_cos_of_small (x := x/2)
    ⟨by linarith [hx.1],by linarith [hx.2,Real.pi_gt_d2]⟩
  dsimp [halfDifference]
  linarith

lemma norm_identity (x : ℝ) :
    (Real.cos x)^2+(1-Real.sin x)^2=2*(halfDifference x)^2 := by
  have hs : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    simpa only [show 2*(x/2)=x by ring] using Real.sin_two_mul (x/2)
  dsimp [halfDifference]
  linear_combination Real.sin_sq_add_cos_sq x-2*Real.sin_sq_add_cos_sq (x/2)-2*hs

lemma diagonal_hasDeriv (c x : ℝ) : HasDerivAt (diagonalTerm c) (diagonalFirst c x) x := by
  convert (((Real.hasDerivAt_cos x).sub
    ((((hasDerivAt_id x).div_const 2).cos).const_mul c)).add
    ((((hasDerivAt_id x).div_const 2).sin).const_mul c)) using 1
  · funext y; simp only [diagonalTerm,Pi.add_apply,Pi.sub_apply,id_eq]
  · dsimp [diagonalFirst]; ring

lemma diagonal_first_hasDeriv (c x : ℝ) :
    HasDerivAt (diagonalFirst c) (diagonalSecond c x) x := by
  convert (((Real.hasDerivAt_sin x).const_mul (-1)).add
    (((((hasDerivAt_id x).div_const 2).sin).add
      (((hasDerivAt_id x).div_const 2).cos)).const_mul (c/2))) using 1
  · funext y; simp only [diagonalFirst,Pi.add_apply,id_eq]; ring
  · dsimp [diagonalSecond,halfDifference]; ring

/-- The curvature is `halfDifference x · (c/4 - cos (x/2) - sin (x/2))`, as
`cos x = halfDifference x · (cos (x/2) + sin (x/2))`. -/
lemma diagonal_second_nonpositive {c x : ℝ} (hc : c ≤ 4) (hx : 0 ≤ x ∧ x ≤ 6/5) :
    diagonalSecond c x ≤ 0 := by
  have hu := half_difference_lower hx
  obtain ⟨hcos,hsin⟩ := cos_sin_nonneg (x := x/2)
    ⟨by linarith [hx.1],by linarith [hx.2,Real.pi_gt_d2]⟩
  have hsum : 1 ≤ Real.cos (x/2)+Real.sin (x/2) := by
    nlinarith [mul_nonneg hsin hcos,Real.sin_sq_add_cos_sq (x/2)]
  have hp := mul_nonpos_of_nonneg_of_nonpos hu
    (show -(Real.cos (x/2)+Real.sin (x/2))+c/4 ≤ 0 by linarith)
  have hid : Real.cos x=halfDifference x*(Real.cos (x/2)+Real.sin (x/2)) := by
    have h := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at h
    dsimp [halfDifference]
    nlinarith only [h,Real.sin_sq_add_cos_sq (x/2)]
  dsimp [diagonalSecond]
  rw [hid]
  dsimp [halfDifference] at hp ⊢
  nlinarith only [hp]

lemma diagonal_concave {c : ℝ} (hc : c ≤ 4) :
    ConcaveOn ℝ (Set.Icc 0 (6/5)) (diagonalTerm c) :=
  concave_of_deriv2 (fun x _ => diagonal_hasDeriv c x) (fun x _ => diagonal_first_hasDeriv c x)
    fun _ h => diagonal_second_nonpositive hc h

/-! ### Values at the points -/

/-- Brackets of `cos` and `sin` at `2/5`, `9/10` and `1/10`; those at `1/2` are
`trig_bracket_half`. -/
lemma trig_two_fifths : (0.921:ℝ) ≤ Real.cos (2/5) ∧ (0.389:ℝ) ≤ Real.sin (2/5) ∧
    Real.sin ((2:ℝ)/5) ≤ 0.39 :=
  ⟨by nlinarith only [cos_lower_six (x := (2:ℝ)/5) (by norm_num)],
    by nlinarith only [sin_lower_seven (x := (2:ℝ)/5) (by norm_num)],
    by nlinarith only [sin_upper_five (x := (2:ℝ)/5) (by norm_num)]⟩

lemma trig_nine_tenths : (0.621:ℝ) ≤ Real.cos (9/10) ∧ (0.783:ℝ) ≤ Real.sin (9/10) :=
  ⟨by nlinarith only [cos_lower_six (x := (9:ℝ)/10) (by norm_num)],
    by nlinarith only [sin_lower_seven (x := (9:ℝ)/10) (by norm_num)]⟩

lemma trig_tenth : (0.995:ℝ) ≤ Real.cos (1/10) ∧ (0.099:ℝ) ≤ Real.sin (1/10) :=
  ⟨by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/10)],
    by nlinarith only [sin_lower_seven (x := (1:ℝ)/10) (by norm_num)]⟩

lemma half_root_bounds : (0.707:ℝ) ≤ Real.sqrt 2/2 ∧ Real.sqrt 2/2 ≤ 0.708 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

/-- Brackets at `π/4 ± 2/5`, from those at `2/5` and `√2/2 ≥ 0.707`. -/
lemma quarter_shift_bounds :
    (0.375:ℝ) ≤ Real.cos (Real.pi/4+2/5) ∧ (0.926:ℝ) ≤ Real.sin (Real.pi/4+2/5) ∧
    (0.926:ℝ) ≤ Real.cos (Real.pi/4-2/5) ∧ (0.375:ℝ) ≤ Real.sin (Real.pi/4-2/5) ∧
    (1.302:ℝ) ≤ Real.cos (Real.pi/4+2/5)+Real.sin (Real.pi/4+2/5) := by
  have hm := mul_le_mul half_root_bounds.1
    (show (0.531:ℝ) ≤ Real.cos (2/5)-Real.sin (2/5) by
      linarith [trig_two_fifths.1,trig_two_fifths.2.2])
    (by norm_num) (by positivity : 0 ≤ Real.sqrt 2/2)
  have hp := mul_le_mul half_root_bounds.1
    (show (1.31:ℝ) ≤ Real.cos (2/5)+Real.sin (2/5) by
      linarith [trig_two_fifths.1,trig_two_fifths.2.1])
    (by norm_num) (by positivity : 0 ≤ Real.sqrt 2/2)
  have hc := mul_le_mul half_root_bounds.1 trig_two_fifths.1
    (by norm_num) (by positivity : 0 ≤ Real.sqrt 2/2)
  rw [Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
    Real.cos_pi_div_four,Real.sin_pi_div_four]
  constructor
  · nlinarith only [hm]
  constructor
  · nlinarith only [hp]
  constructor
  · nlinarith only [hp]
  constructor
  · nlinarith only [hm]
  · nlinarith only [hc]

/-! ### A missing west wing with S on the south side of C -/

namespace MissingWest

/-! With the weights `2`, `4`, `3`, `3` on C–W, C–S, W–D and D–S, the far-vertex
supports of W, S and D leave the terms `westTerm w d`, `southTerm s` and
`diagonalTerm (d - s)` in the gap; the forces on W and D have the lengths
`√(13 + 12 sin d)` and `√(18 - 18 sin (d - s))`. -/

def diagonalTerm (x : ℝ) : ℝ :=
  3*Real.cos x-R0*Real.sqrt (18-18*Real.sin x)

def westTerm (w d : ℝ) : ℝ :=
  3*(Real.cos (d-w)+Real.sin (d-w))-R0*Real.sqrt (13+12*Real.sin d)

def gap (w s d : ℝ) : ℝ :=
  9-6*c0+2*Real.cos w+southTerm s+diagonalTerm (d-s)+westTerm w d

private lemma offset_range {d t : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    0 ≤ d-t ∧ d-t ≤ 6/5 := by
  constructor <;> linarith [hd.1,hd.2,ht.1,ht.2,Real.pi_lt_d2]

private lemma cos_add_sin_lower {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 6/5) :
    1 ≤ Real.cos x+Real.sin x := by
  obtain ⟨hc,hs⟩ := cos_sin_nonneg ⟨hx.1,by linarith [hx.2,Real.pi_gt_d2]⟩
  nlinarith [mul_nonneg hs hc,Real.sin_sq_add_cos_sq x]

/-- The term of D is `3 WestSide.diagonalTerm (√2 R0)` on `[0, 6/5]`, as
`18 - 18 sin x = 2 (3 halfDifference x)²` (`norm_identity`), and `√2 R0 ≤ 4`. -/
lemma diagonalTerm_concave :
    ConcaveOn ℝ (Set.Icc 0 (6/5)) diagonalTerm := by
  have hc : Real.sqrt 2*R0 ≤ 4 := by
    nlinarith [half_root_bounds.2,R0_bounds.2,R0_nonneg,Real.sqrt_nonneg 2]
  refine ((WestSide.diagonal_concave hc).smul (by norm_num : (0:ℝ) ≤ 3)).congr
    fun x hx => ?_
  have hr : Real.sqrt (18-18*Real.sin x)=Real.sqrt 2*(3*halfDifference x) := by
    rw [show 18-18*Real.sin x=2*(3*halfDifference x)^2 by
        nlinarith [norm_identity x,Real.sin_sq_add_cos_sq x],
      Real.sqrt_mul (by norm_num),Real.sqrt_sq (by linarith [half_difference_lower hx])]
  simp only [smul_eq_mul,WestSide.diagonalTerm,diagonalTerm,hr,halfDifference]
  ring

lemma westTerm_diagonal_concave {w : ℝ} (hw : -(2/5) ≤ w ∧ w ≤ 0) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (westTerm w) := by
  let A := 3*(Real.cos w-Real.sin w)
  let B := 3*(Real.cos w+Real.sin w)
  have he (d : ℝ) : A*Real.cos d+B*Real.sin d=
      3*(Real.cos (d-w)+Real.sin (d-w)) := by
    dsimp [A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hh : ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (radicalTrig A B 13 12 R0) := by
    apply radicalTrig_concave R0_nonneg (by norm_num)
    · intro d _
      linarith [Real.neg_one_le_sin d]
    · intro d hd
      have hr : 0 ≤ 13+12*Real.sin d := by linarith [Real.neg_one_le_sin d]
      have hs := Real.sq_sqrt hr
      have hroot : Real.sqrt (13+12*Real.sin d) ≤ 5 := by
        nlinarith [Real.sin_le_one d,Real.sqrt_nonneg (13+12*Real.sin d)]
      have hmul := mul_le_mul_of_nonneg_left hroot R0_nonneg
      have ht := cos_add_sin_lower (offset_range hd ⟨hw.1,by linarith [hw.2]⟩)
      rw [he]
      nlinarith [ht,R0_bounds.2]
  apply hh.congr
  intro d _
  simp only [radicalTrig,westTerm,he]

lemma gap_diagonal_concave {w s : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 0) (hs : -(2/5) ≤ s ∧ s ≤ 2/5) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => gap w s d) := by
  have hd := concave_affine_argument (a := 1) (b := -s) diagonalTerm_concave
    (fun d hd => by
      obtain ⟨h1,h2⟩ := offset_range hd hs
      exact ⟨by linarith,by linarith⟩)
  have h := ((concaveOn_const (9-6*c0+2*Real.cos w+southTerm s)
    (convex_Icc (1/2) (Real.pi/4))).add hd).add
    (westTerm_diagonal_concave hw)
  apply h.congr
  intro d _
  have e : 1*d+-s = d-s := by ring
  simp only [Pi.add_apply,gap,e]

lemma gap_west_concave {s d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    ConcaveOn ℝ (Set.Icc (-(2/5)) 0) (fun w => gap w s d) := by
  let A := 2+3*(Real.cos d+Real.sin d)
  let B := 3*(Real.sin d-Real.cos d)
  have he (w : ℝ) : A*Real.cos w+B*Real.sin w=
      2*Real.cos w+3*(Real.cos (d-w)+Real.sin (d-w)) := by
    dsimp [A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hh : ConcaveOn ℝ (Set.Icc (-(2/5)) 0) (radicalTrig A B 1 0 0) := by
    apply radicalTrig_concave (by norm_num) (by norm_num)
    · intro _ _; norm_num
    · intro w hw
      have hc := cos_small ⟨hw.1,by linarith [hw.2]⟩
      have ht := cos_add_sin_lower (offset_range hd ⟨hw.1,by linarith [hw.2]⟩)
      rw [he]
      nlinarith [ht]
  let K := 9-6*c0+southTerm s+diagonalTerm (d-s)-R0*Real.sqrt (13+12*Real.sin d)
  have h := hh.add (concaveOn_const K (convex_Icc (-(2/5)) 0))
  apply h.congr
  intro w _
  dsimp [radicalTrig,K,gap,westTerm]
  rw [he]
  ring

lemma gap_south_concave {w d l u : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hs : ConcaveOn ℝ (Set.Icc l u) southTerm) :
    ConcaveOn ℝ (Set.Icc l u) (fun s => gap w s d) := by
  have hh := concave_affine_argument (a := -1) (b := d) diagonalTerm_concave
    (fun s hs => by
      have hm := offset_range hd ⟨hl.trans hs.1,hs.2.trans hu⟩
      exact ⟨by linarith [hm.1],by linarith [hm.2]⟩)
  let K := 9-6*c0+2*Real.cos w+westTerm w d
  have h := (hs.add hh).add (concaveOn_const K (convex_Icc l u))
  apply h.congr
  intro s _
  dsimp [gap,K]
  ring_nf

/-- Upper bounds of the radicals at the twelve points, each by squaring. -/
private lemma endpoint_root_bounds :
    Real.sqrt (13+12*Real.sin (1/2)) ≤ 4.331 ∧
    Real.sqrt (13+12*Real.sin (Real.pi/4)) ≤ 4.637 ∧
    Real.sqrt (18-18*Real.sin (9/10)) ≤ 1.977 ∧
    Real.sqrt (18-18*Real.sin (1/2)) ≤ 3.062 ∧
    Real.sqrt (18-18*Real.sin (1/10)) ≤ 4.028 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4+2/5)) ≤ 1.155 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4)) ≤ 2.297 ∧
    Real.sqrt (18-18*Real.sin (Real.pi/4-2/5)) ≤ 3.355 ∧
    Real.sqrt (25-24*Real.sin (-(2/5))) ≤ 5.862 ∧
    Real.sqrt (25-24*Real.sin (2/5)) ≤ 3.958 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> refine Real.sqrt_le_iff.mpr ⟨by norm_num,?_⟩
  · nlinarith only [trig_bracket_half.2.2.2]
  · rw [Real.sin_pi_div_four]
    nlinarith only [half_root_bounds.2]
  · nlinarith only [trig_nine_tenths.2]
  · nlinarith only [trig_bracket_half.2.2.1]
  · nlinarith only [trig_tenth.2]
  · nlinarith only [quarter_shift_bounds.2.1]
  · rw [Real.sin_pi_div_four]
    nlinarith only [half_root_bounds.1]
  · nlinarith only [quarter_shift_bounds.2.2.2.1]
  · rw [Real.sin_neg]
    nlinarith only [trig_two_fifths.2.2]
  · nlinarith only [trig_two_fifths.2.1]

/-! The twelve points `(westEnd i, southEnd j, diagonalEnd k)`, with decimal
bounds for the values of `cos`, `sin` and the radicals there. -/

def westEnd : Fin 2 → ℝ := ![-2/5,0]
def southEnd : Fin 3 → ℝ := ![-2/5,0,2/5]
def diagonalEnd : Fin 2 → ℝ := ![1/2,Real.pi/4]

private def westCosLower : Fin 2 → ℝ := ![0.921,1]
private def southCosLower : Fin 3 → ℝ := ![0.921,1,0.921]
private def southNegativeLower : Fin 3 → ℝ := ![0.389,0,0]
private def westSumLower : Fin 2 → Fin 2 → ℝ := ![![1.404,1.302],![1.356,1.414]]
private def diagonalCosLower : Fin 3 → Fin 2 → ℝ :=
  ![![0.621,0.375],![0.877,0.707],![0.995,0.926]]
private def westRootUpper : Fin 2 → ℝ := ![4.331,4.637]
private def diagonalRootUpper : Fin 3 → Fin 2 → ℝ :=
  ![![1.977,1.155],![3.062,2.297],![4.028,3.355]]
private def southRootUpper : Fin 3 → ℝ := ![5.862,5,3.958]

private lemma endpoint_trig (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    westCosLower i ≤ Real.cos (westEnd i) ∧
    southCosLower j ≤ Real.cos (southEnd j) ∧
    southNegativeLower j ≤ max (-Real.sin (southEnd j)) 0 ∧
    westSumLower i k ≤ Real.cos (diagonalEnd k-westEnd i)+Real.sin (diagonalEnd k-westEnd i) ∧
    diagonalCosLower j k ≤ Real.cos (diagonalEnd k-southEnd j) := by
  have hc4 := trig_two_fifths.1
  have hs4 := trig_two_fifths.2.1
  have hc5 := trig_bracket_half.1
  have hs5 := trig_bracket_half.2.2.1
  have hc9 := trig_nine_tenths.1
  have hs9 := trig_nine_tenths.2
  have hc1 := trig_tenth.1
  have hquarter := half_root_bounds.1
  obtain ⟨hqcm,hqsp,hqcp,hqsm,hqsum⟩ := quarter_shift_bounds
  refine ⟨?_,?_,?_,?_,?_⟩
  · fin_cases i <;> norm_num [westCosLower,westEnd]
    linarith
  · fin_cases j <;> norm_num [southCosLower,southEnd] <;> linarith
  · fin_cases j
    · have e : Real.sin (-2/5 : ℝ) = -Real.sin (2/5) := by
        rw [neg_div,Real.sin_neg]
      simp [southNegativeLower,southEnd,e,hs4]
    · simp [southNegativeLower,southEnd]
    · simp [southNegativeLower,southEnd]
  · fin_cases i <;> fin_cases k <;>
      norm_num [westSumLower,diagonalEnd,westEnd] at * <;> linarith
  · fin_cases j <;> fin_cases k <;>
      norm_num [diagonalCosLower,diagonalEnd,southEnd] at * <;> linarith

private lemma endpoint_roots (j : Fin 3) (k : Fin 2) :
    Real.sqrt (13+12*Real.sin (diagonalEnd k)) ≤ westRootUpper k ∧
    Real.sqrt (18-18*Real.sin (diagonalEnd k-southEnd j)) ≤ diagonalRootUpper j k ∧
    Real.sqrt (25-24*Real.sin (southEnd j)) ≤ southRootUpper j := by
  obtain ⟨hw0,hw1,hd0,hd1,hd2,hd3,hd4,hd5,hs0,hs2⟩ := endpoint_root_bounds
  refine ⟨?_,?_,?_⟩
  · fin_cases k <;> norm_num [diagonalEnd,westRootUpper] at * <;> linarith
  · fin_cases j <;> fin_cases k <;>
      norm_num [diagonalEnd,southEnd,diagonalRootUpper] at * <;> linarith
  · fin_cases j <;> norm_num [southEnd,southRootUpper] at * <;> linarith

/-- The gap at a point with the bounds of the tables, `coreUpper` for `c0` and
`radiusBound` for `R0`. -/
private def rationalReserve (i : Fin 2) (j : Fin 3) (k : Fin 2) : ℝ :=
  9-6*coreUpper+2*westCosLower i+4*southCosLower j+4*southNegativeLower j+
    3*westSumLower i k+3*diagonalCosLower j k-
    radiusBound*(westRootUpper k+diagonalRootUpper j k+southRootUpper j)

private lemma rationalReserve_positive (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    0 < rationalReserve i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [rationalReserve,westCosLower,southCosLower,southNegativeLower,
      westSumLower,diagonalCosLower,westRootUpper,diagonalRootUpper,southRootUpper,
      radiusBound,coreUpper]

lemma endpoint_positive (i : Fin 2) (j : Fin 3) (k : Fin 2) :
    0 < gap (westEnd i) (southEnd j) (diagonalEnd k) := by
  obtain ⟨hw,hs,hn,hq,hx⟩ := endpoint_trig i j k
  obtain ⟨hrW,hrD,hrS⟩ := endpoint_roots j k
  have hroots : Real.sqrt (13+12*Real.sin (diagonalEnd k))+
      Real.sqrt (18-18*Real.sin (diagonalEnd k-southEnd j))+
      Real.sqrt (25-24*Real.sin (southEnd j)) ≤
      westRootUpper k+diagonalRootUpper j k+southRootUpper j := by linarith
  have hprod := mul_le_mul ceiling_bounds.1 hroots (by positivity)
    (by norm_num [radiusBound] : (0:ℝ) ≤ radiusBound)
  have hc := ceiling_bounds.2.2.2
  have hres := rationalReserve_positive i j k
  dsimp [gap,southTerm,diagonalTerm,westTerm,rationalReserve] at *
  nlinarith

/-- The gap is positive on the whole domain, by concavity in each variable; the
interval of `s` is split at the corner `s = 0`. -/
theorem positive {w s d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 0)
    (hs : -(2/5) ≤ s ∧ s ≤ 2/5)
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 < gap w s d := by
  have hdi (k : Fin 2) : 1/2 ≤ diagonalEnd k ∧ diagonalEnd k ≤ Real.pi/4 := by
    fin_cases k <;> norm_num [diagonalEnd] <;> linarith [Real.pi_gt_d2]
  have hwend (i : Fin 2) (j : Fin 3) : 0 < gap (westEnd i) (southEnd j) d := by
    have hw' : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 0 := by
      fin_cases i <;> norm_num [westEnd]
    have hs' : -(2/5) ≤ southEnd j ∧ southEnd j ≤ 2/5 := by
      fin_cases j <;> norm_num [southEnd]
    have h0 := endpoint_positive i j 0
    have h1 := endpoint_positive i j 1
    rw [show diagonalEnd 0 = 1/2 by simp [diagonalEnd]] at h0
    rw [show diagonalEnd 1 = Real.pi/4 by simp [diagonalEnd]] at h1
    exact concave_gt_of_endpoints (f := fun d => gap (westEnd i) (southEnd j) d)
      (gap_diagonal_concave hw' hs') hd h0 h1
  have hsend (j : Fin 3) : 0 < gap w (southEnd j) d := by
    have h0 := hwend 0 j
    have h1 := hwend 1 j
    rw [show westEnd 0 = -(2/5) by norm_num [westEnd]] at h0
    rw [show westEnd 1 = 0 by simp [westEnd]] at h1
    exact concave_gt_of_endpoints (f := fun w => gap w (southEnd j) d)
      (gap_west_concave hd) hw h0 h1
  have k0 := hsend 0
  have k1 := hsend 1
  have k2 := hsend 2
  rw [show southEnd 0 = -(2/5) by norm_num [southEnd]] at k0
  rw [show southEnd 1 = 0 by simp [southEnd]] at k1
  rw [show southEnd 2 = 2/5 by simp [southEnd]] at k2
  by_cases hs0 : s ≤ 0
  · exact concave_gt_of_endpoints (f := fun s => gap w s d)
      (gap_south_concave hd le_rfl (by norm_num) southTerm_negative_concave)
      ⟨hs.1,hs0⟩ k0 k1
  · exact concave_gt_of_endpoints (f := fun s => gap w s d)
      (gap_south_concave hd (by norm_num) le_rfl southTerm_positive_concave)
      ⟨le_of_not_ge hs0,hs.2⟩ k1 k2

/-- There is no missing west wing with W and S separated from C along the west
and south sides of C: with the weights `2`, `4`, `3`, `3` on C–W, C–S, W–D and
D–S, the far-vertex supports of W, D and S and the box of C leave exactly
`gap (-v) s d`, which is positive. -/
theorem impossible {X : Wings.Chart} (hW : X.WestSide) (hS : X.SouthSide)
    (h : X.MissingWest) (hv : 0 ≤ X.v ∧ X.v ≤ 2/5) (hs : |X.s| ≤ 2/5)
    (hd : 1/2 ≤ X.d ∧ X.d ≤ Real.pi/4) : False := by
  obtain ⟨hWD,hSW⟩ := h
  simp only [Wings.Chart.WestSide,Wings.Chart.SouthSide,Wings.Chart.WestDiagonal,
    Wings.Chart.SouthWing] at hW hS hWD hSW
  obtain ⟨hs1,hs2⟩ := abs_le.mp hs
  rw [angularWidth_eq (x := X.v) ⟨hv.1,by linarith [Real.pi_gt_d2]⟩] at hW
  rw [angularWidth,abs_of_nonneg (by linarith [cos_small ⟨hs1,hs2⟩] : 0 ≤ Real.cos X.s)] at hS
  rw [angularWidth_eq (x := X.d+X.v) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩] at hWD
  rw [angularWidth_eq (x := X.d-X.s) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩] at hSW
  have hWs := local_vertex_support X.west
    (2*Real.cos X.v+3*Real.sin (X.d+X.v)) (2*Real.sin X.v-3*Real.cos (X.d+X.v))
  have hSs := local_vertex_support X.south
    (4*Real.cos X.s) (3-4*Real.sin X.s)
  have hDs := local_vertex_support X.diagonal
    (3*Real.cos (X.d-X.s)) (3-3*Real.sin (X.d-X.s))
  have hnW : (2*Real.cos X.v+3*Real.sin (X.d+X.v))^2+(2*Real.sin X.v-3*Real.cos (X.d+X.v))^2 =
      13+12*Real.sin X.d := by
    rw [Real.sin_add,Real.cos_add]
    linear_combination (13+12*Real.sin X.d)*Real.sin_sq_add_cos_sq X.v+
      9*(Real.sin X.v^2+Real.cos X.v^2)*Real.sin_sq_add_cos_sq X.d
  rw [hnW] at hWs
  rw [show (4*Real.cos X.s)^2+(3-4*Real.sin X.s)^2=25-24*Real.sin X.s by
    linear_combination 16*Real.sin_sq_add_cos_sq X.s] at hSs
  rw [show (3*Real.cos (X.d-X.s))^2+(3-3*Real.sin (X.d-X.s))^2=18-18*Real.sin (X.d-X.s) by
    linear_combination 9*Real.sin_sq_add_cos_sq (X.d-X.s)] at hDs
  have hwW := add_le_add (le_abs_self (2*Real.cos X.v+3*Real.sin (X.d+X.v)))
    (neg_le_abs (2*Real.sin X.v-3*Real.cos (X.d+X.v)))
  have hwS := add_le_add (le_abs_self (4*Real.cos X.s)) (le_abs_self (3-4*Real.sin X.s))
  have hwD := add_le_add (le_abs_self (3*Real.cos (X.d-X.s)))
    (le_abs_self (3-3*Real.sin (X.d-X.s)))
  have hcx := mul_le_mul_of_nonneg_left X.box.1.2 (by norm_num : (0:ℝ) ≤ 2)
  have hcy := mul_le_mul_of_nonneg_left X.box.2.2 (by norm_num : (0:ℝ) ≤ 4)
  have hmax : |Real.sin X.s|-Real.sin X.s=2*max (-Real.sin X.s) 0 := by
    rcases le_total 0 (Real.sin X.s) with h0 | h0
    · rw [abs_of_nonneg h0,max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h0,max_eq_left (by linarith)]; ring
  have hpos := positive (w := -X.v) (s := X.s) (d := X.d) ⟨by linarith,by linarith⟩
    ⟨hs1,hs2⟩ hd
  simp only [gap,southTerm,diagonalTerm,westTerm,Real.cos_neg,sub_neg_eq_add] at hpos
  nlinarith only [hW,hS,hWD,hSW,hWs,hSs,hDs,hwW,hwS,hwD,hcx,hcy,hmax,hpos]

end MissingWest

/-! ### A missing south wing with `s ≤ 12/25` -/

namespace SmallSouth

/-! With the weights `4`, `3`, `3` on C–W, W–D and D–S, the far-vertex supports
of W and D leave the term `westTerm w` of W and the chord term `chordTerm (d - w)`
of D, whose force has length `6 sin (q/2)`; `widthTerm d` bounds the threshold of
D–S below (`south_width_lower`). -/

def westTerm (w : ℝ) : ℝ := southTerm (-w)
def chordTerm (q : ℝ) : ℝ := 3*Real.sin q-6*R0*Real.sin (q/2)
def widthTerm (d : ℝ) : ℝ := 3*(Real.cos (d-12/25)+Real.sin (d-12/25))
def gap (w d : ℝ) : ℝ := 8-4*c0-3*R0+westTerm w+chordTerm (d-w)+widthTerm d

private lemma offset {w d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    0 ≤ d-w ∧ d-w ≤ 6/5 := by
  constructor <;> linarith [hw.1,hw.2,hd.1,hd.2,Real.pi_lt_d2]

lemma chordTerm_concave : ConcaveOn ℝ (Set.Icc 0 (6/5)) chordTerm := by
  let f' : ℝ → ℝ := fun q => 3*Real.cos q-3*R0*Real.cos (q/2)
  let f'' : ℝ → ℝ := fun q => -3*Real.sin q+(3*R0/2)*Real.sin (q/2)
  have hf (q : ℝ) : HasDerivAt chordTerm (f' q) q := by
    have hh := (((hasDerivAt_id q).div_const 2).sin).const_mul (6*R0)
    convert ((Real.hasDerivAt_sin q).const_mul 3).sub hh using 1
    · funext y
      simp only [chordTerm,Pi.sub_apply,id]
    · simp only [f',id]
      ring
  have hff (q : ℝ) : HasDerivAt f' (f'' q) q := by
    have hh := (((hasDerivAt_id q).div_const 2).cos).const_mul (3*R0)
    convert ((Real.hasDerivAt_cos q).const_mul 3).sub hh using 1
    · funext y
      simp only [f',Pi.sub_apply,id]
    · simp only [f'',id]
      ring
  refine concave_of_deriv2 (fun x _ => hf x) (fun x _ => hff x) fun q ⟨h1,h2⟩ => ?_
  have hsq := mul_nonneg (show 0 ≤ 3/5-q/2 by linarith) (show 0 ≤ 3/5+q/2 by linarith)
  have hc : 41/50 ≤ Real.cos (q/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := q/2)]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith) (show q/2 ≤ Real.pi by linarith [Real.pi_gt_d2])
  have hp := mul_nonpos_of_nonpos_of_nonneg
    (show -6*Real.cos (q/2)+3*R0/2 ≤ 0 by linarith [R0_bounds.2]) hs
  have hid : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
    simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
  dsimp [f'']
  nlinarith only [hp,hid]

lemma widthTerm_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) widthTerm := by
  have hc : ConcaveOn ℝ (Set.Icc 0 (2/5)) (radicalTrig 3 3 1 0 0) := by
    apply radicalTrig_concave (by norm_num) (by norm_num)
    · intro _ _; norm_num
    · intro x hx
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (by linarith [hx.2,Real.pi_gt_d2])
      have hc := Real.cos_nonneg_of_mem_Icc
        (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
      nlinarith
  have h := concave_affine_argument (a := 1) (b := -(12/25)) hc
    (l := 1/2) (u := Real.pi/4) (fun d hd => by
      constructor <;> linarith [hd.1,hd.2,Real.pi_lt_d2])
  convert h using 1
  funext d
  dsimp [radicalTrig,widthTerm]
  ring_nf

lemma westTerm_negative_concave : ConcaveOn ℝ (Set.Icc (-(2/5)) 0) westTerm := by
  have h := concave_affine_argument (a := -1) (b := 0)
    southTerm_positive_concave
    (l := -(2/5)) (u := 0) (fun w hw => by constructor <;> linarith [hw.1,hw.2])
  convert h using 1
  funext w
  simp [westTerm]

lemma westTerm_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) westTerm := by
  have h := concave_affine_argument (a := -1) (b := 0)
    southTerm_negative_concave
    (l := 0) (u := 2/5) (fun w hw => by constructor <;> linarith [hw.1,hw.2])
  convert h using 1
  funext w
  simp [westTerm]

lemma gap_diagonal_concave {w : ℝ} (hw : -(2/5) ≤ w ∧ w ≤ 2/5) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => gap w d) := by
  have hq0 := concave_affine_argument (a := 1) (b := -w) chordTerm_concave
    (l := 1/2) (u := Real.pi/4) (fun d hd => by simpa [sub_eq_add_neg] using offset hw hd)
  have hq : ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => chordTerm (d-w)) := by
    convert hq0 using 1
    funext d
    congr 1
    ring
  exact ((concaveOn_const (8-4*c0-3*R0+westTerm w) (convex_Icc (1/2) (Real.pi/4))).add hq).add
    widthTerm_concave

lemma gap_west_concave {d l u : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hw : ConcaveOn ℝ (Set.Icc l u) westTerm) :
    ConcaveOn ℝ (Set.Icc l u) (fun w => gap w d) := by
  have hq0 := concave_affine_argument (a := -1) (b := d) chordTerm_concave
    (l := l) (u := u) (fun w hmem => by
      have h := offset ⟨hl.trans hmem.1,hmem.2.trans hu⟩ hd
      constructor <;> linarith [h.1,h.2])
  have hq : ConcaveOn ℝ (Set.Icc l u) (fun w => chordTerm (d-w)) := by
    convert hq0 using 1
    funext w
    congr 1
    ring
  have h := ((concaveOn_const (8-4*c0-3*R0) (convex_Icc l u)).add hw).add hq
  exact h.add (concaveOn_const (widthTerm d) (convex_Icc l u))

/-- `√(18 - 18 cos q) = 6 sin (q/2)` for `0 ≤ q ≤ 6/5`. -/
lemma chord_norm {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 6/5) :
    Real.sqrt (18-18*Real.cos q)=6*Real.sin (q/2) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1]) (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hc : Real.cos q=1-2*Real.sin (q/2)^2 := by
    have h := Real.cos_two_mul (q/2)
    rw [show 2*(q/2)=q by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq (q/2)]
  rw [show 18-18*Real.cos q=(6*Real.sin (q/2))^2 by nlinarith only [hc],
    Real.sqrt_sq (by positivity)]

private lemma shifted_trig :
    (0.375:ℝ) ≤ Real.cos (Real.pi/4+2/5) ∧ (0.926:ℝ) ≤ Real.sin (Real.pi/4+2/5) ∧
    (0.926:ℝ) ≤ Real.cos (Real.pi/4-2/5) ∧ (0.375:ℝ) ≤ Real.sin (Real.pi/4-2/5) ∧
    (0.707:ℝ) ≤ Real.cos (Real.pi/4) ∧ (0.707:ℝ) ≤ Real.sin (Real.pi/4) := by
  obtain ⟨h1,h2,h3,h4,-⟩ := quarter_shift_bounds
  rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
  exact ⟨h1,h2,h3,h4,half_root_bounds.1,half_root_bounds.1⟩

/-- `cos x + sin x` at the two ends `x = 1/2 - 12/25` and `x = π/4 - 12/25` of
`d - 12/25`; at the second it exceeds its value `5/4` at `3/10`, as it increases
on `[0, π/4]`. -/
private lemma width_endpoints :
    (1.019:ℝ) ≤ Real.cos ((1:ℝ)/50)+Real.sin ((1:ℝ)/50) ∧
    (5/4:ℝ) ≤ Real.cos (Real.pi/4-12/25)+Real.sin (Real.pi/4-12/25) := by
  constructor
  · nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/50),
      Real.sin_ge_sub_cube (x := (1:ℝ)/50) (by norm_num)]
  · have hm := cos_add_sin_mono (x := 3/10) (y := Real.pi/4-12/25) (by norm_num)
      (by linarith [Real.pi_gt_d2]) (by linarith)
    nlinarith only [hm,Real.one_sub_sq_div_two_le_cos (x := (3:ℝ)/10),
      Real.sin_ge_sub_cube (x := (3:ℝ)/10) (by norm_num)]

/-! The six points `(westEnd i, diagonalEnd j)`, with decimal bounds for the
values there. -/

def westEnd : Fin 3 → ℝ := ![-2/5,0,2/5]
def diagonalEnd : Fin 2 → ℝ := ![1/2,Real.pi/4]
private def cosBound : Fin 3 → ℝ := ![0.921,1,0.921]
private def positiveSinBound : Fin 3 → ℝ := ![0,0,0.389]
private def westRootBound : Fin 3 → ℝ := ![3.958,5,5.862]
private def gapSinBound : Fin 3 → Fin 2 → ℝ :=
  ![![0.783,0.926],![0.479,0.707],![0.099,0.375]]
private def gapRootBound : Fin 3 → Fin 2 → ℝ :=
  ![![2.612,3.355],![1.488,2.297],![0.3,1.155]]
private def gapCosBound : Fin 3 → Fin 2 → ℝ :=
  ![![0.621,0.375],![0.877,0.707],![0.995,0.926]]
private def widthBound : Fin 2 → ℝ := ![1.019,5/4]

private lemma endpoint_bounds (i : Fin 3) (j : Fin 2) :
    cosBound i ≤ Real.cos (westEnd i) ∧
    positiveSinBound i ≤ max (Real.sin (westEnd i)) 0 ∧
    Real.sqrt (25+24*Real.sin (westEnd i)) ≤ westRootBound i ∧
    gapSinBound i j ≤ Real.sin (diagonalEnd j-westEnd i) ∧
    Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) ≤ gapRootBound i j ∧
    widthBound j ≤ Real.cos (diagonalEnd j-12/25)+Real.sin (diagonalEnd j-12/25) := by
  obtain ⟨hc4,hs4,hs4u⟩ := trig_two_fifths
  obtain ⟨hc5,-,hs5,-⟩ := trig_bracket_half
  obtain ⟨hc9,hs9⟩ := trig_nine_tenths
  obtain ⟨hc1,hs1⟩ := trig_tenth
  obtain ⟨hqcp,hqsp,hqcm,hqsm,hcq,hsq⟩ := shifted_trig
  have hcos : gapCosBound i j ≤ Real.cos (diagonalEnd j-westEnd i) := by
    fin_cases i <;> fin_cases j <;>
      norm_num [gapCosBound,diagonalEnd,westEnd] at * <;> linarith
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · fin_cases i <;> norm_num [cosBound,westEnd] <;> linarith
  · fin_cases i
    · exact le_max_right _ _
    · simp [positiveSinBound,westEnd]
    · simpa [positiveSinBound,westEnd] using hs4.trans (le_max_left _ _)
  · refine Real.sqrt_le_iff.mpr ⟨?_,?_⟩
    · fin_cases i <;> norm_num [westRootBound]
    · fin_cases i <;> norm_num [westEnd,westRootBound] at * <;> nlinarith
  · fin_cases i <;> fin_cases j <;>
      norm_num [gapSinBound,diagonalEnd,westEnd] at * <;> linarith
  · refine Real.sqrt_le_iff.mpr ⟨?_,?_⟩
    · fin_cases i <;> fin_cases j <;> norm_num [gapRootBound]
    · fin_cases i <;> fin_cases j <;>
        norm_num [gapCosBound,gapRootBound] at * <;> nlinarith only [hcos]
  · have hh := width_endpoints
    fin_cases j <;> norm_num [diagonalEnd,widthBound] at * <;> linarith

/-- The gap at a point with the bounds of the tables, `coreUpper` for `c0` and
`radiusBound` for `R0`. -/
private def reserve (i : Fin 3) (j : Fin 2) : ℝ :=
  8-4*coreUpper-3*radiusBound+4*cosBound i+4*positiveSinBound i-
    radiusBound*westRootBound i+3*gapSinBound i j-
    radiusBound*gapRootBound i j+3*widthBound j

private lemma reserve_positive (i : Fin 3) (j : Fin 2) : 0 < reserve i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [reserve,cosBound,positiveSinBound,westRootBound,gapSinBound,gapRootBound,widthBound,
      radiusBound,coreUpper]

lemma endpoint_positive (i : Fin 3) (j : Fin 2) : 0 < gap (westEnd i) (diagonalEnd j) := by
  obtain ⟨hc,hs,hrW,hq,hrD,hwidth⟩ := endpoint_bounds i j
  have hw : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 2/5 := by
    fin_cases i <;> norm_num [westEnd]
  have hd : 1/2 ≤ diagonalEnd j ∧ diagonalEnd j ≤ Real.pi/4 := by
    fin_cases j <;> norm_num [diagonalEnd] <;> linarith [Real.pi_gt_d2]
  have hroot := chord_norm (offset hw hd)
  have hmul := mul_le_mul_of_nonneg_left
    (show 3+Real.sqrt (25+24*Real.sin (westEnd i))+
      Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) ≤
      3+westRootBound i+gapRootBound i j by linarith) R0_nonneg
  have hr := mul_le_mul_of_nonneg_right ceiling_bounds.1
    (show 0 ≤ 3+westRootBound i+gapRootBound i j by
      fin_cases i <;> fin_cases j <;> norm_num [westRootBound,gapRootBound])
  have hC := ceiling_bounds.2.2.2
  have hp := reserve_positive i j
  dsimp [reserve] at hp
  have hroot' : 6*R0*Real.sin ((diagonalEnd j-westEnd i)/2)=
      R0*Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) := by
    rw [hroot]
    ring
  dsimp [gap,westTerm,southTerm,chordTerm,widthTerm]
  rw [Real.cos_neg,Real.sin_neg,neg_neg,mul_neg,sub_neg_eq_add]
  linarith only [hc,hs,hq,hwidth,hmul,hr,hC,hp,hroot']

/-- `gap w d` is positive on `[-2/5, 2/5] × [1/2, π/4]`. -/
theorem positive {w d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 < gap w d := by
  have he (i : Fin 3) : 0 < gap (westEnd i) d := by
    have hwi : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 2/5 := by
      fin_cases i <;> norm_num [westEnd]
    exact concave_gt_of_endpoints (gap_diagonal_concave hwi) hd
      (endpoint_positive i 0) (endpoint_positive i 1)
  have h0 : 0 < gap (-(2/5)) d := by
    have h := he 0
    rwa [show westEnd 0 = -(2/5) by norm_num [westEnd]] at h
  by_cases hw0 : w ≤ 0
  · exact concave_gt_of_endpoints (f := fun w => gap w d)
      (gap_west_concave hd le_rfl (by norm_num) westTerm_negative_concave)
      ⟨hw.1,hw0⟩ h0 (he 1)
  · exact concave_gt_of_endpoints (f := fun w => gap w d)
      (gap_west_concave hd (by norm_num) le_rfl westTerm_positive_concave)
      ⟨le_of_not_ge hw0,hw.2⟩ (he 1) (he 2)

/-- For `s ≤ 12/25` and a phase gap `π/2 + s - d ≥ π/4`, the term
`cos (d-s) + sin (d-s)` is at least its value at `s = 12/25`. -/
lemma south_width_lower {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hs : s ≤ 12/25)
    (hgap : Real.pi/4 ≤ Real.pi/2+s-d) :
    Real.cos (d-12/25)+Real.sin (d-12/25) ≤
      Real.cos (d-s)+Real.sin (d-s) := by
  apply cos_add_sin_mono
  · linarith [hd.1]
  · linarith
  · linarith

/-- With W separated from C along the west side of C, a missing south wing has
`s > 12/25`: with the weights `4`, `3`, `3` on C–W, W–D and D–S, the far-vertex
supports of W, D and S and the box of C leave at least `gap (-v) d`. -/
theorem impossible {X : Wings.Chart} (hW : X.WestSide) (h : X.MissingSouth)
    (hv : |X.v| ≤ 2/5) (hd : 1/2 ≤ X.d ∧ X.d ≤ Real.pi/4) (hs : X.s ≤ 12/25)
    (hr : X.d-X.s ≤ Real.pi/4) : False := by
  obtain ⟨hWD,hDS⟩ := h
  simp only [Wings.Chart.WestSide,Wings.Chart.WestWing,Wings.Chart.SouthDiagonal] at hW hWD hDS
  obtain ⟨hv1,hv2⟩ := abs_le.mp hv
  have hq : 0 ≤ X.d+X.v ∧ X.d+X.v ≤ 6/5 := by
    constructor <;> linarith [Real.pi_lt_d2]
  rw [angularWidth,abs_of_nonneg (by linarith [cos_small ⟨hv1,hv2⟩] : 0 ≤ Real.cos X.v)] at hW
  rw [angularWidth_eq (x := X.d+X.v) ⟨hq.1,by linarith [Real.pi_gt_d2]⟩] at hWD
  rw [angularWidth_eq (x := X.d-X.s) ⟨by linarith [Real.pi_lt_d2],by linarith [Real.pi_gt_d2]⟩]
    at hDS
  have hWs := local_vertex_support X.west (4*Real.cos X.v) (4*Real.sin X.v-3)
  have hDs := local_vertex_support X.diagonal
    (3*Real.sin (X.d+X.v)) (3*Real.cos (X.d+X.v)-3)
  have hSs := local_vertex_support X.south
    (3*Real.cos (X.d-X.s)) (3*Real.sin (X.d-X.s))
  rw [show (4*Real.cos X.v)^2+(4*Real.sin X.v-3)^2=25-24*Real.sin X.v by
    linear_combination 16*Real.sin_sq_add_cos_sq X.v] at hWs
  rw [show (3*Real.sin (X.d+X.v))^2+(3*Real.cos (X.d+X.v)-3)^2=18-18*Real.cos (X.d+X.v) by
    linear_combination 9*Real.sin_sq_add_cos_sq (X.d+X.v),chord_norm hq] at hDs
  rw [show (3*Real.cos (X.d-X.s))^2+(3*Real.sin (X.d-X.s))^2=3^2 by
    linear_combination 9*Real.sin_sq_add_cos_sq (X.d-X.s),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at hSs
  have hwW := add_le_add (le_abs_self (4*Real.cos X.v)) (neg_le_abs (4*Real.sin X.v-3))
  have hwD := add_le_add (le_abs_self (3*Real.sin (X.d+X.v)))
    (neg_le_abs (3*Real.cos (X.d+X.v)-3))
  have hwS := add_le_add (le_abs_self (3*Real.cos (X.d-X.s))) (le_abs_self (3*Real.sin (X.d-X.s)))
  have hcx := mul_le_mul_of_nonneg_left X.box.1.2 (by norm_num : (0:ℝ) ≤ 4)
  have hwidth := south_width_lower hd hs (by linarith)
  have hpos := positive (w := -X.v) (d := X.d) ⟨by linarith,by linarith⟩ hd
  have hmax : |Real.sin X.v|-Real.sin X.v=2*max (-Real.sin X.v) 0 := by
    rcases le_total 0 (Real.sin X.v) with h0 | h0
    · rw [abs_of_nonneg h0,max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h0,max_eq_left (by linarith)]; ring
  simp only [gap,westTerm,southTerm,chordTerm,widthTerm,neg_neg,
    sub_neg_eq_add] at hpos
  nlinarith only [hW,hWD,hDS,hWs,hDs,hSs,hwW,hwD,hwS,hcx,hwidth,hpos,hmax]

end SmallSouth

/-! ### A missing south wing with S on its own axis and `s ≥ 12/25` -/

namespace LargeSouth

/-! On each side of `v = 0` the angle `v` lies in `[vLower, vUpper]`, and the
profile has the coefficient `coefficient` of `sin v`: the far-vertex support of
W contributes `(12/5) R̄ sin v`, and the threshold of C–W with the half-sum of
the components of the force on W contributes `2 (|sin v| - sin v)`. -/

def vLower (negative : Bool) : ℝ := if negative then -(2/5) else 0
def vUpper (negative : Bool) : ℝ := if negative then 0 else 2/5
def coefficient (negative : Bool) : ℝ :=
  if negative then (12/5)*radiusBound-4 else (12/5)*radiusBound

/-- A lower bound for the defect (`profile_le_defect`): the defect with `c0`
replaced by `coreUpper` and `|sin (d - s)|` by `sin (d - s)`. -/
def profile (negative : Bool) (v s d : ℝ) : ℝ :=
  13-5*radiusBound-10*rhoBound+(5-10*coreUpper)*Real.cos s+5*Real.sin s+
    4*Real.cos v+coefficient negative*Real.sin v+
    3*Real.sin (d+v)-6*radiusBound*Real.sin ((d+v)/2)-
    (3*rhoBound-3/2)*Real.cos (d-s)+(3/2)*Real.sin (d-s)

lemma v_bounds {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    -(2/5) ≤ v ∧ v ≤ 2/5 := by
  cases negative <;> simp only [vLower,vUpper,Bool.false_eq_true,ite_true,ite_false] at hv <;>
    constructor <;> linarith [hv.1,hv.2]

private lemma q_bounds {v d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ d+v ∧ d+v ≤ 6/5 := by
  constructor <;> linarith [hv.1,hv.2,hd.1,hd.2]

private lemma coefficient_sine_lower {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    -(1/10) ≤ coefficient negative*Real.sin v := by
  cases negative
  · simp only [vLower,vUpper,Bool.false_eq_true,ite_false] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
      (by linarith [hv.2,Real.pi_gt_d2])
    dsimp [coefficient,radiusBound]
    linarith
  · simp only [vLower,vUpper,ite_true] at hv
    have hs := Real.sin_le (show 0 ≤ -v by linarith [hv.2])
    rw [Real.sin_neg] at hs
    dsimp [coefficient,radiusBound]
    linarith [hv.1]

/-- The derivative of the profile in `d` is nonpositive: `3 cos q - 3 R̄ cos (q/2)`
is at most `3 - 3 R̄`, and `sin (d - s) ≤ 11/14 - 12/25`. -/
lemma diagonal_derivative_nonpositive {v s d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    3*Real.cos (d+v)-3*radiusBound*Real.cos ((d+v)/2)+
      (3*rhoBound-3/2)*Real.sin (d-s)+(3/2)*Real.cos (d-s) ≤ 0 := by
  have hq := q_bounds hv hd
  have hc0 : 0 ≤ Real.cos ((d+v)/2) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,Real.pi_gt_d2]⟩
  have hid : Real.cos (d+v)=2*Real.cos ((d+v)/2)^2-1 := by
    have h := Real.cos_two_mul ((d+v)/2)
    rw [show 2*((d+v)/2)=d+v by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq ((d+v)/2)]
  have hp := mul_nonpos_of_nonpos_of_nonneg
    (show Real.cos ((d+v)/2)-1 ≤ 0 by linarith [Real.cos_le_one ((d+v)/2)])
    (show 0 ≤ 6*(Real.cos ((d+v)/2)+1)-3*radiusBound by norm_num [radiusBound]; linarith)
  have hchord : 3*Real.cos (d+v)-3*radiusBound*Real.cos ((d+v)/2) ≤ 3-3*radiusBound := by
    nlinarith only [hid,hp]
  have hrhi : d-s ≤ 11/14-12/25 := by linarith [hd.2,hs.1]
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d-s by linarith [Real.pi_gt_d2])
    (show (11/14-12/25:ℝ) ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hrhi
  have hsin : Real.sin (d-s) ≤ 11/14-12/25 :=
    hmono.trans (Real.sin_le (by norm_num))
  have hr := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 3*rhoBound-3/2 by norm_num [rhoBound])
  have hR : 3-3*radiusBound+(3*rhoBound-3/2)*(11/14-12/25)+3/2 ≤ 0 := by
    norm_num [radiusBound,rhoBound]
  linarith [Real.cos_le_one (d-s)]

lemma profile_at_upper_diagonal {negative : Bool} {v s d : ℝ}
    (hv : -(2/5) ≤ v ∧ v ≤ 2/5)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    profile negative v s (11/14) ≤ profile negative v s d := by
  let D : ℝ → ℝ := fun x =>
    3*Real.cos (x+v)-3*radiusBound*Real.cos ((x+v)/2)+
      (3*rhoBound-3/2)*Real.sin (x-s)+(3/2)*Real.cos (x-s)
  have hf (x : ℝ) : HasDerivAt (profile negative v s) (D x) x := by
    let K := 13-5*radiusBound-10*rhoBound+(5-10*coreUpper)*Real.cos s+5*Real.sin s+
      4*Real.cos v+coefficient negative*Real.sin v
    have h := (((((((hasDerivAt_id' x).add_const v).sin).const_mul 3).fun_sub
      (((((hasDerivAt_id' x).add_const v).div_const 2).sin).const_mul (6*radiusBound))).fun_sub
      ((((hasDerivAt_id' x).sub_const s).cos).const_mul (3*rhoBound-3/2))).fun_add
      ((((hasDerivAt_id' x).sub_const s).sin).const_mul (3/2))).const_add K
    convert h using 1
    · funext y
      simp only [profile,K]
      ring
    · simp only [D]
      ring
  have hmono : MonotoneOn (fun x => -profile negative v s x) (Set.Icc (1/2) (11/14)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (hf x).fun_neg.continuousAt.continuousWithinAt)
      (fun x _ => (hf x).fun_neg)
    intro x hx
    exact neg_nonneg.mpr (diagonal_derivative_nonpositive hv hs ⟨hx.1.le,hx.2.le⟩)
  have h := hmono hd (by norm_num : (11:ℝ)/14 ∈ Set.Icc (1/2) (11/14)) hd.2
  linarith

lemma profile_v_concave (negative : Bool) {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc (vLower negative) (vUpper negative))
      (fun v => profile negative v s d) := by
  let f' : ℝ → ℝ := fun v => -4*Real.sin v+coefficient negative*Real.cos v+
    3*Real.cos (d+v)-3*radiusBound*Real.cos ((d+v)/2)
  let f'' : ℝ → ℝ := fun v => -4*Real.cos v-coefficient negative*Real.sin v-
    3*Real.sin (d+v)+(3/2)*radiusBound*Real.sin ((d+v)/2)
  have hf (v : ℝ) : HasDerivAt (fun x => profile negative x s d) (f' v) v := by
    let K := 13-5*radiusBound-10*rhoBound+(5-10*coreUpper)*Real.cos s+5*Real.sin s-
      (3*rhoBound-3/2)*Real.cos (d-s)+(3/2)*Real.sin (d-s)
    have h := (((((Real.hasDerivAt_cos v).const_mul 4).fun_add
      ((Real.hasDerivAt_sin v).const_mul (coefficient negative))).fun_add
      ((((hasDerivAt_id' v).const_add d).sin).const_mul 3)).fun_sub
      (((((hasDerivAt_id' v).const_add d).div_const 2).sin).const_mul (6*radiusBound))).const_add K
    convert h using 1
    · funext y
      simp only [profile,K]
      ring
    · simp only [f']
      ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    exact (((((Real.hasDerivAt_sin v).const_mul (-4)).fun_add
      ((Real.hasDerivAt_cos v).const_mul (coefficient negative))).fun_add
      ((((hasDerivAt_id' v).const_add d).cos).const_mul 3)).fun_sub
      (((((hasDerivAt_id' v).const_add d).div_const 2).cos).const_mul (3*radiusBound))).congr_deriv
      (by simp only [f'']; ring)
  refine concave_of_deriv2 (fun x _ => hf x) (fun x _ => hff x) fun v hmem => ?_
  have hraw := v_bounds hmem
  have hc := cos_small hraw
  have hq := q_bounds hraw hd
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hq.1
    (by linarith [hq.2,Real.pi_gt_d2])
  have hb := coefficient_sine_lower hmem
  have hR : (3/2)*radiusBound*Real.sin ((d+v)/2) ≤ 3 := by
    norm_num [radiusBound]; linarith [Real.sin_le_one ((d+v)/2)]
  dsimp [f'']
  linarith

private lemma extend_s {negative : Bool} {v s d : ℝ}
    (hs : 12/25 ≤ s ∧ s ≤ 2/3)
    (hleft : 0 < profile negative v (12/25) d)
    (hright : 0 < profile negative v (2/3) d) :
    0 < profile negative v s d := by
  let A := 5-10*coreUpper-(3*rhoBound-3/2)*Real.cos d+(3/2)*Real.sin d
  let B := 5-(3*rhoBound-3/2)*Real.sin d-(3/2)*Real.cos d
  let K := 13-5*radiusBound-10*rhoBound+4*Real.cos v+coefficient negative*Real.sin v+
    3*Real.sin (d+v)-6*radiusBound*Real.sin ((d+v)/2)
  have hid (x : ℝ) : profile negative v x d=K+A*Real.cos x+B*Real.sin x := by
    dsimp [profile,K,A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hA : 0 ≤ A := by
    dsimp [A,coreUpper,rhoBound]
    linarith [Real.cos_le_one d,Real.neg_one_le_sin d]
  have hB : 0 ≤ B := by
    dsimp [B,rhoBound]
    linarith [Real.sin_le_one d,Real.cos_le_one d]
  rw [hid] at hleft hright ⊢
  exact harmonic_pos_of_endpoints hA hB (by norm_num) (by linarith [Real.pi_gt_d2]) hs hleft hright

private def endpointPolynomial (negative : Bool) (v s : ℝ) : ℝ :=
  13-5*radiusBound-10*rhoBound+(5-10*coreUpper)*cosLower s+5*sinBelow s+
    4*cosLower v+coefficient negative*sinBelow v+
    3*sinBelow (11/14+v)-6*radiusBound*sinUpper ((11/14+v)/2)-
    (3*rhoBound-3/2)*cosUpper (11/14-s)+(3/2)*sinBelow (11/14-s)

private lemma endpointPolynomial_le {negative : Bool} {v s : ℝ} (hq : 0 ≤ 11/14+v) :
    endpointPolynomial negative v s ≤ profile negative v s (11/14) := by
  have cs := cosLower_le s
  have ss := sinBelow_le s
  have cv := cosLower_le v
  have sv := sinBelow_le v
  have sq := sinBelow_le (11/14+v)
  have sh := le_sinUpper (x := (11/14+v)/2) (by linarith)
  have cr := le_cosUpper (11/14-s)
  have sr := sinBelow_le (11/14-s)
  cases negative <;>
    dsimp [endpointPolynomial,profile,coefficient,radiusBound,rhoBound,coreUpper] <;>
    nlinarith only [cs,ss,cv,sv,sq,sh,cr,sr]

/-- The profile is positive at the corners of the domain with `d = 11/14`. -/
private lemma corner (negative : Bool) (v s : ℝ)
    (hv : v=vLower negative ∨ v=vUpper negative)
    (hs : s=12/25 ∨ s=2/3) : 0 < profile negative v s (11/14) := by
  rcases hv with rfl | rfl <;> rcases hs with rfl | rfl <;> cases negative
  all_goals
    apply lt_of_lt_of_le _ (endpointPolynomial_le (by norm_num [vLower,vUpper]))
    norm_num [endpointPolynomial,coefficient,vLower,vUpper,cosLower,cosUpper,sinBelow,
      sinLower,sinUpper,radiusBound,rhoBound,coreUpper]

/-- The profile is positive on its domain. -/
theorem positive (negative : Bool) {v s d : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 < profile negative v s d := by
  have hside (x : ℝ) (hx : x=12/25 ∨ x=2/3) :
      0 < profile negative v x (11/14) := by
    apply concave_gt_of_endpoints
      (profile_v_concave negative (s := x) (d := 11/14) ⟨by norm_num,le_rfl⟩) hv
    · exact corner negative (vLower negative) x (Or.inl rfl) hx
    · exact corner negative (vUpper negative) x (Or.inr rfl) hx
  have htop := extend_s hs (hside (12/25) (Or.inl rfl)) (hside (2/3) (Or.inr rfl))
  exact htop.trans_le (profile_at_upper_diagonal (v_bounds hv) hs hd)

/-! The `defect` is the threshold sum less the far-vertex bounds `westUpper` and
`diagonalUpper` for the works on W and D, the cone bound
`rhoBound (10 + 3 cos (d - s))` on S and `10 c0 cos s` on C. -/

def westUpper (v : ℝ) : ℝ :=
  radiusBound*(5-(12/5)*Real.sin v)-(4*Real.cos v+3-4*Real.sin v)/2

def diagonalUpper (q : ℝ) : ℝ :=
  6*radiusBound*Real.sin (q/2)-(3*Real.sin q+3-3*Real.cos q)/2

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) (v : ℝ) :
    4*Real.cos v*a+(4*Real.sin v-3)*b ≤ westUpper v := by
  have h := vertex_support hc (U := 4*Real.cos v) (V := 4*Real.sin v-3)
    (r := 5-(12/5)*Real.sin v) (by linarith [Real.sin_le_one v])
    (by nlinarith [Real.sin_sq_add_cos_sq v,sq_nonneg (Real.sin v)])
  dsimp [westUpper]
  linarith [le_abs_self (4*Real.cos v),neg_le_abs (4*Real.sin v-3)]

lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 0 ≤ q ∧ q ≤ 6/5) :
    3*Real.sin q*a+(3*Real.cos q-3)*b ≤ diagonalUpper q := by
  have hs := (cos_sin_nonneg (x := q/2) ⟨by linarith [hq.1],by linarith [hq.2,Real.pi_gt_d2]⟩).2
  have hhalf := Real.cos_sq (q/2)
  rw [show 2*(q/2)=q by ring] at hhalf
  have h := vertex_support hc (U := 3*Real.sin q) (V := 3*Real.cos q-3)
    (r := 6*Real.sin (q/2)) (by linarith)
    (le_of_eq (by linear_combination 9*Real.sin_sq_add_cos_sq q-
      36*Real.sin_sq_add_cos_sq (q/2)+36*hhalf))
  dsimp [diagonalUpper]
  linarith [le_abs_self (3*Real.sin q),neg_le_abs (3*Real.cos q-3)]

/-- The force on S lies in the axial cone. -/
lemma south_support {a b r : ℝ} (hc : ContainedChart a |b|)
    (hr : 0 ≤ Real.cos r) :
    (10+3*Real.cos r)*a+3*Real.sin r*b ≤
      rhoBound*(10+3*Real.cos r) :=
  cone_support hc (by linarith)
    ((show |3*Real.sin r| ≤ 3 from abs_le.mpr ⟨by linarith [Real.neg_one_le_sin r],
      by linarith [Real.sin_le_one r]⟩).trans (by linarith))

lemma south_trig {s : ℝ} (hs : 12/25 ≤ s ∧ s ≤ 2/3) :
    0 ≤ Real.cos s ∧ 2/5 ≤ Real.sin s := by
  obtain ⟨hl,-,hc,-⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_d2]) hs
  norm_num at hl hc
  exact ⟨by linarith,by linarith⟩

lemma central_support {s cx cy : ℝ} (hs : 12/25 ≤ s ∧ s ≤ 2/3)
    (hx : 0 ≤ cx) (hy : cy ≤ c0) :
    (4-10*Real.sin s)*cx+10*Real.cos s*cy ≤ 10*c0*Real.cos s := by
  have ht := south_trig hs
  have hX := mul_nonpos_of_nonpos_of_nonneg (show 4-10*Real.sin s ≤ 0 by linarith) hx
  have hY := mul_nonneg (sub_nonneg.mpr hy) ht.1
  nlinarith only [hX,hY]

def totalThreshold (v s d : ℝ) : ℝ :=
  4*(1/2+angularWidth v)+10*(1/2+angularWidth s)+
    3*(1/2+angularWidth (d+v))+3*(1/2+angularWidth (d-s))

def defect (v s d : ℝ) : ℝ :=
  totalThreshold v s d-westUpper v-diagonalUpper (d+v)-
    rhoBound*(10+3*Real.cos (d-s))-10*c0*Real.cos s

private lemma sine_term_lower {negative : Bool} {v : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) :
    coefficient negative*Real.sin v ≤
      2*(|Real.sin v|-Real.sin v)+(12/5)*radiusBound*Real.sin v := by
  cases negative
  · simp only [vLower,vUpper,Bool.false_eq_true,ite_false] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
      (by linarith [hv.2,Real.pi_gt_d2])
    rw [abs_of_nonneg hs]
    dsimp [coefficient]
    linarith
  · simp only [vLower,vUpper,ite_true] at hv
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ -v by linarith [hv.2])
      (show -v ≤ Real.pi by linarith [hv.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at hs
    rw [abs_of_nonpos (by linarith : Real.sin v ≤ 0)]
    dsimp [coefficient]
    linarith

/-- The profile is a lower bound for the defect on its domain. -/
lemma profile_le_defect (negative : Bool) {v s d : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    profile negative v s d ≤ defect v s d := by
  have hraw := v_bounds hv
  have hq : 0 ≤ d+v ∧ d+v ≤ Real.pi/2 := by
    constructor <;> linarith [hraw.1,hraw.2,hd.1,hd.2,Real.pi_gt_d2]
  have hC := mul_le_mul_of_nonneg_right ceiling_bounds.2.2.2 (south_trig hs).1
  have hV := sine_term_lower hv
  have hW : angularWidth v=(Real.cos v+|Real.sin v|)/2 := by
    rw [angularWidth,abs_of_nonneg (by linarith [cos_small hraw] : 0 ≤ Real.cos v)]
  dsimp [profile,defect,totalThreshold,westUpper,diagonalUpper]
  rw [hW,angularWidth_eq (x := s) ⟨by linarith [hs.1],by linarith [hs.2,Real.pi_gt_d2]⟩,
    angularWidth_eq hq]
  linarith [angularWidth_lower (d-s),hC,hV]

/-- With W separated from C along the west side of C and S along its own axis at
an angle `s ≥ 12/25`, the separations of a missing south wing are
incompatible: the weights `4`, `10`, `3`, `3` on C–W, C–S, W–D and D–S leave a
defect above the positive profile. -/
theorem impossible {X : Wings.Chart} (hW : X.WestSide) (hS : X.SouthOwn)
    (h : X.MissingSouth) (hv : |X.v| ≤ 2/5) (hs : 12/25 ≤ X.s ∧ X.s ≤ 2/3)
    (hd : 1/2 ≤ X.d ∧ X.d ≤ 11/14) : False := by
  have hWD := h.west
  have hDS := h.south
  simp only [Wings.Chart.WestSide,Wings.Chart.SouthOwn,Wings.Chart.WestWing,
    Wings.Chart.SouthDiagonal] at hW hS hWD hDS
  have hsum : totalThreshold X.v X.s X.d ≤
      (4*Real.cos X.v*X.aW+(4*Real.sin X.v-3)*X.bW)+
      (3*Real.sin (X.d+X.v)*X.aD+(3*Real.cos (X.d+X.v)-3)*X.bD)+
      ((10+3*Real.cos (X.d-X.s))*X.aS+3*Real.sin (X.d-X.s)*X.bS)+
      ((4-10*Real.sin X.s)*X.cx+10*Real.cos X.s*X.cy) := by
    dsimp [totalThreshold]
    linear_combination 4*hW+10*hS+3*hWD+3*hDS
  have hq : 0 ≤ X.d+X.v ∧ X.d+X.v ≤ 6/5 := by
    constructor <;> linarith [(abs_le.mp hv).1,(abs_le.mp hv).2]
  have hcr := Real.cos_nonneg_of_mem_Icc
    (show X.d-X.s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_gt_d2])
  have hnonpos : defect X.v X.s X.d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,west_support X.west X.v,diagonal_support X.diagonal hq,
      south_support X.south hcr,central_support hs X.box.1.1 X.box.2.2]
  have finish (negative : Bool) (hv : vLower negative ≤ X.v ∧ X.v ≤ vUpper negative) :
      False := by
    have hp := (positive negative hv hs hd).trans_le (profile_le_defect negative hv hs hd)
    linarith
  rcases le_total 0 X.v with h0 | h0
  · exact finish false (by simpa [vLower,vUpper] using And.intro h0 (abs_le.mp hv).2)
  · exact finish true (by simpa [vLower,vUpper] using And.intro (abs_le.mp hv).1 h0)

end LargeSouth

end SquaresInCircles.Six.Wings.WestSide
