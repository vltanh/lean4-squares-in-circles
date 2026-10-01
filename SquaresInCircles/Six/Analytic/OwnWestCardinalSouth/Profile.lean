import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.SouthAngle

/-!
# Own W, cardinal S: the profile

Give the edges C–W, C–S, C–D, W–D and D–S the weights `2, 1, 3/10, 1, 1`.
Once the angle of S is eliminated, the weighted sum leaves a `profile` in the
angle `v` of W and the angle `d` of D. It comes in two versions, for the two
ends `0` and `5641/50000` of the range of the second coordinate of the centre
of C. Both are concave in each variable on `0 ≤ v ≤ 2/3`, `1/2 ≤ d ≤ 11/14`.
The chord term of the edge W–D has second derivative at most `-3/25` on
`1/2 ≤ q ≤ 3/2`, by comparison of coefficients with the envelope of
`OwnSouthWestDominant.chordSecond`. In `v` the west term is a nonnegative
harmonic, whose second derivative is its negative; in `d` the half-angle terms
are absorbed by `sin (d/2) ≥ 95/384`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth

def westWeight : ℝ := 2
def diagonalWeight : ℝ := 3/10
def centerY (upper : Bool) : ℝ := if upper then 5641/50000 else 0

def wingCos : ℝ := 19359/50000

def chordSin : ℝ := 6830387/2000000
def chordCos : ℝ := 25329/50000

def chord (q : ℝ) : ℝ :=
  Real.sin q-chordSin*Real.sin (q/2)-chordCos*Real.cos (q/2)
def chordFirst (q : ℝ) : ℝ :=
  Real.cos q-(chordSin/2)*Real.cos (q/2)+(chordCos/2)*Real.sin (q/2)
def chordSecond (q : ℝ) : ℝ :=
  -Real.sin q+(chordSin/4)*Real.sin (q/2)+(chordCos/4)*Real.cos (q/2)

def westTerm (upper : Bool) (v : ℝ) : ℝ :=
  westWeight*(wingCos*Real.cos v+(1/2+centerY upper)*Real.sin v)
def diagonalTerm (upper : Bool) (d : ℝ) : ℝ :=
  diagonalWeight*(wingCos*Real.cos d+(1/2-centerY upper)*Real.sin d)
def westFirst (upper : Bool) (v : ℝ) : ℝ :=
  westWeight*(-wingCos*Real.sin v+(1/2+centerY upper)*Real.cos v)
def diagonalFirst (upper : Bool) (d : ℝ) : ℝ :=
  diagonalWeight*(-wingCos*Real.sin d+(1/2-centerY upper)*Real.cos d)

def constantTerm (upper : Bool) : ℝ := 63759707/62500000-centerY upper

def profile (upper : Bool) (v d : ℝ) : ℝ :=
  constantTerm upper+westTerm upper v+diagonalTerm upper d+chord (d+v)+halfLinear d

lemma chord_hasDeriv (q : ℝ) : HasDerivAt chord (chordFirst q) q := by
  convert (((Real.hasDerivAt_sin q).sub
    ((((hasDerivAt_id q).div_const 2).sin).const_mul chordSin)).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul chordCos)) using 1 <;>
    (try funext x) <;> dsimp [chord,chordFirst]
  ring

lemma chord_first_hasDeriv (q : ℝ) : HasDerivAt chordFirst (chordSecond q) q := by
  convert (((Real.hasDerivAt_cos q).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul (chordSin/2))).add
    ((((hasDerivAt_id q).div_const 2).sin).const_mul (chordCos/2))) using 1 <;>
    (try funext x) <;> dsimp [chordFirst,chordSecond]
  ring

/-- `chordSecond q ≤ -3/25` on `[1/2, 3/2]`: it lies `9/200` below the
envelope of `OwnSouthWestDominant.chordSecond`. -/
lemma chord_second_upper {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 3/2) :
    chordSecond q ≤ -(3/25) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hsq := mul_nonneg
    (show 0 ≤ 3/4-q/2 by linarith [hq.2])
    (show 0 ≤ 3/4+q/2 by linarith [hq.1])
  have hc : 23/32 ≤ Real.cos (q/2) := by
    nlinarith only [hsq,Real.one_sub_sq_div_two_le_cos (x := q/2)]
  have hcompare : chordSecond q ≤ OwnSouthWestDominant.chordSecond q-9/200 := by
    dsimp [chordSecond,chordSin,chordCos,
      OwnSouthWestDominant.chordSecond,OwnSouthWestDominant.chordSin,OwnSouthWestDominant.chordCos]
    nlinarith only [hs,hc]
  have hold := OwnSouthWestDominant.chord_second_envelope hq
  have hm : (1:ℝ)/2 ≤ min q 1 := le_min hq.1 (by norm_num)
  linarith

lemma west_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westTerm upper) (westFirst upper v) v := by
  convert (((Real.hasDerivAt_cos v).const_mul wingCos).add
    ((Real.hasDerivAt_sin v).const_mul (1/2+centerY upper))).const_mul westWeight using 1 <;>
    (try funext x) <;> dsimp [westTerm,westFirst]
  ring

lemma west_first_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westFirst upper) (-westTerm upper v) v := by
  convert (((Real.hasDerivAt_sin v).const_mul (-wingCos)).add
    ((Real.hasDerivAt_cos v).const_mul (1/2+centerY upper))).const_mul westWeight using 1 <;>
    (try funext x) <;> dsimp [westTerm,westFirst]
  ring

lemma diagonal_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalTerm upper) (diagonalFirst upper d) d := by
  convert (((Real.hasDerivAt_cos d).const_mul wingCos).add
    ((Real.hasDerivAt_sin d).const_mul (1/2-centerY upper))).const_mul diagonalWeight using 1 <;>
    (try funext x) <;> dsimp [diagonalTerm,diagonalFirst]
  ring

lemma diagonal_first_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalFirst upper) (-diagonalTerm upper d) d := by
  convert (((Real.hasDerivAt_sin d).const_mul (-wingCos)).add
    ((Real.hasDerivAt_cos d).const_mul (1/2-centerY upper))).const_mul diagonalWeight using 1 <;>
    (try funext x) <;> dsimp [diagonalTerm,diagonalFirst]
  ring

lemma half_linear_hasDeriv (d : ℝ) :
    HasDerivAt halfLinear (southB*Real.sin (d/2)+(1/2)*Real.cos (d/2)) d := by
  convert (((((hasDerivAt_id d).div_const 2).cos).const_mul (-2*southB)).add
    (((hasDerivAt_id d).div_const 2).sin)) using 1 <;> (try funext x) <;> dsimp [halfLinear]
  ring

lemma half_linear_first_hasDeriv (d : ℝ) :
    HasDerivAt (fun x => southB*Real.sin (x/2)+(1/2)*Real.cos (x/2))
      ((southB/2)*Real.cos (d/2)-(1/4)*Real.sin (d/2)) d := by
  convert (((((hasDerivAt_id d).div_const 2).sin).const_mul southB).add
    ((((hasDerivAt_id d).div_const 2).cos).const_mul (1/2))) using 1 <;> (try funext x) <;>
    dsimp
  ring

private lemma west_nonnegative (upper : Bool) {v : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) : 0 ≤ westTerm upper v := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  cases upper <;> dsimp [westTerm,westWeight,wingCos,centerY] <;> positivity

private lemma diagonal_lower (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    (3/10)*wingCos*(4/3) ≤ diagonalTerm upper d := by
  have h := OwnSouthWestDominant.diagonal_trig_lower hd
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ d by linarith [hd.1])
    (show d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
  cases upper <;> dsimp [diagonalTerm,diagonalWeight,wingCos,centerY] <;>
    nlinarith only [h,hs]

private lemma half_sine_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    95/384 ≤ Real.sin (d/2) := by
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/4 by linarith [Real.pi_pos])
    (show d/2 ≤ Real.pi/2 by linarith [hd.2,Real.pi_gt_d2])
    (show (1:ℝ)/4 ≤ d/2 by linarith [hd.1])
  have hl := Real.sin_ge_sub_cube (x := (1:ℝ)/4) (by norm_num)
  nlinarith only [hm,hl]

lemma profile_west_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun v => profile upper v d) := by
  let f' : ℝ → ℝ := fun v => westFirst upper v+chordFirst (d+v)
  let f'' : ℝ → ℝ := fun v => -westTerm upper v+chordSecond (d+v)
  have hf (v : ℝ) : HasDerivAt (fun x => profile upper x d) (f' v) v := by
    have hq := (chord_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert ((west_hasDeriv upper v).add hq).const_add
      (constantTerm upper+diagonalTerm upper d+halfLinear d) using 1 <;>
      (try funext x) <;> dsimp [profile,f'] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    have hq := (chord_first_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert (west_first_hasDeriv upper v).add hq using 1 <;> (try funext x) <;>
      dsimp [f',f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro v _; exact (hf v).hasDerivWithinAt
  · intro v _; exact (hff v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hq : 1/2 ≤ d+v ∧ d+v ≤ 3/2 := by
      constructor <;> linarith [hd.1,hd.2,h.1,h.2]
    dsimp [f'']
    linarith [west_nonnegative upper h,chord_second_upper hq]

lemma profile_diagonal_concave (upper : Bool) {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 2/3) :
    ConcaveOn ℝ (Set.Icc (1/2) (11/14)) (profile upper v) := by
  let f' : ℝ → ℝ := fun d => diagonalFirst upper d+chordFirst (d+v)+
    southB*Real.sin (d/2)+(1/2)*Real.cos (d/2)
  let f'' : ℝ → ℝ := fun d => -diagonalTerm upper d+chordSecond (d+v)+
    (southB/2)*Real.cos (d/2)-(1/4)*Real.sin (d/2)
  have hf (d : ℝ) : HasDerivAt (profile upper v) (f' d) d := by
    have hq := (chord_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    convert (((diagonal_hasDeriv upper d).add hq).add (half_linear_hasDeriv d)).const_add
      (constantTerm upper+westTerm upper v) using 1 <;> (try funext x) <;>
      dsimp [profile,f'] <;> ring
  have hff (d : ℝ) : HasDerivAt f' (f'' d) d := by
    have hq := (chord_first_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    convert ((diagonal_first_hasDeriv upper d).add hq).add (half_linear_first_hasDeriv d)
      using 1 <;> (try funext x) <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (11/14))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro d _; exact (hf d).hasDerivWithinAt
  · intro d _; exact (hff d).hasDerivWithinAt
  · intro d hd
    have h := interior_subset hd
    have hq : 1/2 ≤ d+v ∧ d+v ≤ 3/2 := by
      constructor <;> linarith [hv.1,hv.2,h.1,h.2]
    have hdiag := diagonal_lower upper h
    have hchord := chord_second_upper hq
    have hhalf := half_sine_lower h
    have hc := Real.cos_le_one (d/2)
    dsimp [f'',southB,wingCos] at *
    linarith

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
