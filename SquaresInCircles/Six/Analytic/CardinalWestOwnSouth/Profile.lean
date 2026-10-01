import SquaresInCircles.Six.Analytic.HighChordCurvature
import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Profile

/-!
# Cardinal W, own S: the profile

W is separated from the central square along its west side and S along its own
axis. The case is read in the reflection in the diagonal, which exchanges W and
S: `v` is the angle of the new W and `d ∈ [157/200, 34/35]` the new diagonal
angle. The weights on the separations C–W, C–S, C–D, W–D and D–S are
`2037/1000`, `1`, `391/1000`, `1` and `1`, and the weighted thresholds exceed
the support bounds by at least the profile, with the second central coordinate
at either end of `[0, 5641/50000]`. It is concave in `v` and in `d`, because the
chord term `sin q - L sin (q/2) - M cos (q/2)` has second derivative at most
`-19/100` on `[157/200, 5/3]`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalWestOwnSouth

def westWeight : ℝ := 2037/1000
def diagonalWeight : ℝ := 391/1000
def centerY (upper : Bool) : ℝ := if upper then 5641/50000 else 0

def wingCos : ℝ := 19359/50000
def southB : ℝ := 30641/50000

def chordSin : ℝ := 68834774283/20000000000
def chordCos : ℝ := 3301213/5000000

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

def constantTerm (upper : Bool) : ℝ := 137023941021/125000000000-centerY upper

def profile (upper : Bool) (v d : ℝ) : ℝ :=
  constantTerm upper+westTerm upper v+diagonalTerm upper d+chord (d+v)+
    OwnWestCardinalSouth.halfLinear d

lemma chord_hasDeriv (q : ℝ) : HasDerivAt chord (chordFirst q) q := by
  convert (((Real.hasDerivAt_sin q).sub
    ((((hasDerivAt_id q).div_const 2).sin).const_mul chordSin)).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul chordCos)) using 1 <;> (try funext y) <;>
    dsimp [chord,chordFirst]
  ring

lemma chord_first_hasDeriv (q : ℝ) : HasDerivAt chordFirst (chordSecond q) q := by
  convert (((Real.hasDerivAt_cos q).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul (chordSin/2))).add
    ((((hasDerivAt_id q).div_const 2).sin).const_mul (chordCos/2))) using 1 <;> (try funext y) <;>
    dsimp [chordFirst,chordSecond]
  ring

lemma chord_second_upper {q : ℝ} (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    chordSecond q ≤ -(19/100) := by
  exact HighChordCurvature.upper
    (L := chordSin) (M := chordCos)
    (by norm_num [chordSin]) (by norm_num [chordCos]) hq

lemma west_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westTerm upper) (westFirst upper v) v := by
  convert (((Real.hasDerivAt_cos v).const_mul wingCos).add
    ((Real.hasDerivAt_sin v).const_mul (1/2+centerY upper))).const_mul westWeight using 1 <;> (try funext y) <;>
    dsimp [westTerm,westFirst]
  ring

lemma west_first_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westFirst upper) (-westTerm upper v) v := by
  convert (((Real.hasDerivAt_sin v).const_mul (-wingCos)).add
    ((Real.hasDerivAt_cos v).const_mul (1/2+centerY upper))).const_mul westWeight using 1 <;> (try funext y) <;>
    dsimp [westTerm,westFirst]
  ring

lemma diagonal_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalTerm upper) (diagonalFirst upper d) d := by
  convert (((Real.hasDerivAt_cos d).const_mul wingCos).add
    ((Real.hasDerivAt_sin d).const_mul (1/2-centerY upper))).const_mul diagonalWeight using 1 <;> (try funext y) <;>
    dsimp [diagonalTerm,diagonalFirst]
  ring

lemma diagonal_first_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalFirst upper) (-diagonalTerm upper d) d := by
  convert (((Real.hasDerivAt_sin d).const_mul (-wingCos)).add
    ((Real.hasDerivAt_cos d).const_mul (1/2-centerY upper))).const_mul diagonalWeight using 1 <;> (try funext y) <;>
    dsimp [diagonalTerm,diagonalFirst]
  ring

private lemma diagonal_wave_lower {d : ℝ} (hd : 157/200 ≤ d ∧ d ≤ 34/35) :
    4/3 ≤ Real.cos d+Real.sin d := by
  have h := trig_lower_of_endpoints (A := 1) (B := 1) (C := 4/3)
    (l := 3/4) (u := 1) (t := d) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_d2])
    (show 3/4 ≤ d ∧ d ≤ 1 by constructor <;> linarith [hd.1,hd.2])
    (by nlinarith only [Seven.cos_lower_six (x := (3:ℝ)/4) (by norm_num),
      Seven.sin_lower_seven (x := (3:ℝ)/4) (by norm_num)])
    (by nlinarith only [Seven.cos_lower_six (x := (1:ℝ)) (by norm_num),
      Seven.sin_lower_seven (x := (1:ℝ)) (by norm_num)])
  simpa only [one_mul] using h.le

private lemma diagonal_lower (upper : Bool) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 34/35) :
    diagonalWeight*wingCos*(4/3) ≤ diagonalTerm upper d := by
  have h := diagonal_wave_lower hd
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ d by linarith [hd.1])
    (show d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
  cases upper <;> dsimp [diagonalTerm,diagonalWeight,wingCos,centerY] <;>
    nlinarith only [h,hs]

private lemma west_nonnegative (upper : Bool) {v : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) : 0 ≤ westTerm upper v := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  cases upper <;> dsimp [westTerm,westWeight,wingCos,centerY] <;> positivity

lemma profile_west_concave (upper : Bool) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 34/35) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun v => profile upper v d) := by
  let f' : ℝ → ℝ := fun v => westFirst upper v+chordFirst (d+v)
  let f'' : ℝ → ℝ := fun v => -westTerm upper v+chordSecond (d+v)
  have hf (v : ℝ) : HasDerivAt (fun x => profile upper x d) (f' v) v := by
    have hq := (chord_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert ((west_hasDeriv upper v).add hq).const_add
      (constantTerm upper+diagonalTerm upper d+OwnWestCardinalSouth.halfLinear d) using 1 <;> (try funext y) <;>
      dsimp [profile,f'] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    have hq := (chord_first_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert (west_first_hasDeriv upper v).add hq using 1 <;> (try funext y) <;> dsimp [f',f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
    (f' := f') (f'' := f'') (by dsimp [profile,westTerm,chord]; fun_prop)
  · intro v _; exact (hf v).hasDerivWithinAt
  · intro v _; exact (hff v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hq : 157/200 ≤ d+v ∧ d+v ≤ 5/3 := by
      constructor <;> linarith [hd.1,hd.2,h.1,h.2]
    dsimp [f'']
    linarith [west_nonnegative upper h,chord_second_upper hq]

lemma profile_diagonal_concave (upper : Bool) {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 2/3) :
    ConcaveOn ℝ (Set.Icc (157/200) (34/35)) (profile upper v) := by
  let f' : ℝ → ℝ := fun d => diagonalFirst upper d+chordFirst (d+v)+
    southB*Real.sin (d/2)+(1/2)*Real.cos (d/2)
  let f'' : ℝ → ℝ := fun d => -diagonalTerm upper d+chordSecond (d+v)+
    (southB/2)*Real.cos (d/2)-(1/4)*Real.sin (d/2)
  have hf (d : ℝ) : HasDerivAt (profile upper v) (f' d) d := by
    have hq := (chord_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    convert (((diagonal_hasDeriv upper d).add hq).add
      (OwnWestCardinalSouth.half_linear_hasDeriv d)).const_add
      (constantTerm upper+westTerm upper v) using 1 <;> (try funext y) <;>
      dsimp [profile,f',southB,OwnWestCardinalSouth.southB] <;> ring
  have hff (d : ℝ) : HasDerivAt f' (f'' d) d := by
    have hq := (chord_first_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    convert ((diagonal_first_hasDeriv upper d).add hq).add
      (OwnWestCardinalSouth.half_linear_first_hasDeriv d) using 1 <;> (try funext y) <;>
      dsimp [f',f'',southB,OwnWestCardinalSouth.southB] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (157/200) (34/35))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro d _; exact (hf d).hasDerivWithinAt
  · intro d _; exact (hff d).hasDerivWithinAt
  · intro d hd
    have h := interior_subset hd
    have hq : 157/200 ≤ d+v ∧ d+v ≤ 5/3 := by
      constructor <;> linarith [hv.1,hv.2,h.1,h.2]
    have hdiag := diagonal_lower upper h
    have hchord := chord_second_upper hq
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ d/2 by linarith [h.1])
      (show d/2 ≤ Real.pi by linarith [h.2,Real.pi_gt_d2])
    have hc := Real.cos_le_one (d/2)
    dsimp [f'',southB,wingCos,diagonalWeight] at *
    linarith

end SquaresInCircles.Six.Analytic.CardinalWestOwnSouth
