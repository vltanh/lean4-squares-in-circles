module
public import SquaresInCircles.Six.Analytic.ReflectedOwnWings.Transverse

@[expose] public section

/-!
# Coordinate concavity for the last reflected two-OWN case

The scalar reflection gives 157/200<=d<=163/175, not the original diagonal
half-window. Here 48/175<=s<=12/25 and 0<=v<=2/3. The chord curvature is
at most -19/100, the transverse curvature at most 31/100, the south harmonic
at least 9/25, and the diagonal harmonic at least (9/20)A. These explicit
reserves prove all coordinate concavity statements on the enlarged domain.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.ReflectedOwnWings

def beta : ℝ := 9/4
def gamma : ℝ := 3/4
def delta : ℝ := 9/20
def face (upper : Bool) : ℝ := if upper then 5641/50000 else 0

def chordSin : ℝ := 27701483/8000000
def chordCos : ℝ := 75987/100000
def constantTerm : ℝ := 20670077/250000000

def chord (q : ℝ) : ℝ := Real.sin q-chordSin*Real.sin (q/2)-chordCos*Real.cos (q/2)
def chordFirst (q : ℝ) : ℝ :=
  Real.cos q-(chordSin/2)*Real.cos (q/2)+(chordCos/2)*Real.sin (q/2)
def chordSecond (q : ℝ) : ℝ :=
  -Real.sin q+(chordSin/4)*Real.sin (q/2)+(chordCos/4)*Real.cos (q/2)

def westTerm (upper : Bool) (v : ℝ) : ℝ := beta*(A*Real.cos v+(1/2+face upper)*Real.sin v)
def southTerm (upper : Bool) (s : ℝ) : ℝ := gamma*((1/2-face upper)*Real.cos s+B*Real.sin s)
def diagonalTerm (upper : Bool) (d : ℝ) : ℝ := delta*(A*Real.cos d+(1/2-face upper)*Real.sin d)

def westFirst (upper : Bool) (v : ℝ) : ℝ := beta*(-A*Real.sin v+(1/2+face upper)*Real.cos v)
def southFirst (upper : Bool) (s : ℝ) : ℝ := gamma*(-(1/2-face upper)*Real.sin s+B*Real.cos s)
def diagonalFirst (upper : Bool) (d : ℝ) : ℝ := delta*(-A*Real.sin d+(1/2-face upper)*Real.cos d)

def westSlice (upper : Bool) (d v : ℝ) : ℝ := westTerm upper v+chord (d+v)
def southSlice (upper : Bool) (d s : ℝ) : ℝ := southTerm upper s+transverse (d-s)

def value (upper : Bool) (v s d : ℝ) : ℝ :=
  constantTerm+diagonalTerm upper d+westSlice upper d v+southSlice upper d s

lemma chord_hasDeriv (q : ℝ) : HasDerivAt chord (chordFirst q) q := by
  convert (((Real.hasDerivAt_sin q).sub
    ((((hasDerivAt_id q).div_const 2).sin).const_mul chordSin)).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul chordCos)) using 1 <;>
    dsimp [chord,chordFirst] <;> ring

lemma chord_first_hasDeriv (q : ℝ) : HasDerivAt chordFirst (chordSecond q) q := by
  convert (((Real.hasDerivAt_cos q).sub
    ((((hasDerivAt_id q).div_const 2).cos).const_mul (chordSin/2))).add
    ((((hasDerivAt_id q).div_const 2).sin).const_mul (chordCos/2))) using 1 <;>
    dsimp [chordFirst,chordSecond] <;> ring

lemma chord_second_upper {q : ℝ} (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    chordSecond q ≤ -(19/100) :=
  HighChordCurvature.upper (L := chordSin) (M := chordCos) le_rfl le_rfl hq

lemma west_hasDeriv (upper : Bool) (v : ℝ) : HasDerivAt (westTerm upper) (westFirst upper v) v := by
  convert (((Real.hasDerivAt_cos v).const_mul A).add
    ((Real.hasDerivAt_sin v).const_mul (1/2+face upper))).const_mul beta using 1 <;>
    dsimp [westTerm,westFirst] <;> ring

lemma west_first_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westFirst upper) (-westTerm upper v) v := by
  convert (((Real.hasDerivAt_sin v).const_mul (-A)).add
    ((Real.hasDerivAt_cos v).const_mul (1/2+face upper))).const_mul beta using 1 <;>
    dsimp [westTerm,westFirst] <;> ring

lemma south_hasDeriv (upper : Bool) (s : ℝ) : HasDerivAt (southTerm upper) (southFirst upper s) s := by
  convert (((Real.hasDerivAt_cos s).const_mul (1/2-face upper)).add
    ((Real.hasDerivAt_sin s).const_mul B)).const_mul gamma using 1 <;>
    dsimp [southTerm,southFirst] <;> ring

lemma south_first_hasDeriv (upper : Bool) (s : ℝ) :
    HasDerivAt (southFirst upper) (-southTerm upper s) s := by
  convert (((Real.hasDerivAt_sin s).const_mul (-(1/2-face upper))).add
    ((Real.hasDerivAt_cos s).const_mul B)).const_mul gamma using 1 <;>
    dsimp [southTerm,southFirst] <;> ring

lemma diagonal_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalTerm upper) (diagonalFirst upper d) d := by
  convert (((Real.hasDerivAt_cos d).const_mul A).add
    ((Real.hasDerivAt_sin d).const_mul (1/2-face upper))).const_mul delta using 1 <;>
    dsimp [diagonalTerm,diagonalFirst] <;> ring

lemma diagonal_first_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalFirst upper) (-diagonalTerm upper d) d := by
  convert (((Real.hasDerivAt_sin d).const_mul (-A)).add
    ((Real.hasDerivAt_cos d).const_mul (1/2-face upper))).const_mul delta using 1 <;>
    dsimp [diagonalTerm,diagonalFirst] <;> ring

private lemma west_nonnegative (upper : Bool) {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 2/3) :
    0 ≤ westTerm upper v := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  cases upper <;> dsimp [westTerm,beta,A,face] <;> positivity

private lemma south_lower (upper : Bool) {s : ℝ} (hs : 48/175 ≤ s ∧ s ≤ 12/25) :
    9/25 ≤ southTerm upper s := by
  have hsq := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 12/25+s by linarith [hs.1])
  have hc : 22/25 ≤ Real.cos s := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (27:ℝ)/100 by linarith [Real.pi_pos])
    (show s ≤ Real.pi/2 by linarith [hs.2,Real.pi_gt_d2])
    (show (27:ℝ)/100 ≤ s by linarith [hs.1])
  have ht := Seven.sin_lower_seven (x := (27:ℝ)/100) (by norm_num)
  have hsin : 1/4 ≤ Real.sin s := by nlinarith only [hm,ht]
  cases upper <;> dsimp [southTerm,gamma,face,B] <;> linarith

private lemma diagonal_lower (upper : Bool) {d : ℝ}
    (hd : 157/200 ≤ d ∧ d ≤ 163/175) : delta*A ≤ diagonalTerm upper d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ d by linarith [hd.1]) (show d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
  have hp := mul_nonneg hc hs
  have hsum : 1 ≤ Real.cos d+Real.sin d := by nlinarith [Real.sin_sq_add_cos_sq d]
  cases upper <;> dsimp [diagonalTerm,delta,A,face] <;> nlinarith only [hs,hsum]

lemma west_concave (upper : Bool) {d : ℝ} (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (westSlice upper d) := by
  let f' : ℝ → ℝ := fun v => westFirst upper v+chordFirst (d+v)
  let f'' : ℝ → ℝ := fun v => -westTerm upper v+chordSecond (d+v)
  have hf (v : ℝ) : HasDerivAt (westSlice upper d) (f' v) v := by
    have hq := (chord_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert (west_hasDeriv upper v).add hq using 1 <;> dsimp [westSlice,f'] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    have hq := (chord_first_hasDeriv (d+v)).comp v ((hasDerivAt_id v).const_add d)
    convert (west_first_hasDeriv upper v).add hq using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
    (f' := f') (f'' := f'') (by dsimp [westSlice,westTerm,chord]; fun_prop)
  · intro v _; exact (hf v).hasDerivWithinAt
  · intro v _; exact (hff v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hq : 157/200 ≤ d+v ∧ d+v ≤ 5/3 := by
      constructor <;> linarith [hd.1,hd.2,h.1,h.2]
    dsimp [f'']
    linarith [west_nonnegative upper h,chord_second_upper hq]

lemma south_concave (upper : Bool) {d : ℝ} (hd : 157/200 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc (48/175) (12/25)) (southSlice upper d) := by
  let f' : ℝ → ℝ := fun s => southFirst upper s-transverseFirst (d-s)
  let f'' : ℝ → ℝ := fun s => -southTerm upper s+transverseSecond (d-s)
  have hf (s : ℝ) : HasDerivAt (southSlice upper d) (f' s) s := by
    have hr := (transverse_hasDeriv (d-s)).comp s ((hasDerivAt_id s).const_sub d)
    convert (south_hasDeriv upper s).add hr using 1 <;> dsimp [southSlice,f'] <;> ring
  have hff (s : ℝ) : HasDerivAt f' (f'' s) s := by
    have hr := (transverse_first_hasDeriv (d-s)).comp s ((hasDerivAt_id s).const_sub d)
    convert (south_first_hasDeriv upper s).sub hr using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (48/175) (12/25))
    (f' := f') (f'' := f'') (by dsimp [southSlice,southTerm,transverse]; fun_prop)
  · intro s _; exact (hf s).hasDerivWithinAt
  · intro s _; exact (hff s).hasDerivWithinAt
  · intro s hs
    have h := interior_subset hs
    have hr : 3/10 ≤ d-s ∧ d-s ≤ 2/3 := by
      constructor <;> linarith [hd.1,hd.2,h.1,h.2]
    dsimp [f'']
    linarith [south_lower upper h,transverse_second_upper hr]

lemma diagonal_concave (upper : Bool) {v s : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 48/175 ≤ s ∧ s ≤ 12/25) :
    ConcaveOn ℝ (Set.Icc (157/200) (163/175)) (value upper v s) := by
  let f' : ℝ → ℝ := fun d => diagonalFirst upper d+chordFirst (d+v)+transverseFirst (d-s)
  let f'' : ℝ → ℝ := fun d => -diagonalTerm upper d+chordSecond (d+v)+transverseSecond (d-s)
  have hf (d : ℝ) : HasDerivAt (value upper v s) (f' d) d := by
    have hq := (chord_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    have hr := (transverse_hasDeriv (d-s)).comp d ((hasDerivAt_id d).sub_const s)
    convert (((diagonal_hasDeriv upper d).add hq).add hr).const_add
      (constantTerm+westTerm upper v+southTerm upper s) using 1 <;>
      dsimp [value,westSlice,southSlice,f'] <;> ring
  have hff (d : ℝ) : HasDerivAt f' (f'' d) d := by
    have hq := (chord_first_hasDeriv (d+v)).comp d ((hasDerivAt_id d).add_const v)
    have hr := (transverse_first_hasDeriv (d-s)).comp d ((hasDerivAt_id d).sub_const s)
    convert ((diagonal_first_hasDeriv upper d).add hq).add hr using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (157/200) (163/175))
    (f' := f') (f'' := f'') (by dsimp [value,westSlice,southSlice,diagonalTerm,chord,transverse]; fun_prop)
  · intro d _; exact (hf d).hasDerivWithinAt
  · intro d _; exact (hff d).hasDerivWithinAt
  · intro d hd
    have h := interior_subset hd
    have hq : 157/200 ≤ d+v ∧ d+v ≤ 5/3 := by
      constructor <;> linarith [h.1,h.2,hv.1,hv.2]
    have hr : 3/10 ≤ d-s ∧ d-s ≤ 2/3 := by
      constructor <;> linarith [h.1,h.2,hs.1,hs.2]
    have hD := diagonal_lower upper h
    have hQ := chord_second_upper hq
    have hR := transverse_second_upper hr
    dsimp [f'',delta,A] at *
    linarith

end SquaresInCircles.Six.Analytic.ReflectedOwnWings
