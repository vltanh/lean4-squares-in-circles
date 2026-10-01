import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Transverse

/-!
# The west-dominant five-edge profile

Weights on CW, CS, CD, WD and DS are 9/4, 3/4, 9/20, 1 and 1.
The Boolean records which endpoint of the central y interval supports the
actual force. Both alternatives will be proved over the entire domain.
The support estimates use the radial-chord majorant and the smooth quadratic
axial support; their scalar expression is separated into three harmonics,
a chord term and a transverse term. All derivatives are displayed below.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

def westWeight : ℝ := 9/4
def southWeight : ℝ := 3/4
def diagonalWeight : ℝ := 9/20
def centerY (upper : Bool) : ℝ := if upper then 5641/50000 else 0

def westTerm (upper : Bool) (v : ℝ) : ℝ :=
  westWeight*(wingCos*Real.cos v+(1/2+centerY upper)*Real.sin v)
def southTerm (upper : Bool) (s : ℝ) : ℝ :=
  southWeight*((1/2-centerY upper)*Real.cos s+wingSin*Real.sin s)
def diagonalTerm (upper : Bool) (d : ℝ) : ℝ :=
  diagonalWeight*(wingCos*Real.cos d+(1/2-centerY upper)*Real.sin d)

def westFirst (upper : Bool) (v : ℝ) : ℝ :=
  westWeight*(-wingCos*Real.sin v+(1/2+centerY upper)*Real.cos v)
def southFirst (upper : Bool) (s : ℝ) : ℝ :=
  southWeight*(-(1/2-centerY upper)*Real.sin s+wingSin*Real.cos s)
def diagonalFirst (upper : Bool) (d : ℝ) : ℝ :=
  diagonalWeight*(-wingCos*Real.sin d+(1/2-centerY upper)*Real.cos d)

def constantTerm : ℝ := 20670077/250000000

def westSlice (upper : Bool) (d v : ℝ) : ℝ := westTerm upper v+chord (d+v)
def southSlice (upper : Bool) (d s : ℝ) : ℝ := southTerm upper s+transverse (d-s)

def profile (upper : Bool) (v s d : ℝ) : ℝ :=
  constantTerm+diagonalTerm upper d+westSlice upper d v+southSlice upper d s

lemma west_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westTerm upper) (westFirst upper v) v := by
  exact ((((Real.hasDerivAt_cos v).const_mul wingCos).fun_add
    ((Real.hasDerivAt_sin v).const_mul (1/2+centerY upper))).const_mul westWeight).congr_deriv
    (by simp only [westFirst]; ring)

lemma west_first_hasDeriv (upper : Bool) (v : ℝ) :
    HasDerivAt (westFirst upper) (-westTerm upper v) v := by
  exact ((((Real.hasDerivAt_sin v).const_mul (-wingCos)).fun_add
    ((Real.hasDerivAt_cos v).const_mul (1/2+centerY upper))).const_mul westWeight).congr_deriv
    (by simp only [westTerm]; ring)

lemma south_hasDeriv (upper : Bool) (s : ℝ) :
    HasDerivAt (southTerm upper) (southFirst upper s) s := by
  exact ((((Real.hasDerivAt_cos s).const_mul (1/2-centerY upper)).fun_add
    ((Real.hasDerivAt_sin s).const_mul wingSin)).const_mul southWeight).congr_deriv
    (by simp only [southFirst]; ring)

lemma south_first_hasDeriv (upper : Bool) (s : ℝ) :
    HasDerivAt (southFirst upper) (-southTerm upper s) s := by
  exact ((((Real.hasDerivAt_sin s).const_mul (-(1/2-centerY upper))).fun_add
    ((Real.hasDerivAt_cos s).const_mul wingSin)).const_mul southWeight).congr_deriv
    (by simp only [southTerm]; ring)

lemma diagonal_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalTerm upper) (diagonalFirst upper d) d := by
  exact ((((Real.hasDerivAt_cos d).const_mul wingCos).fun_add
    ((Real.hasDerivAt_sin d).const_mul (1/2-centerY upper))).const_mul
    diagonalWeight).congr_deriv (by simp only [diagonalFirst]; ring)

lemma diagonal_first_hasDeriv (upper : Bool) (d : ℝ) :
    HasDerivAt (diagonalFirst upper) (-diagonalTerm upper d) d := by
  exact ((((Real.hasDerivAt_sin d).const_mul (-wingCos)).fun_add
    ((Real.hasDerivAt_cos d).const_mul (1/2-centerY upper))).const_mul
    diagonalWeight).congr_deriv (by simp only [diagonalTerm]; ring)

lemma west_slice_hasDeriv (upper : Bool) (d v : ℝ) :
    HasDerivAt (westSlice upper d) (westFirst upper v+chordFirst (d+v)) v := by
  have h := (chord_hasDeriv (d+v)).comp v ((hasDerivAt_id' v).const_add d)
  exact ((west_hasDeriv upper v).fun_add h).congr_deriv (by ring)

lemma west_slice_first_hasDeriv (upper : Bool) (d v : ℝ) :
    HasDerivAt (fun x => westFirst upper x+chordFirst (d+x))
      (-westTerm upper v+chordSecond (d+v)) v := by
  have h := (chord_first_hasDeriv (d+v)).comp v ((hasDerivAt_id' v).const_add d)
  exact ((west_first_hasDeriv upper v).fun_add h).congr_deriv (by ring)

lemma south_slice_hasDeriv (upper : Bool) (d s : ℝ) :
    HasDerivAt (southSlice upper d) (southFirst upper s-transverseFirst (d-s)) s := by
  have h := (transverse_hasDeriv (d-s)).comp s ((hasDerivAt_id' s).const_sub d)
  exact ((south_hasDeriv upper s).fun_add h).congr_deriv (by ring)

lemma south_slice_first_hasDeriv (upper : Bool) (d s : ℝ) :
    HasDerivAt (fun x => southFirst upper x-transverseFirst (d-x))
      (-southTerm upper s+transverseSecond (d-s)) s := by
  have h := (transverse_first_hasDeriv (d-s)).comp s ((hasDerivAt_id' s).const_sub d)
  exact ((south_first_hasDeriv upper s).fun_sub h).congr_deriv (by ring)

lemma profile_diagonal_hasDeriv (upper : Bool) (v s d : ℝ) :
    HasDerivAt (profile upper v s)
      (diagonalFirst upper d+chordFirst (d+v)+transverseFirst (d-s)) d := by
  have hq := (chord_hasDeriv (d+v)).comp d ((hasDerivAt_id' d).add_const v)
  have hr := (transverse_hasDeriv (d-s)).comp d ((hasDerivAt_id' d).sub_const s)
  have h := (((diagonal_hasDeriv upper d).fun_add hq).fun_add hr).const_add
    (constantTerm+westTerm upper v+southTerm upper s)
  have e : profile upper v s = fun x => (constantTerm+westTerm upper v+southTerm upper s)+
      (diagonalTerm upper x+(chord ∘ fun x => x+v) x+(transverse ∘ fun x => x-s) x) := by
    funext x
    simp only [profile,westSlice,southSlice,Function.comp_apply]
    ring
  rw [e]
  exact h.congr_deriv (by ring)

lemma profile_diagonal_first_hasDeriv (upper : Bool) (v s d : ℝ) :
    HasDerivAt (fun x => diagonalFirst upper x+chordFirst (x+v)+transverseFirst (x-s))
      (-diagonalTerm upper d+chordSecond (d+v)+transverseSecond (d-s)) d := by
  have hq := (chord_first_hasDeriv (d+v)).comp d ((hasDerivAt_id' d).add_const v)
  have hr := (transverse_first_hasDeriv (d-s)).comp d ((hasDerivAt_id' d).sub_const s)
  exact (((diagonal_first_hasDeriv upper d).fun_add hq).fun_add hr).congr_deriv (by ring)

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant
