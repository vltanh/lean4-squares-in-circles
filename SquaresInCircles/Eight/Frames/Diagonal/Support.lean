module

public import SquaresInCircles.Eight.Frames.Diagonal.Transport
public import SquaresInCircles.Eight.Frames.Pair.Calculus

/-!
# Eight squares: the supports of the folded pairs on the diagonal circle

For `lam ≥ 0`, the cost of a folded pair less `lam` times the central margin is a base plus a
linear function `source m i lam` of the source state and a linear function `target n j lam x` of
the target state (`exact_identity`); with a nonnegative margin, lower bounds of the two parts give
a lower bound of the cost (`support`). The supports of the whole circle bound the two parts for
coefficients of any signs (`source_circle_lower`, `target_circle_lower`, `both_circle`), and the
derivatives along the arcs locate their minima (`source_deriv`, `target_deriv`); the bounds at the
two ends stay separate inequalities. The base has closed forms before and after the quarter turn
(`base_first`, `base_second`, `fixed_target_first`, `fixed_target_second`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalSupport
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def sourceU (m i : Bool) (lam : ℝ) : ℝ := sign i*primary m-lam
def sourceV (m i : Bool) (lam : ℝ) : ℝ := sign i*(transverse m-lam)
def targetU (n j : Bool) (lam x : ℝ) : ℝ :=
  -sign j*primary n-lam*(Real.sin x-Real.cos x)
def targetV (n j : Bool) (lam x : ℝ) : ℝ :=
  sign j*(lam*(Real.sin x+Real.cos x)-transverse n)
def source (m i : Bool) (lam b : ℝ) : ℝ := linear (sourceU m i lam) (sourceV m i lam) b
def target (n j : Bool) (lam x B : ℝ) : ℝ := linear (targetU n j lam x) (targetV n j lam x) B
def base (m n i j : Bool) (lam x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+2*lam*pairWidth x+sign i*constant m-sign j*constant n
def sourceCircle (m i : Bool) (lam : ℝ) : ℝ :=
  -sourceU m i lam-R*Real.sqrt ((sourceU m i lam)^2+(sourceV m i lam)^2)
def targetCircle (n j : Bool) (lam x : ℝ) : ℝ :=
  -targetU n j lam x-R*Real.sqrt ((targetU n j lam x)^2+(targetV n j lam x)^2)

theorem exact_identity (m n i j : Bool) (lam b B x : ℝ) :
    cost m n i j b B x-lam*central i j (A b) b (A B) B x=
      base m n i j lam x+source m i lam b+target n j lam x B := by
  rw [cost,marker_affine,marker_affine]
  dsimp [central,base,source,target,linear,sourceU,sourceV,targetU,targetV]
  ring

theorem support {m n i j : Bool} {lam b B x S T : ℝ}
    (hlam : 0≤lam) (hm : 0≤central i j (A b) b (A B) B x)
    (hs : S≤ source m i lam b) (ht : T≤target n j lam x B) :
    base m n i j lam x+S+T≤cost m n i j b B x := by
  have he := exact_identity m n i j lam b B x
  have hp := mul_nonneg hlam hm
  linarith

theorem source_circle_lower (m i : Bool) (lam : ℝ) {b : ℝ} (hb : b∈arc m) :
    sourceCircle m i lam≤ source m i lam b :=
  circle_linear_lower (A_circle (arc_subset hb)) (sourceU m i lam) (sourceV m i lam)

theorem target_circle_lower (n j : Bool) (lam x : ℝ) {B : ℝ} (hB : B∈arc n) :
    targetCircle n j lam x≤target n j lam x B :=
  circle_linear_lower (A_circle (arc_subset hB)) (targetU n j lam x) (targetV n j lam x)

theorem both_circle {m n i j : Bool} {lam b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hlam : 0≤lam)
    (hm : 0≤central i j (A b) b (A B) B x) :
    base m n i j lam x+sourceCircle m i lam+targetCircle n j lam x≤
      cost m n i j b B x :=
  support hlam hm (source_circle_lower m i lam hb) (target_circle_lower n j lam x hB)

theorem source_deriv (m i : Bool) (lam : ℝ) {b : ℝ} (hb : b∈arc m) :
    HasDerivAt (source m i lam)
      (-sourceU m i lam*slope b+sourceV m i lam) b := by
  have h := linear_hasDerivAt (arc_subset hb) (sourceU m i lam) (sourceV m i lam)
  have he : -sourceU m i lam*FrameDiagonalArc.slope b+sourceV m i lam=
      sourceU m i lam*Ad b+sourceV m i lam := by
    simp only [Ad,FrameDiagonalArc.slope]; ring
  rw [he]
  exact h

theorem target_deriv (n j : Bool) (lam x : ℝ) {B : ℝ} (hB : B∈arc n) :
    HasDerivAt (target n j lam x)
      (-targetU n j lam x*slope B+targetV n j lam x) B := by
  have h := linear_hasDerivAt (arc_subset hB) (targetU n j lam x) (targetV n j lam x)
  have he : -targetU n j lam x*FrameDiagonalArc.slope B+targetV n j lam x=
      targetU n j lam x*Ad B+targetV n j lam x := by
    simp only [Ad,FrameDiagonalArc.slope]; ring
  rw [he]
  exact h

theorem base_first (m n i j : Bool) (lam : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    base m n i j lam x=
      x+9/100+lam+(lam-9/100)*(Real.sin x+Real.cos x)+
        sign i*constant m-sign j*constant n := by
  rw [base,(first_width hx).1,(first_width hx).2]
  ring

theorem base_second (m n i j : Bool) (lam : ℝ) {x : ℝ}
    (hx : x∈Icc (Real.pi/2) Real.pi) :
    base m n i j lam x=
      x+9/100+lam+(lam-9/100)*(Real.sin x-Real.cos x)+
        sign i*constant m-sign j*constant n := by
  rw [base,(second_width hx).1,(second_width hx).2]
  ring

theorem fixed_target_first (m n i j : Bool) (lam B S : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    base m n i j lam x+S+target n j lam x B=
      x+9/100+lam+sign i*constant m-sign j*marker n B+S+
        (lam*(1+A B+sign j*B)-9/100)*Real.cos x+
        (lam*(1-A B+sign j*B)-9/100)*Real.sin x := by
  rw [base_first m n i j lam hx,marker_affine]
  dsimp [target,targetU,targetV,linear]
  ring

theorem fixed_target_second (m n i j : Bool) (lam B S : ℝ) {x : ℝ}
    (hx : x∈Icc (Real.pi/2) Real.pi) :
    base m n i j lam x+S+target n j lam x B=
      x+9/100+lam+sign i*constant m-sign j*marker n B+S+
        (lam*(A B+sign j*B-1)+9/100)*Real.cos x+
        (lam*(1-A B+sign j*B)-9/100)*Real.sin x := by
  rw [base_second m n i j lam hx,marker_affine]
  dsimp [target,targetU,targetV,linear]
  ring

end SquaresInCircles.Eight.FrameDiagonalSupport
