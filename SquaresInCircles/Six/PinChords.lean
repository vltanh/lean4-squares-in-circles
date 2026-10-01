import SquaresInCircles.Six.DiagonalPositive
import SquaresInCircles.Six.DirectedAxes

/-!
# Chords between the fixed pins

The five fixed pins lie on the circle of radius `9/10` about the disk centre, at
the angles `0`, `π/2`, `11π/12`, `5π/4` and `19π/12`. The chords W–D and D–S
have length `9/10`, the chords N–W and E–S have length `(9/5) sin (5π/24)`, and
the reflection in the diagonal `y = x` exchanges the two chords of each pair.
The projections of the chords W–D and D–S on the axes of a square at a given
angle give the signs used to orient separating axes.
-/
noncomputable section
namespace SquaresInCircles.Six
open Normalization Normalization.Certificates

def polar (r t : ℝ) : Point := (r*Real.cos t,r*Real.sin t)
def primary (t : ℝ) : Point := (Real.cos t,Real.sin t)
def secondary (t : ℝ) : Point := (-Real.sin t,Real.cos t)

private lemma cos_pi_add' (x : ℝ) : Real.cos (Real.pi+x) = -Real.cos x := by
  rw [add_comm,Real.cos_add_pi]

private lemma sin_pi_add' (x : ℝ) : Real.sin (Real.pi+x) = -Real.sin x := by
  rw [add_comm,Real.sin_add_pi]

lemma centered_chord (r m u : ℝ) :
    sub (polar r (m+u)) (polar r (m-u)) =
      scale (2*r*Real.sin u) (-Real.sin m,Real.cos m) := by
  apply Prod.ext <;> dsimp [sub,polar,scale] <;>
    simp only [Real.cos_add,Real.cos_sub,Real.sin_add,Real.sin_sub] <;> ring

lemma sub_reverse (p q : Point) : sub p q=scale (-1) (sub q p) := by
  apply Prod.ext <;> dsimp [sub,scale] <;> ring

/-- The chord from the pin of W to the pin of D. -/
lemma pin_chord_WD : sub (fixedPin 3) (fixedPin 2)=
    ((9/10)*Real.sin (Real.pi/12),-(9/10)*Real.cos (Real.pi/12)) := by
  have h := centered_chord (9/10) (13*Real.pi/12) (Real.pi/6)
  have h1 : 13*Real.pi/12+Real.pi/6=(5/4)*Real.pi := by ring
  have h2 : 13*Real.pi/12-Real.pi/6=(11/12)*Real.pi := by ring
  rw [h1,h2,show 13*Real.pi/12=Real.pi+Real.pi/12 by ring,
    sin_pi_add',cos_pi_add',Real.sin_pi_div_six,
    show (2:ℝ)*(9/10)*(1/2)=9/10 by norm_num] at h
  simpa [fixedPin,polar,scale] using h

/-- The chord from the pin of D to the pin of S, the reflection of the chord
W–D in the diagonal. -/
lemma pin_chord_DS : sub (fixedPin 4) (fixedPin 3)=
    ((9/10)*Real.cos (Real.pi/12),-(9/10)*Real.sin (Real.pi/12)) := by
  have h := congrArg diagonalPoint pin_chord_WD
  have hd : ∀ p q : Point, diagonalPoint (sub p q)=sub (diagonalPoint p) (diagonalPoint q) := by
    intro p q
    rfl
  rw [hd,fixedPin_diagonal,fixedPin_diagonal] at h
  change sub (fixedPin 3) (fixedPin 4)=
    (-(9/10)*Real.cos (Real.pi/12),(9/10)*Real.sin (Real.pi/12)) at h
  rw [sub_reverse (fixedPin 4) (fixedPin 3),h]
  apply Prod.ext <;> dsimp [scale] <;> ring

/-- The common length of the chords N–W and E–S. -/
def adjacentChordLength : ℝ := (9/5)*Real.sin (5*Real.pi/24)

lemma adjacentChordLength_pos : 0 < adjacentChordLength := by
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

lemma pin_chord_NW : sub (fixedPin 1) (fixedPin 2)=
    polar adjacentChordLength (5*Real.pi/24) := by
  have h := centered_chord (9/10) (17*Real.pi/24) (5*Real.pi/24)
  have h1 : 17*Real.pi/24+5*Real.pi/24=(11/12)*Real.pi := by ring
  have h2 : 17*Real.pi/24-5*Real.pi/24=Real.pi/2 := by ring
  rw [h1,h2,show 17*Real.pi/24=Real.pi/2+5*Real.pi/24 by ring,
    Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two] at h
  have hn : polar (9/10) (Real.pi/2)=fixedPin 1 := by simp [polar,fixedPin]
  have hw : polar (9/10) ((11/12)*Real.pi)=fixedPin 2 := rfl
  rw [hn,hw] at h
  rw [sub_reverse (fixedPin 1) (fixedPin 2),h]
  apply Prod.ext <;> dsimp [scale,polar,adjacentChordLength] <;> ring

lemma pin_chord_ES : sub (fixedPin 0) (fixedPin 4)=
    polar adjacentChordLength (7*Real.pi/24) := by
  have h := congrArg diagonalPoint pin_chord_NW
  change sub (diagonalPoint (fixedPin 1)) (diagonalPoint (fixedPin 2))=
    diagonalPoint (polar adjacentChordLength (5*Real.pi/24)) at h
  rw [fixedPin_diagonal,fixedPin_diagonal] at h
  change sub (fixedPin 0) (fixedPin 4)=_ at h
  rw [h,show 7*Real.pi/24=Real.pi/2-5*Real.pi/24 by ring]
  apply Prod.ext <;> simp [diagonalPoint,polar,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]

lemma WD_secondary_projection (t : ℝ) :
    dot (secondary (Real.pi+t)) (sub (fixedPin 3) (fixedPin 2))=
      (9/10)*Real.cos (t-Real.pi/12) := by
  rw [pin_chord_WD]
  dsimp [dot,secondary]
  rw [cos_pi_add',sin_pi_add',Real.cos_sub]
  ring

lemma DS_primary_D_projection (d : ℝ) :
    dot (primary (Real.pi+d)) (sub (fixedPin 4) (fixedPin 3))=
      -(9/10)*Real.cos (d+Real.pi/12) := by
  rw [pin_chord_DS]
  dsimp [dot,primary]
  rw [cos_pi_add',sin_pi_add',Real.cos_add]
  ring

lemma DS_secondary_D_projection (d : ℝ) :
    dot (secondary (Real.pi+d)) (sub (fixedPin 4) (fixedPin 3))=
      (9/10)*Real.sin (d+Real.pi/12) := by
  rw [pin_chord_DS]
  dsimp [dot,secondary]
  rw [cos_pi_add',sin_pi_add',Real.sin_add]
  ring

lemma DS_secondary_S_projection (s : ℝ) :
    dot (secondary (3*Real.pi/2+s)) (sub (fixedPin 4) (fixedPin 3))=
      (9/10)*Real.cos (s+Real.pi/12) := by
  rw [pin_chord_DS]
  dsimp [dot,secondary]
  rw [Real.cos_add,Real.sin_add,south_cos,south_sin,Real.cos_add]
  ring

end SquaresInCircles.Six
