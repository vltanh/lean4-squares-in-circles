import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.MarkerArc

/-!
# Support sums of a canonical pair

The support sum of a canonical pair on each of the four edge axes of the first
square, with its value on each axis. A sign `s` turns the state `(a, u)` into
the offset `s u` and the label `s * label a u`, and the second square is turned
by the relative phase. The support of a square is at least the support of any
point of its marker arc.
-/
noncomputable section
namespace SquaresInCircles.Seven

inductive TransverseSign where
  | positive
  | negative

namespace TransverseSign

def coe : TransverseSign → ℝ
  | .positive => 1
  | .negative => -1

def flip : TransverseSign → TransverseSign
  | .positive => .negative
  | .negative => .positive

lemma coe_flip (s : TransverseSign) : s.flip.coe = -s.coe := by cases s <;> norm_num [flip,coe]

end TransverseSign

def cardinalAngle (k : Fin 4) : ℝ := (k.val : ℝ)*Real.pi/2

def pairSupport (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) (gamma : ℝ) : ℝ :=
  support a (s.coe*u) (cardinalAngle k) +
  support A (t.coe*v)
    (cardinalAngle k+Real.pi-gamma-s.coe*label a u+t.coe*label A v)

lemma sign_admissible {a u : ℝ} (h : Admissible a u) (s : TransverseSign) :
    Admissible a |s.coe*u| := by
  cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.u_nonneg] using h

/-- A point of the marker arc about the signed label lies in the closed square,
so its support in every direction is at most that of the square. -/
lemma marker_arc_support {a u x : ℝ} (h : Admissible a u) (s : TransverseSign)
    (hx : |x-s.coe*label a u| ≤ 801/1600) (z : ℝ) :
    Real.cos (z-x) ≤ support a (s.coe*u) z := by
  rw [Real.cos_sub]
  cases s
  · obtain ⟨hc,hs⟩ := marker_arc h (by simpa [TransverseSign.coe] using hx)
    simpa [TransverseSign.coe,mul_comm] using point_le_support hc hs z
  · obtain ⟨hc,hs⟩ := marker_arc h (t := -x) (by
      rw [show -x-label a u = -(x-TransverseSign.negative.coe*label a u) by
        simp [TransverseSign.coe]; ring,abs_neg]
      exact hx)
    rw [Real.cos_neg,Real.sin_neg,show -Real.sin x-u = -(Real.sin x-(-1)*u) by ring,
      abs_neg] at *
    simpa [TransverseSign.coe,mul_comm] using point_le_support hc hs z

lemma support_three_half_sub (a b z : ℝ) :
    support a b (3*Real.pi/2-z) =
      -a*Real.sin z-b*Real.cos z+(|Real.sin z|+|Real.cos z|)/2 := by
  rw [show 3*Real.pi/2-z = (Real.pi/2-z)+Real.pi by ring]
  simp only [support,Real.cos_add_pi,Real.sin_add_pi,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub,abs_neg]
  ring

lemma support_two_pi_sub (a b z : ℝ) :
    support a b (2*Real.pi-z) =
      a*Real.cos z-b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2 := by
  simp only [support,Real.cos_two_pi_sub,Real.sin_two_pi_sub,abs_neg]
  ring

lemma pairSupport_zero (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 0 gamma =
      a+1/2+support A (t.coe*v)
        (Real.pi-gamma-s.coe*label a u+t.coe*label A v) := by
  simp [pairSupport,cardinalAngle,support]

lemma pairSupport_one (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 1 gamma =
      1/2+s.coe*u+support A (t.coe*v)
        (3*Real.pi/2-gamma-s.coe*label a u+t.coe*label A v) := by
  norm_num [pairSupport,cardinalAngle,support]
  ring_nf

lemma pairSupport_two (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 2 gamma =
      1/2-a+support A (t.coe*v)
        (2*Real.pi-gamma-s.coe*label a u+t.coe*label A v) := by
  norm_num [pairSupport,cardinalAngle,support]
  ring_nf

lemma pairSupport_three (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 3 gamma =
      1/2-s.coe*u+support A (t.coe*v)
        (5*Real.pi/2-gamma-s.coe*label a u+t.coe*label A v) := by
  have hk : cardinalAngle (3 : Fin 4) = Real.pi+Real.pi/2 := by norm_num [cardinalAngle]; ring
  rw [pairSupport,hk]
  norm_num [support,Real.cos_add,Real.sin_add]
  ring_nf

/-- The inward support sum with a positive source sign, in the turn
`label a u - t label A v - π/6`. -/
lemma pairSupport_inward {a u A v : ℝ} (t : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .positive t 2 gap =
      1/2-a-A*Real.sin (label a u-t.coe*label A v-Real.pi/6)+
      |Real.sin (label a u-t.coe*label A v-Real.pi/6)|/2+
      (1/2-t.coe*v)*Real.cos (label a u-t.coe*label A v-Real.pi/6) := by
  have hc : 0 ≤ Real.cos (label a u-t.coe*label A v-Real.pi/6) := by
    obtain ⟨h0,h1⟩ := h.label_mem
    obtain ⟨h2,h3⟩ := h'.label_mem
    apply Real.cos_nonneg_of_mem_Icc
    cases t <;> simp only [TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have he : 2*Real.pi-gap-TransverseSign.positive.coe*label a u+t.coe*label A v =
      3*Real.pi/2-(label a u-t.coe*label A v-Real.pi/6) := by
    simp only [gap,TransverseSign.coe]
    ring
  rw [pairSupport_two,he,support_three_half_sub,abs_of_nonneg hc]
  ring

/-! The support sums in the frame of the first square: the relative phase `d`
of the second square and the coordinates of its centre give each sum as the
half-width of the pair on that axis minus the offset of the centres. -/

def relativePhase (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  g+s.coe*label a u-t.coe*label A v

def centerDX (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  A*Real.cos (relativePhase a u A v g s t)-t.coe*v*Real.sin (relativePhase a u A v g s t)-a

def centerDY (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  A*Real.sin (relativePhase a u A v g s t)+t.coe*v*Real.cos (relativePhase a u A v g s t)-s.coe*u

def pairWidth (d : ℝ) : ℝ := (1+|Real.cos d|+|Real.sin d|)/2

lemma pair_support_axis_values (a u A v g : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 0 g=pairWidth (relativePhase a u A v g s t)-centerDX a u A v g s t ∧
    pairSupport a u A v s t 1 g=pairWidth (relativePhase a u A v g s t)-centerDY a u A v g s t ∧
    pairSupport a u A v s t 2 g=pairWidth (relativePhase a u A v g s t)+centerDX a u A v g s t ∧
    pairSupport a u A v s t 3 g=pairWidth (relativePhase a u A v g s t)+centerDY a u A v g s t := by
  let d := relativePhase a u A v g s t
  have he (c : ℝ) : c-g-s.coe*label a u+t.coe*label A v=c-d := by
    dsimp [d,relativePhase]
    ring
  rw [pairSupport_zero,pairSupport_one,pairSupport_two,pairSupport_three,he,he,he,he,
    support_three_half_sub,support_two_pi_sub,
    show 5*Real.pi/2-d=(Real.pi/2-d)+2*Real.pi by ring]
  simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,Real.cos_add_two_pi,Real.sin_add_two_pi,
    Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,abs_neg,pairWidth,centerDX,centerDY,d]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

end SquaresInCircles.Seven
