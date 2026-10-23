module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondMixedPrimarySupportLower
public import SquaresInCircles.Eight.TableFree.SecondOuterVBounds
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Two global tangents for the positive outer target at role two

Each affine envelope follows from the strict concavity of the original
outer label.  Its fixed reference is enclosed directly by the physical
circle equation.  Both envelopes hold on the entire outer arc.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic

def p : ℝ := 33529/50000
def k : ℝ := 59217/500000
def γ : ℝ := 17953/20000
def value (b B φ : ℝ) : ℝ := φ-c-g*b-V B
def K : ℝ := Real.pi/2-c-k+(g+p)/2-γ
def reference : ℝ := 229/400

lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])

lemma tangent_reference :
    (134115933/200000000:ℝ)<VLabel.d1 reference ∧
      VLabel.d1 reference<p ∧ V reference<(502340627/1000000000:ℝ) := by
  have hu := shifted_chart_reference (outer_domain reference_mem)
    (l := (20786653432852/12500000000000:ℝ))
    (u := (166293227462817/100000000000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
  have hd := VLabel.first_chart_reference (outer_domain reference_mem)
    (l := (20786653432852/12500000000000:ℝ))
    (u := (166293227462817/100000000000000:ℝ))
    (dlo := (134115933/200000000:ℝ)) (dhi := p)
    (by norm_num) (by norm_num)
    (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
    (by norm_num [reference,VLabel,W,Q0,p]) (by norm_num [reference,VLabel,W,Q0,p])
  refine ⟨hd.1,hd.2,?_⟩
  have he : V reference= -(41/4000)*(U reference-1/2)+
      (16031/100000)*reference+(63457/100000)*(U reference-1/2)*reference := by
    dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel,U]
    ring
  rw [he]
  norm_num [reference] at *
  linarith

lemma tangent_upper {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : V B≤k+p*B := by
  have hh := VLabel.tangent_upper (fun _ hy => outer_domain hy) hB reference_mem
    (fun y hy => (V_second_upper hy).le)
  change V B≤V reference+VLabel.d1 reference*(B-reference) at hh
  have hp := mul_le_mul_of_nonneg_right tangent_reference.2.1.le hB.1
  have hδ := tangent_reference.1
  have hV := tangent_reference.2.2
  dsimp [reference,k] at *
  nlinarith

lemma zero_first_upper : VLabel.d1 0<(1061/1000:ℝ) := by
  have hh := VLabel.first_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567/100000000:ℝ)) (u := (47864392/25000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (1061/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact hh.2

lemma zero_tangent_upper {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    V B≤ -1449/100000+(1061/1000)*B := by
  have hh := VLabel.tangent_upper (fun _ hy => outer_domain hy) hB outer_zero_mem
    (fun y hy => (V_second_upper hy).le)
  change V B≤V 0+VLabel.d1 0*(B-0) at hh
  have hp := mul_le_mul_of_nonneg_right zero_first_upper.le hB.1
  linarith [V_zero_bounds.2]

lemma K_bounds : (1408657326/1000000000:ℝ)<K ∧ K<(1408657327/1000000000:ℝ) := by
  dsimp [K,c,g,p,k,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma radius_fine : (791515/400000:ℝ)<radius ∧ radius<(494697/250000:ℝ) := by
  have hh := radius_sq
  norm_num [Q0] at hh
  constructor <;> nlinarith [radius_bounds.1]

lemma primary_norm_zero :
    (123728831/100000000:ℝ)<MixedPrimarySupport.N g p 0 ∧
      MixedPrimarySupport.N g p 0<(15466104/12500000:ℝ) := by
  have hh := MixedPrimarySupport.N_sq (p := p) (x := 0)
    (show 0<g by norm_num [g])
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  norm_num [g,p] at hh
  constructor <;> nlinarith

lemma primary_zero : (13/100000:ℝ)<MixedPrimarySupport.minus g p K 0 := by
  have hRN := (mul_lt_mul_of_pos_left primary_norm_zero.2
    (by linarith [radius_bounds.1] : 0<radius)).trans
      (mul_lt_mul_of_pos_right radius_fine.2
        (by norm_num : (0:ℝ)<15466104/12500000))
  rw [MixedPrimarySupport.minus_zero]
  norm_num [g]
  linarith [K_bounds.1]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
