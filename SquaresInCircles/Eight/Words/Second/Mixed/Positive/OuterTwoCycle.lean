module

public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeUpper
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.SupportThird
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds

/-!
# Eight squares: physical-cycle adapters for the complete positive-outer role-two row

The exact original owner is preserved, including ties.  Reflection
carries the literal role-two cost to role six.
-/

section
/-!
## All original role-two negative-outer to positive-core owners

The four weak physical axes are exhausted on the full closed quarter
window.  The estimates keep the original circle point, radius and
core piece, and require no separately supplied strip theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hrad := core_radius_sq ht
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.sin φ-B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [hs.1]
      have he : (A*Real.sin φ-B*Real.cos φ)^2+
          (A*Real.cos φ+B*Real.sin φ)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.cos φ+B*Real.sin φ)]
    · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
      have hbs := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
    · apply lower_secondary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.cos x+B*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [hs.1]
      have he : (A*Real.cos x+B*Real.sin x)^2+
          (A*Real.sin x-B*Real.cos x)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.sin x-B*Real.cos x)]
    · apply upper_second hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_secondary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 2<cost 2 .outer kind false true a b A B φ := by
  rw [threshold_value,outer_core_negative_positive hk hs]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end

section
/-!
## Physical-cycle adapters for the complete positive-core role-two row

The exact original owner is preserved, including ties.  Reflection
carries the literal role-two cost to role six.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=2 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=true) ∨
  (i=6 ∧ source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,rfl,hk,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl,rfl⟩
  · exact literal hk (by simpa [State] using hs) (by simpa [State,hk] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : CoreState a b := by simpa [State,hk] using hs
    have ht' : OuterState A B := by simpa [State] using ht
    have heq := margin_reflection j a b A B (-1) 1 φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) 1 φ := by
      norm_num at heq
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (2:Vertex) .outer source false true A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end

section
/-!
## Two global tangents for the positive outer target at role two

Each affine envelope follows from the strict concavity of the original
outer label.  Its fixed reference is enclosed directly by the physical
circle equation.  Both envelopes hold on the entire outer arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
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
    (fun y hy => (V_second_upper hy).le.trans (by norm_num))
  change V B≤V reference+VLabel.d1 reference*(B-reference) at hh
  have hp := mul_le_mul_of_nonneg_right tangent_reference.2.1.le hB.1
  have hδ := tangent_reference.1
  have hV := tangent_reference.2.2
  dsimp [reference,k] at *
  linarith

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
    (fun y hy => (V_second_upper hy).le.trans (by norm_num))
  change V B≤V 0+VLabel.d1 0*(B-0) at hh
  have hp := mul_le_mul_of_nonneg_right zero_first_upper.le hB.1
  linarith [V_zero_bounds.2]

lemma K_bounds : (1408657326/1000000000:ℝ)<K ∧ K<(1408657327/1000000000:ℝ) := by
  dsimp [K,c,g,p,k,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma radius_fine : (791515/400000:ℝ)<CommonQuarter.radius ∧ CommonQuarter.radius<(494697/250000:ℝ) := by
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
  have hh' : (MixedPrimarySupport.N g p 0)^2=612352949/400000000 := by
    rw [hh]; norm_num [g,p]
  constructor <;> nlinarith

lemma primary_zero : (13/100000:ℝ)<MixedPrimarySupport.minus g p K 0 := by
  have hRN := (mul_lt_mul_of_pos_left primary_norm_zero.2
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_fine.2
        (by norm_num : (0:ℝ)<15466104/12500000))
  rw [MixedPrimarySupport.minus_zero]
  have hg : g=103981/100000 := rfl
  linarith [K_bounds.1]

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end

section
/-!
## Complete primary supports for negative core to positive outer

The lower expression is positive by one square completion on the full
closed interval.  The upper expression is strictly concave there and
positive at its two endpoints.  No local enclosure is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic

lemma primary_gain :
    (359583/1000000:ℝ)<MixedPrimarySupport.gain g p ∧
      MixedPrimarySupport.gain g p<(44948/125000:ℝ) := by
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  constructor
  · apply (lt_div_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_fine.1
    have hN := primary_norm_zero.2
    norm_num [g,p] at *
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_fine.2
    have hN := primary_norm_zero.1
    norm_num [g,p] at *
    nlinarith

theorem lower_primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.minus g p K x := by
  apply MixedPrimarySupport.minus_positive
    (α := 6323/50000) (β := 1379/4000) (ε := 5059/20000)
    (by norm_num [g]) (by linarith [K_bounds.1])
  · linarith [K_bounds.2,primary_gain.1]
  · norm_num [g]
  · norm_num [g]
  · linarith [primary_zero]
  · norm_num [MixedPrimarySupport.linearCoefficient,g]
  · dsimp [MixedPrimarySupport.quadraticCoefficient]
    linarith [K_bounds.2,primary_gain.1]
  · have hgv : g=103981/100000 := rfl
    dsimp only [MixedPrimarySupport.cubicCoefficient]
    linarith [K_bounds.1,K_bounds.2,primary_gain.2]
  · norm_num
  · norm_num
  · exact hx

lemma upper_primary_concave :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (MixedPrimarySupport.plus g p K) := by
  apply MixedPrimarySupport.plus_concave
    (by norm_num [g]) (by linarith [K_bounds.1])
  · norm_num [g,p]
    linarith [radius_bounds.2,K_bounds.1]
  · norm_num [g,p]
    linarith [radius_bounds.2,K_bounds.2]

lemma upper_primary_right : (3/10:ℝ)<MixedPrimarySupport.plus g p K (7/10) := by
  have ht := cap_trig
  have hs : Real.sin (7/10)<(1289/2000:ℝ) := by linarith [ht.2.1]
  have hc : (1529/2000:ℝ)<Real.cos (7/10) ∧ Real.cos (7/10)<(153/200:ℝ) :=
    ⟨by linarith [ht.2.2.1],by linarith [ht.2.2.2]⟩
  have hn := MixedPrimarySupport.N_sq (p := p) (x := (7/10:ℝ))
    (show 0<g by norm_num [g])
  have hp := MixedPrimarySupport.N_positive (p := p) (x := (7/10:ℝ))
    (show 0<g by norm_num [g])
  have hN : MixedPrimarySupport.N g p (7/10)<(2319/2000:ℝ) := by
    have hh := pow_le_pow_left₀ (by linarith [hc.1] : 0≤Real.cos (7/10)) hc.2.le 2
    have hsq : (MixedPrimarySupport.N g p (7/10))^2<(2319/2000:ℝ)^2 := by
      rw [hn]
      norm_num [g,p] at hh ⊢
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<2319/2000))
  have hK : (2108657/1000000:ℝ)<K+7/10 := by linarith [K_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hc.1
    (by norm_num : (0:ℝ)<2108657/1000000)).trans
      (mul_lt_mul_of_pos_right hK (by linarith [hc.1] : 0<Real.cos (7/10)))
  dsimp only [MixedPrimarySupport.plus]
  simp only [g] at *
  linarith

theorem upper_primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.plus g p K x := by
  have hz : MixedPrimarySupport.plus g p K 0=MixedPrimarySupport.minus g p K 0 := by
    simp [MixedPrimarySupport.plus,MixedPrimarySupport.minus]
  exact concave_gt_of_endpoints upper_primary_concave hx
    (by rw [hz]; linarith [primary_zero]) (by linarith [upper_primary_right])

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end

section
/-!
## All transverse support ranges for the positive outer target

A stronger separator multiplier and the tangent at zero handle the
whole early contact range.  The later range uses the interior tangent.
Every range is controlled by strict concavity and its actual endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower)
open MixedTransverseSupport

def early (φ : ℝ) : ℝ := lower (7/5) (1061/1000) (-c+1449/100000) φ
def late (φ : ℝ) : ℝ := lower g p (-c-k) φ
def upperTransverse (x : ℝ) : ℝ := upper g p (-c-k) x

lemma early_left : (101/100:ℝ)<early 1 := by
  have ht := PointProducts.trig (show (0:ℝ)≤1 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (841/1000:ℝ)<Real.sin 1 := by linarith [ht.1.1]
  have hc : (27/50:ℝ)<Real.cos 1 := by linarith [ht.2.1]
  have hn := lower_sq (g := (7/5:ℝ)) (p := (1061/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) 1
  have hN : lowerN (7/5) (1061/1000) 1<(609/500:ℝ) := by
    have hsq : (lowerN (7/5) (1061/1000) 1)^2<(609/500:ℝ)^2 := by
      rw [hn]
      norm_num
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<609/500))
  dsimp only [early,lower,c]
  linarith

lemma early_right : (47/50:ℝ)<early (6/5) := by
  have ht := PointProducts.trig (show (0:ℝ)≤6/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (233/250:ℝ)<Real.sin (6/5) := by linarith [ht.1.1]
  have hc : (3623/10000:ℝ)<Real.cos (6/5) := by linarith [ht.2.1]
  have hn := lower_sq (g := (7/5:ℝ)) (p := (1061/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (6/5)
  have hN : lowerN (7/5) (1061/1000) (6/5)<(709/500:ℝ) := by
    have hsq : (lowerN (7/5) (1061/1000) (6/5))^2<(709/500:ℝ)^2 := by
      rw [hn]
      norm_num
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<709/500))
  dsimp only [early,lower,c]
  linarith

theorem early_lower {φ : ℝ} (hφ : φ∈Icc (1:ℝ) (6/5)) : (47/50:ℝ)<early φ := by
  have hc : ConcaveOn ℝ (Icc (1:ℝ) (6/5)) early :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt (by norm_num) (by norm_num) (by norm_num) (-c+1449/100000) x)
      (fun x _ => lowerD_hasDerivAt (by norm_num) (by norm_num) (by norm_num) x)
      (fun x hx => (lower_curvature (by norm_num) (by norm_num) (by norm_num)
        (show Lower x from ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
          by linarith [hx.2,pi_hand_enclosure.1]⟩)).le)
  exact concave_gt_of_endpoints hc hφ (by linarith [early_left]) early_right

lemma late_left : (9/10:ℝ)<late (6/5) := by
  have ht := PointProducts.trig (show (0:ℝ)≤6/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (93203/100000:ℝ)<Real.sin (6/5) := by linarith [ht.1.1]
  have hc : (7247/20000:ℝ)<Real.cos (6/5) := by linarith [ht.2.1]
  have hn := lower_sq (g := g) (p := p)
    (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (6/5)
  have hN : lowerN g p (6/5)<(101271/100000:ℝ) := by
    have hsq : (lowerN g p (6/5))^2<(101271/100000:ℝ)^2 := by
      rw [hn]
      norm_num [g,p]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<101271/100000))
  dsimp only [late,lower]
  simp only [c,g,p,k] at hRN ⊢
  linarith

lemma late_aligned : γ<late (Real.pi/2) := by
  have he : late (Real.pi/2)=γ+MixedPrimarySupport.minus g p K 0 := by
    simp [late,lower,lowerN,CircularNorm.norm,CircularNorm.energy,
      MixedPrimarySupport.minus,MixedPrimarySupport.N,K]
    ring
  rw [he]
  linarith [primary_zero]

theorem late_lower {φ : ℝ} (hφ : φ∈Icc (6/5:ℝ) (Real.pi/2)) : γ<late φ := by
  have hc : ConcaveOn ℝ (Icc (6/5:ℝ) (Real.pi/2)) late :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (-c-k) x)
      (fun x _ => lowerD_hasDerivAt (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) x)
      (fun x hx => (lower_curvature (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p])
        (show Lower x from ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],hx.2⟩)).le)
  exact concave_gt_of_endpoints hc hφ (by norm_num [γ]; linarith [late_left]) late_aligned

lemma upper_aligned : γ<upperTransverse 0 := by
  have he : upperTransverse 0=late (Real.pi/2) := by
    simp [upperTransverse,upper,upperN,late,lower,lowerN,CircularNorm.norm,CircularNorm.energy]
  rw [he]
  exact late_aligned

lemma upper_right : (69/50:ℝ)<upperTransverse (7/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (3221/5000:ℝ)<Real.sin (7/10) ∧ Real.sin (7/10)<(32211/50000:ℝ) :=
    ⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩
  have hc : (478/625:ℝ)<Real.cos (7/10) := by linarith [ht.2.1]
  have hn := upper_sq (g := g) (p := p)
    (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (7/10)
  have hN : upperN g p (7/10)<(15587/10000:ℝ) := by
    have hsq : (upperN g p (7/10))^2<(15587/10000:ℝ)^2 := by
      rw [hn]
      norm_num [g,p]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<15587/10000))
  dsimp only [upperTransverse,upper]
  simp only [c,g,p,k] at hRN ⊢
  linarith [pi_hand_enclosure.1]

theorem upper_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : γ<upperTransverse x :=
  concave_gt_of_endpoints
    (upper_concave (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (-c-k))
    hx upper_aligned (by norm_num [γ]; linarith [upper_right])

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end

section
/-!
## Original weak-owner joins for negative core to positive outer

The separator multiplier in the early transverse case is paid for by
the nonnegative original core coordinate.  The primary case retains
the actual core side or corner; the lower corner is geometrically
impossible.  No point or radius is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

lemma core_transverse_upper {a b : ℝ} (hs : CoreState a b) : b<(559/1000:ℝ) :=
  (CoreAngleEndpoint.state_bounds hs).2.2.2.2.trans_lt
    (by linarith [CoreAngleEndpoint.diagonal_bounds.2])

lemma first_angle_lower {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    (1:ℝ)<φ := by
  by_contra hn
  have htr := lower_trig hφ
  have href : Lower (1:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have htaylor := PointProducts.trig (show (0:ℝ)≤1 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at htaylor
  have hsin : Real.sin φ<(1683/2000:ℝ) :=
    (PositiveThree.lower_sin_monotone hφ href (le_of_not_gt hn)).trans_lt
      (by linarith [htaylor.1.2])
  have hcos : (5403/10000:ℝ)<Real.cos φ :=
    (show (5403/10000:ℝ)<Real.cos 1 by linarith [htaylor.2.1]).trans_le
      (PositiveThree.lower_cos_antitone hφ href (le_of_not_gt hn))
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2
    (by linarith [htr.1] : 0≤Real.sin φ)
  have hB := mul_nonneg ht.1 htr.2.2.1
  have hκ := (mul_lt_mul_of_pos_right MixedAffine.κ_bounds.2
    (by linarith [htr.1] : 0<Real.sin φ)).trans
      (mul_lt_mul_of_pos_left hsin (by norm_num : (0:ℝ)<183/200))
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  dsimp [MixedAffine.κ] at hκ
  nlinarith

lemma first_support {a b A B φ lam q η : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hlam : 0≤lam) (hglam : g≤lam) (henv : V B≤η+q*B)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    MixedTransverseSupport.lower lam q (-c-η) φ≤value b B φ := by
  have hsupp := outer_circle_lower (X := -lam*Real.sin φ) (Y := lam*Real.cos φ-q) ht
  have he : Real.sqrt ((-lam*Real.sin φ)^2+(lam*Real.cos φ-q)^2)=
      MixedTransverseSupport.lowerN lam q φ := by
    dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lam^2*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep hlam
  have hpaid := mul_nonneg (sub_nonneg.mpr hglam) (CoreAngleEndpoint.state_bounds hs).2.2.1
  dsimp [MixedTransverseSupport.lower,value]
  nlinarith

theorem lower_first {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    γ<value b B φ := by
  by_cases hearly : φ≤6/5
  · have hh := first_support hs ht (lam := (7/5:ℝ)) (q := (1061/1000:ℝ))
      (η := (-1449/100000:ℝ)) (by norm_num) (by norm_num [g])
      (zero_tangent_upper (NegativeTwo.source_mem ht)) hsep
    rw [show (-c - -1449/100000:ℝ)=-c+1449/100000 by ring] at hh
    have hl := early_lower ⟨(first_angle_lower hs ht hφ hsep).le,hearly⟩
    change early φ≤value b B φ at hh
    norm_num [γ]
    linarith
  · have hh := first_support hs ht (lam := g) (q := p) (η := k)
      (by norm_num [g]) le_rfl (tangent_upper (NegativeTwo.source_mem ht)) hsep
    exact (late_lower ⟨by linarith,hφ.2⟩).trans_le hh

theorem lower_primary {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -a*Real.cos φ-b*Real.sin φ+A) :
    γ<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have ha : a=(7/12:ℝ) := by
    rcases hs with ⟨rfl,_,_⟩ | ⟨hb,hba,_⟩
    · rfl
    · have hac := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤a by linarith) htr.2.2.1
      have hbs := mul_le_mul_of_nonneg_right hb hsine.le
      have hA := (NegativeTwo.primary_mem ht).2
      have ha0 := outer_endpoint_bounds.2.1
      exfalso
      linarith [htr.2.2.2.2]
  rw [ha] at hsep
  have hV := mul_le_mul_of_nonneg_right (tangent_upper (NegativeTwo.source_mem ht)) hsine.le
  have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.sin φ) ht
  have he : Real.sqrt ((-g)^2+(-p*Real.sin φ)^2)=
      Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by congr 1; ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hpos := lower_primary_positive (lower_deviation hφ)
  have heq : MixedPrimarySupport.minus g p K (Real.pi/2-φ)=
      (φ-c-k+(g+p)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
        CommonQuarter.radius*Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
    simp only [MixedPrimarySupport.minus,MixedPrimarySupport.N,K,
      Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
      zero_mul,one_mul,sub_zero,zero_add]
    ring
  rw [heq] at hpos
  have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
    dsimp only [value]
    linarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
  linarith

theorem upper_first {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+B*Real.sin x) :
    γ<value b B (Real.pi/2+x) := by
  have hV := tangent_upper (NegativeTwo.source_mem ht)
  have hsupp := outer_circle_lower (X := -g*Real.cos x) (Y := -g*Real.sin x-p) ht
  have he : Real.sqrt ((-g*Real.cos x)^2+(-g*Real.sin x-p)^2)=
      MixedTransverseSupport.upperN g p x := by
    dsimp [MixedTransverseSupport.upperN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hh := upper_lower hx
  dsimp [upperTransverse,MixedTransverseSupport.upper,value] at *
  nlinarith

theorem upper_primary {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have ha := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds hs).2.1 htr.2.2.1
  have hV := mul_le_mul_of_nonneg_right (tangent_upper (NegativeTwo.source_mem ht)) hcos.le
  have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.cos x) ht
  have he : Real.sqrt ((-g)^2+(-p*Real.cos x)^2)=MixedPrimarySupport.N g p x := by
    dsimp [MixedPrimarySupport.N]
    congr 1
    ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hcore := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤g by norm_num [g])
  have hpos := upper_primary_positive hx
  have hpositive : 0<(value b B (Real.pi/2+x)-γ)*Real.cos x := by
    dsimp [MixedPrimarySupport.plus,K,value] at *
    nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg
    (show value b B (Real.pi/2+x)-γ≤0 by linarith) hcos.le
  linarith

lemma late_value {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : (213/100:ℝ)≤φ) : γ<value b B φ := by
  have hV := (V_monotone (NegativeTwo.source_mem ht)
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)
    (NegativeTwo.source_mem ht).2).trans_lt V_diagonal_bounds.2
  have hb := core_transverse_upper hs
  dsimp [value,c,g,γ]
  linarith

theorem upper_fourth {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) := by
  by_cases hlate : (213/100:ℝ)≤Real.pi/2+x
  · exact late_value hs ht hlate
  have htr := positive_trig hx
  have ha := (CoreAngleEndpoint.state_bounds hs).2.1
  have hA : A<(283/200:ℝ) := (NegativeTwo.primary_mem ht).2.trans_lt outer_endpoint_bounds.2.1
  have hAs := mul_le_mul_of_nonneg_right hA.le htr.2.2.1
  have hBc := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.cos x)
  have hxlo : (2/5:ℝ)<x := by
    by_contra hn
    have hsin : Real.sin x≤(2/5:ℝ) := htr.2.2.2.2.1.trans (le_of_not_gt hn)
    have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
    have hcos : (229/250:ℝ)<Real.cos x := by
      by_contra hc
      have hcc := mul_le_mul (le_of_not_gt hc) (le_of_not_gt hc) (by linarith [htr.1])
        (by norm_num : (0:ℝ)≤229/250)
      linarith [Real.sin_sq_add_cos_sq x]
    linarith
  have hxhi : x<(14/25:ℝ) := by linarith [pi_hand_enclosure.1]
  have hsin : Real.sin x≤(14/25:ℝ) := htr.2.2.2.2.1.trans hxhi.le
  have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
  have hcos : (207/250:ℝ)<Real.cos x := by
    by_contra hc
    have hcc := mul_le_mul (le_of_not_gt hc) (le_of_not_gt hc) (by linarith [htr.1])
      (by norm_num : (0:ℝ)≤207/250)
    linarith [Real.sin_sq_add_cos_sq x]
  have hB : B<(23/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hcos.le ht.1
    linarith
  have hV := zero_tangent_upper (NegativeTwo.source_mem ht)
  have hb := core_transverse_upper hs
  dsimp [value,c,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end

section
/-!
## The negative-core to positive-outer role-two family

Every original weak axis is covered on both closed quarter halves (`original`, `literal`). The
transverse core support excludes the third owner directly; the other owners use the whole-angle
supports or the direct late bound. Both physical core pieces are covered.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hrad := core_radius_sq hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · apply lower_first hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have hlarge : 1≤a*Real.sin φ-b*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [ht.1]
      have he : (a*Real.sin φ-b*Real.cos φ)^2+
          (a*Real.cos φ+b*Real.sin φ)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (a*Real.cos φ+b*Real.sin φ)]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · apply upper_first ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · have hlarge : 1≤a*Real.cos x+b*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [ht.1]
      have he : (a*Real.cos x+b*Real.sin x)^2+
          (a*Real.sin x-b*Real.cos x)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (a*Real.sin x-b*Real.cos x)]
    · apply upper_fourth hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 2<cost 2 kind .outer false true a b A B φ := by
  rw [threshold_value,core_outer_negative_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=2 ∧ source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=true) ∨
  (i=6 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,hk,rfl,rfl,rfl⟩ | ⟨rfl,rfl,hk,rfl,rfl⟩
  · exact literal hk (by simpa [State,hk] using hs) (by simpa [State] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : OuterState a b := by simpa [State] using hs
    have ht' : CoreState A B := by simpa [State,hk] using ht
    have heq := margin_reflection j a b A B (-1) 1 φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) 1 φ := by
      norm_num at heq
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (2:Vertex) target .outer false true A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
end
end
end
