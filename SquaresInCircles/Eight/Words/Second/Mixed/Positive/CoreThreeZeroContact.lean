module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeSupport
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.ZeroCurve
public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoDiagonalReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: original-point closure of the early primary owner

Feasibility supplies the physical lower angle and places the original
source below the zero-contact transverse coordinate. The relaxed cost
comparison therefore applies on its proved domain, including the weak
owner boundary.
-/

section
/-!
## Primary T-label growth on the whole early zero-contact height range

One rational height reference, followed by derivative monotonicity,
proves that the second derivative exceeds twice the first derivative.
This supplies both the contact cost curvature and the boundary slope
comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma primary_second_monotone :
    MonotoneOn TPrimaryLabel.d2 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (TPrimaryLabel.d2_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => TPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (NegativeThree.primary_third_positive (Ioo_subset_Icc_self ha)).le)

lemma primary_first_monotone : MonotoneOn TPrimaryLabel.d1 (Icc (1:ℝ) outerAxial) := by
  have hdom {a : ℝ} (ha : a∈Icc (1:ℝ) outerAxial) : a∈Icc outerDiagonal outerAxial :=
    ⟨primary_one_mem.1.trans ha.1,ha.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun a ha => (TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ha))).continuousAt.continuousWithinAt)
    (fun a ha => TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha))))
  intro a ha
  have hh := primary_second_monotone primary_one_mem
    (hdom (Ioo_subset_Icc_self ha)) ha.1.le
  linarith [NegativeThree.primary_one_references.2.2.1]

lemma primary_growth_reference :
    (981/1000:ℝ)<TPrimaryLabel.d1 (147/125) ∧
    TPrimaryLabel.d1 (147/125)<(491/500:ℝ) ∧
    (64/25:ℝ)<TPrimaryLabel.d2 (147/125) := by
  have ha : (147/125:ℝ)∈Icc outerDiagonal outerAxial := by
    constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]
  have h1 := TPrimaryLabel.first_chart_reference (primary_domain ha)
    (l := (105196197649/100000000000:ℝ)) (u := (2103923953/2000000000:ℝ))
    (dlo := (981/1000:ℝ)) (dhi := (491/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  have h2 := TPrimaryLabel.second_chart_reference (primary_domain ha)
    (l := (105196197649/100000000000:ℝ)) (u := (2103923953/2000000000:ℝ))
    (dlo := (64/25:ℝ)) (dhi := (257/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact ⟨h1.1,h1.2,h2.1⟩

lemma primary_growth {a : ℝ} (ha : a∈Icc (147/125:ℝ) outerAxial) :
    (981/1000:ℝ)<TPrimaryLabel.d1 a ∧ 2*TPrimaryLabel.d1 a<TPrimaryLabel.d2 a := by
  have hdom {a : ℝ} (ha : a∈Icc (147/125:ℝ) outerAxial) : a∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.2],ha.2⟩
  have hr : (147/125:ℝ)∈Icc (147/125:ℝ) outerAxial :=
    ⟨le_rfl,by linarith [outer_endpoint_bounds.1]⟩
  have hm : MonotoneOn (fun a => TPrimaryLabel.d2 a-2*TPrimaryLabel.d1 a)
      (Icc (147/125:ℝ) outerAxial) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a ha => ((TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom ha))).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ha))).const_mul 2)).continuousAt.continuousWithinAt)
      (fun a ha => (TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha)))).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha)))).const_mul 2))
      (fun a ha => (NegativeThree.primary_growth_one (hdom (Ioo_subset_Icc_self ha))).le)
  have hh := hm hr ha ha.1
  have hf := primary_first_monotone
    (show (147/125:ℝ)∈Icc (1:ℝ) outerAxial from ⟨by norm_num,hr.2⟩)
    (show a∈Icc (1:ℝ) outerAxial from ⟨by linarith [ha.1],ha.2⟩) ha.1
  exact ⟨primary_growth_reference.1.trans_le hf,by
    linarith [primary_growth_reference.2.1,primary_growth_reference.2.2]⟩

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
/-!
## The complete early primary zero-contact curve

Both endpoint trigonometric bounds are rational Taylor consequences.
They place the entire harmonic-height curve on the original outer
circle and within the range of the primary T-label growth estimate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

abbrev m := PrimaryZero.m
abbrev v := PrimaryZero.v
abbrev U := PrimaryZero.U
abbrev V := PrimaryZero.V
abbrev b := PrimaryZero.b
def a (φ : ℝ) : ℝ := U φ-1/2
def angles : Set ℝ := Icc (57/50) (7/5)
def K (φ : ℝ) : ℝ := φ-c+TPrimaryLabel.outer (a φ)
def KD (φ : ℝ) : ℝ := 1-TPrimaryLabel.d1 (a φ)*v φ
def KDD (φ : ℝ) : ℝ := TPrimaryLabel.d2 (a φ)*(v φ)^2-TPrimaryLabel.d1 (a φ)*m φ

lemma initial_trig :
    (90863349/100000000:ℝ)<Real.sin (57/50) ∧ Real.sin (57/50)<90863350/100000000 ∧
    (41759450/100000000:ℝ)<Real.cos (57/50) ∧ Real.cos (57/50)<41759451/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (57/50:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (57/50:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (57/50:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (57/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨by dsimp [angles] at hφ; dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],
    by dsimp [angles] at hφ; linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    (227/250:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<(209/500:ℝ) := by
  have hi : (57/50:ℝ)∈angles := by norm_num [angles]
  have hs := PositiveThree.lower_sin_monotone (lower_mem hi) (lower_mem hφ) hφ.1
  have hc := PositiveThree.lower_cos_antitone (lower_mem hi) (lower_mem hφ) hφ.1
  exact ⟨by linarith [initial_trig.1],Real.sin_le_one φ,(lower_trig (lower_mem hφ)).2.2.1,
    by linarith [initial_trig.2.2.2]⟩

lemma harmonic_bounds {φ : ℝ} (hφ : φ∈angles) :
    (169/250:ℝ)< m φ ∧ m φ<(907/1000:ℝ) ∧
    (31/40:ℝ)<v φ ∧ v φ<(983/1000:ℝ) := by
  have hm : AntitoneOn m angles := by
    apply antiOn_of_hasDeriv_nonpos
      (fun φ _ => (PrimaryZero.m_hasDerivAt φ).continuousAt.continuousWithinAt)
      (fun φ _ => PrimaryZero.m_hasDerivAt φ)
    intro φ hφ
    have ht := trig (Ioo_subset_Icc_self hφ)
    dsimp [v,PrimaryZero.v]
    linarith [ht.1,ht.2.2.2]
  have hv : MonotoneOn v angles := by
    apply monoOn_of_hasDeriv_nonneg
      (fun φ _ => (PrimaryZero.v_hasDerivAt φ).continuousAt.continuousWithinAt)
      (fun φ _ => PrimaryZero.v_hasDerivAt φ)
    intro φ hφ
    have ht := trig (Ioo_subset_Icc_self hφ)
    dsimp [m,PrimaryZero.m]
    linarith [ht.1,ht.2.2.1]
  have hi : (57/50:ℝ)∈angles := by norm_num [angles]
  have he : (7/5:ℝ)∈angles := by norm_num [angles]
  have hml := hm hφ he hφ.2
  have hmu := hm hi hφ hφ.1
  have hvl := hv hi hφ hφ.1
  have hvu := hv hφ he hφ.2
  have ht := PrimaryZero.terminal_trig
  dsimp [m,PrimaryZero.m,v,PrimaryZero.v] at hml hmu hvl hvu ⊢
  exact ⟨by linarith [ht.1,ht.2.2.1],by linarith [initial_trig.2.1,initial_trig.2.2.2],
    by linarith [initial_trig.1,initial_trig.2.2.2],by linarith [ht.2.1,ht.2.2.1]⟩

lemma U_bounds {φ : ℝ} (hφ : φ∈angles) : (419/250:ℝ)<U φ ∧ U φ<(1907/1000:ℝ) := by
  dsimp [U,PrimaryZero.U]
  exact ⟨by linarith [(harmonic_bounds hφ).1],by linarith [(harmonic_bounds hφ).2.1]⟩

lemma domain {φ : ℝ} (hφ : φ∈angles) : 0<Q0-(U φ)^2 := by
  have hh := U_bounds hφ
  have hp := pow_le_pow_left₀ (by linarith [hh.1] : 0≤U φ) hh.2.le 2
  norm_num [Q0]
  nlinarith

lemma V_bounds {φ : ℝ} (hφ : φ∈angles) : (1/2:ℝ)<V φ ∧ V φ<(1052/1000:ℝ) := by
  have he : (V φ)^2=Q0-(U φ)^2 := HeightLabel.root_sq (domain hφ)
  have hp : 0<V φ := HeightLabel.root_pos (domain hφ)
  have hh := U_bounds hφ
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤419/250) hh.1.le 2
  have hhi := pow_le_pow_left₀ (by linarith [hh.1] : 0≤U φ) hh.2.le 2
  norm_num [Q0] at he
  constructor <;> nlinarith

lemma physical {φ : ℝ} (hφ : φ∈angles) : OuterState (a φ) (b φ) := by
  have hh := U_bounds hφ
  have hv := V_bounds hφ
  have hc : (V φ)^2=Q0-(U φ)^2 := HeightLabel.root_sq (domain hφ)
  dsimp [OuterState,a,b,PrimaryZero.b]
  exact ⟨by linarith,by linarith,by nlinarith only [hc]⟩

lemma primary_mem {φ : ℝ} (hφ : φ∈angles) : a φ∈Icc (147/125:ℝ) outerAxial :=
  ⟨by dsimp [a]; linarith [(U_bounds hφ).1],(NegativeTwo.primary_mem (physical hφ)).2⟩

lemma source_mem {φ : ℝ} (hφ : φ∈angles) : b φ∈Icc (0:ℝ) (3/5) := by
  have hh := V_bounds hφ
  dsimp [b,PrimaryZero.b]
  exact ⟨by linarith,by linarith⟩

lemma a_hasDerivAt (φ : ℝ) : HasDerivAt a (-v φ) φ :=
  (PrimaryZero.U_hasDerivAt φ).sub_const (1/2)

lemma K_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt K (KD φ) φ := by
  have hT := TPrimaryLabel.outer_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hT.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.outer (a x)) (TPrimaryLabel.d1 (a φ)*-v φ) φ := hc0
  have h := ((hasDerivAt_id' φ).sub_const c).add hc
  exact h.congr_deriv (by simp only [KD]; ring)

lemma KD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KD (KDD φ) φ := by
  have hD := TPrimaryLabel.d1_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hD.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.d1 (a x)) (TPrimaryLabel.d2 (a φ)*-v φ) φ := hc0
  have h := (hc.mul (PrimaryZero.v_hasDerivAt φ)).const_sub 1
  exact h.congr_deriv (by simp only [KDD]; ring)

lemma KDD_lower {φ : ℝ} (hφ : φ∈angles) : (7/25:ℝ)<KDD φ := by
  have hh := harmonic_bounds hφ
  have hg := primary_growth (primary_mem hφ)
  have hs : (31/40:ℝ)^2<(v φ)^2 := by nlinarith [hh.2.2.1]
  have hp := mul_lt_mul_of_pos_right hg.2 (sq_pos_of_pos (by linarith [hh.2.2.1] : 0<v φ))
  have hq := mul_pos (show 0<TPrimaryLabel.d1 (a φ) by linarith [hg.1])
    (show 0<2*(v φ)^2-m φ-(1177/4000:ℝ) by nlinarith [hh.2.1])
  dsimp [KDD]
  nlinarith [hg.1]

lemma cost_eq {φ : ℝ} (hφ : φ∈angles) : K φ=φ-c-T (b φ) := by
  dsimp [K]
  rw [NegativeThree.primary_actual (physical hφ)]
  ring

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
end
end
end

section
/-!
## One exact reference for the interior primary-contact minimum

The reference angle is rational. Taylor inequalities enclose its
harmonic height, and two squared rational radical cages control the
primary label and its first derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
open CommonQuarter CorePairGeometry Arithmetic

def reference : ℝ := 345759/250000
def aL : ℝ := 23868527/20000000
def aU : ℝ := 29835659/25000000

lemma reference_mem : reference∈angles := by norm_num [reference,angles]
lemma aL_mem : aL∈Icc outerDiagonal outerAxial := by
  constructor <;> dsimp [aL] <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]
lemma aU_mem : aU∈Icc outerDiagonal outerAxial := by
  constructor <;> dsimp [aU] <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma reference_trig :
    (9824247540/10000000000:ℝ)<Real.sin reference ∧ Real.sin reference<9824247541/10000000000 ∧
    (1866590545/10000000000:ℝ)<Real.cos reference ∧ Real.cos reference<1866590547/10000000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := reference) (by norm_num [reference])
  have hsU := HighOrderTaylor.sin_le_S17 (x := reference) (by norm_num [reference])
  have hc := HighOrderTaylor.C14_le_cos (x := reference) (by norm_num [reference])
  have hcU := HighOrderTaylor.cos_le_C16 (x := reference) (by norm_num [reference])
  norm_num [reference,HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S11,
    HighOrderTaylor.S13,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8] at hs hsU hc hcU
  simp only [reference]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates :
    aL<a reference ∧ a reference<aU ∧
    (9709639/10000000:ℝ)<v reference ∧ v reference<(242741/250000:ℝ) := by
  dsimp [a,aL,aU,U,PrimaryZero.U,PrimaryZero.m,v,PrimaryZero.v]
  exact ⟨by linarith [reference_trig.1,reference_trig.2.2.1],
    by linarith [reference_trig.2.1,reference_trig.2.2.2],
    by linarith [reference_trig.1,reference_trig.2.2.2],
    by linarith [reference_trig.2.1,reference_trig.2.2.1]⟩

lemma reference_value : -(43555943/100000000:ℝ)<TPrimaryLabel.outer aL := by
  have hr := shifted_chart_reference (primary_domain aL_mem)
    (l := (102367338400/100000000000:ℝ)) (u := (102367338401/100000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [aL,W,Q0]) (by norm_num [aL,W,Q0])
  dsimp [SecondWord.U,aL] at hr
  norm_num [TPrimaryLabel,RoleLabel.primary,RoleLabel.outer,RoleLabel.eval,TLabel,aL,Q0]
  nlinarith [hr.2]

lemma reference_slopes :
    (10299/10000:ℝ)<TPrimaryLabel.d1 aL ∧ TPrimaryLabel.d1 aU<(102991/100000:ℝ) := by
  constructor
  · have hh := TPrimaryLabel.first_chart_reference (primary_domain aL_mem)
      (l := (102367338400/100000000000:ℝ)) (u := (102367338401/100000000000:ℝ))
      (dlo := (10299/10000:ℝ)) (dhi := (102991/100000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [aL,W,Q0]) (by norm_num [aL,W,Q0])
      (by norm_num [aL,TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
      (by norm_num [aL,TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    exact hh.1
  · have hh := TPrimaryLabel.first_chart_reference (primary_domain aU_mem)
      (l := (102367336746/100000000000:ℝ)) (u := (102367336747/100000000000:ℝ))
      (dlo := (10299/10000:ℝ)) (dhi := (102991/100000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [aU,W,Q0]) (by norm_num [aU,W,Q0])
      (by norm_num [aU,TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
      (by norm_num [aU,TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    exact hh.2

lemma reference_cost : (112222/125000:ℝ)<K reference ∧ |KD reference|<(1/100000:ℝ) := by
  have hh := reference_coordinates
  have ha := NegativeTwo.primary_mem (physical reference_mem)
  have hm := NegativeThree.primary_monotone aL_mem ha hh.1.le
  have hl := primary_first_monotone
    (show aL∈Icc (1:ℝ) outerAxial from ⟨by norm_num [aL],aL_mem.2⟩)
    (show a reference∈Icc (1:ℝ) outerAxial from ⟨by dsimp [aL] at hh; linarith [hh.1],ha.2⟩) hh.1.le
  have hu := primary_first_monotone
    (show a reference∈Icc (1:ℝ) outerAxial from ⟨by dsimp [aL] at hh; linarith [hh.1],ha.2⟩)
    (show aU∈Icc (1:ℝ) outerAxial from ⟨by norm_num [aU],aU_mem.2⟩) hh.2.1.le
  have hd : (10299/10000:ℝ)<TPrimaryLabel.d1 (a reference) ∧
      TPrimaryLabel.d1 (a reference)<(102991/100000:ℝ) :=
    ⟨reference_slopes.1.trans_le hl,hu.trans_lt reference_slopes.2⟩
  have hlo := mul_le_mul hd.1.le hh.2.2.1.le (by norm_num : (0:ℝ)≤9709639/10000000)
    (by linarith [hd.1] : 0≤TPrimaryLabel.d1 (a reference))
  have hhi := mul_le_mul hd.2.le hh.2.2.2.le
    (by linarith [hh.2.2.1] : 0≤v reference) (by norm_num : (0:ℝ)≤102991/100000)
  constructor
  · have hr : reference=345759/250000 := rfl
    have hc : c=497/10000 := rfl
    dsimp only [K]
    linarith [reference_value]
  · rw [abs_lt]
    dsimp only [KD]
    constructor <;> linarith

theorem cost_lower {φ : ℝ} (hφ : φ∈angles) : γ<K φ := by
  have ht := curvature_tangent (f := K) (d := KD) (dd := KDD) (κ := (7/25:ℝ))
    hφ reference_mem (fun _ hx => K_hasDerivAt hx) (fun _ hx => KD_hasDerivAt hx)
    (fun _ hx => (KDD_lower hx).le)
  have hd := abs_lt.mp reference_cost.2
  have hs : (KD reference)^2<(1/100000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((7/25)*(φ-reference)+KD reference)
  dsimp [γ]
  nlinarith [reference_cost.1]

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
end
end
end

section
/-!
## The complete primary zero-boundary slope comparison

The product of the primary label slope and sine decreases on the
entire contact interval. Its terminal lower bound makes the relaxed
contact cost decrease in the original transverse coordinate up to
the zero boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def product (φ : ℝ) : ℝ := TPrimaryLabel.d1 (a φ)*Real.sin φ

lemma product_hasDerivAt {φ : ℝ} (hφ : φ∈angles) :
    HasDerivAt product (-TPrimaryLabel.d2 (a φ)*v φ*Real.sin φ+
      TPrimaryLabel.d1 (a φ)*Real.cos φ) φ := by
  have hD := TPrimaryLabel.d1_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hD.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.d1 (a x)) (TPrimaryLabel.d2 (a φ)*-v φ) φ := hc0
  have h := hc.mul (Real.hasDerivAt_sin φ)
  exact h.congr_deriv (by ring)

lemma product_antitone : AntitoneOn product angles := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ hφ => (product_hasDerivAt hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => product_hasDerivAt (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have h := Ioo_subset_Icc_self hφ
  have hg := primary_growth (primary_mem h)
  have ht := trig h
  have hv := harmonic_bounds h
  have hvs : (7037/10000:ℝ)≤v φ*Real.sin φ := by
    have hh := mul_le_mul hv.2.2.1.le ht.1.le (by norm_num : (0:ℝ)≤227/250)
      (by linarith [hv.2.2.1] : 0≤v φ)
    linarith
  have hp := mul_lt_mul_of_pos_right hg.2 (by linarith : 0<v φ*Real.sin φ)
  have hq := mul_neg_of_pos_of_neg (show 0<TPrimaryLabel.d1 (a φ) by linarith [hg.1])
    (show Real.cos φ-2*(v φ*Real.sin φ)<0 by linarith [ht.2.2.2])
  nlinarith

lemma product_lower {φ : ℝ} (hφ : φ∈angles) : g<product φ := by
  have he : (7/5:ℝ)∈angles := by norm_num [angles]
  have hm := product_antitone hφ he hφ.2
  have hg := primary_growth (primary_mem he)
  have hp := mul_le_mul hg.1.le PrimaryZero.terminal_trig.1
    (by norm_num : (0:ℝ)≤123181215/125000000)
    (by linarith [hg.1] : 0≤TPrimaryLabel.d1 (a (7/5)))
  dsimp [product,g] at *
  linarith

def contactD (φ y : ℝ) : ℝ := g*ratio y/Real.sin φ-TLabel.d1 y

lemma contact_hasDerivAt {φ y : ℝ} (_hφ : φ∈angles) (hy : y∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => primaryContact y φ) (contactD φ y) y := by
  have hT : HasDerivAt T (TLabel.d1 y) y := TLabel.outer_hasDerivAt (outer_domain hy)
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hy)).sub_const (1/2)).sub_const
    ((13/12)*Real.cos φ)).div_const (Real.sin φ)).sub_const (1/2)
  have h := (hT.const_sub (φ-c)).sub (hd.const_mul g)
  exact h.congr_deriv (by simp only [contactD]; ring)

lemma contactD_monotone {φ : ℝ} (hφ : φ∈angles) :
    MonotoneOn (contactD φ) (Icc (0:ℝ) (b φ)) := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans (NegativeTwo.source_mem (physical hφ)).2⟩
  have hd {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) :
      HasDerivAt (contactD φ) (g*ratioD y/Real.sin φ-TLabel.d2 y) y := by
    have h := (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (hdom hy))).const_mul
      g).div_const (Real.sin φ)).sub (TLabel.d1_hasDerivAt (outer_domain (hdom hy)))
    exact h
  apply monoOn_of_hasDeriv_nonneg (fun y hy => (hd hy).continuousAt.continuousWithinAt)
    (fun y hy => hd (Ioo_subset_Icc_self hy))
  intro y hy
  have hr := ShortOuterOne.SameContact.ratioD_pos (outer_domain (hdom (Ioo_subset_Icc_self hy)))
  have hT := MixedTSmall.concave_second
    (show y∈Icc (0:ℝ) (3/5) from ⟨hy.1.le,hy.2.le.trans (source_mem hφ).2⟩)
  have hp := div_pos (mul_pos (show 0<g by norm_num [g]) hr)
    (show 0<Real.sin φ by linarith [(trig hφ).1])
  linarith

lemma contactD_boundary {φ : ℝ} (hφ : φ∈angles) : contactD φ (b φ)<0 := by
  have hs := physical hφ
  have ht := trig hφ
  have hr : 0<ratio (b φ) := by
    dsimp [ratio]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    exact div_pos (by linarith [hs.1]) (by linarith [hs.1,hs.2.1])
  have he := NegativeThree.primary_first_exchange hs
  have hd : g/Real.sin φ<TPrimaryLabel.d1 (a φ) :=
    (div_lt_iff₀ (show 0<Real.sin φ by linarith [ht.1])).2 (product_lower hφ)
  have hp := mul_lt_mul_of_pos_right hd hr
  have hq : g*ratio (b φ)/Real.sin φ=g/Real.sin φ*ratio (b φ) := by ring
  dsimp only [contactD]
  rw [←he,hq]
  linarith

lemma contact_antitone {φ : ℝ} (hφ : φ∈angles) :
    AntitoneOn (fun y => primaryContact y φ) (Icc (0:ℝ) (b φ)) := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (b φ)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans (NegativeTwo.source_mem (physical hφ)).2⟩
  apply antiOn_of_hasDeriv_nonpos
    (fun y hy => (contact_hasDerivAt hφ (hdom hy)).continuousAt.continuousWithinAt)
    (fun y hy => contact_hasDerivAt hφ (hdom (Ioo_subset_Icc_self hy)))
  intro y hy
  have hm := contactD_monotone hφ (Ioo_subset_Icc_self hy)
    (show b φ∈Icc (0:ℝ) (b φ) from ⟨(source_mem hφ).1,le_rfl⟩) hy.2.le
  exact hm.trans (contactD_boundary hφ).le

lemma boundary_identity {φ : ℝ} (hφ : φ∈angles) : primaryContact (b φ) φ=K φ := by
  have hs := physical hφ
  have he := (ShortOuterOne.SameContact.actual_arc hs).1
  have hp : primaryCut (a φ) φ=0 := by
    dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut,a,U,PrimaryZero.U,PrimaryZero.m]
    field_simp [ne_of_gt (show 0<Real.sin φ by linarith [(trig hφ).1])]
    ring
  dsimp [primaryContact]
  rw [he,hp,cost_eq hφ]
  ring

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma zeroHeight_antitone : AntitoneOn PrimaryZero.U (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ _ => (PrimaryZero.U_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => PrimaryZero.U_hasDerivAt φ)
  intro φ hφ
  have hh := lower_trig (Ioo_subset_Icc_self hφ)
  dsimp [PrimaryZero.v]
  linarith [hh.1,hh.2.2.2.1]

lemma preinitial_height : (961/500:ℝ)<PrimaryZero.U (28/25) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (28/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (28/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  dsimp [PrimaryZero.U,PrimaryZero.m]
  linarith

lemma early_primary {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B)
    (hφ : Lower φ) (hφu : φ≤7/5)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-(7/12)*Real.cos φ-B*Real.sin φ) :
    γ<value b B φ := by
  have ht := lower_trig hφ
  have hsin : 0<Real.sin φ := by linarith [ht.1]
  have hBsin := mul_nonneg hB hsin.le
  have hheight : PrimaryZero.U φ-1/2≤a := by
    dsimp [PrimaryZero.U,PrimaryZero.m]
    linarith
  have ha : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have h28 : Lower (28/25:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have h57 : Lower (57/50:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have hlo : (28/25:ℝ)<φ := by
    by_contra hn
    have hm := zeroHeight_antitone hφ h28 (le_of_not_gt hn)
    linarith [preinitial_height]
  by_cases he : φ≤57/50
  · have hm := zeroHeight_antitone hφ h57 he
    have hi : (19/10:ℝ)<PrimaryZero.U (57/50) := by
      dsimp [PrimaryZero.U,PrimaryZero.m]
      linarith [Zero.initial_trig.1,Zero.initial_trig.2.2.1]
    have haL : (7/5:ℝ)<a := by linarith
    have hb : b<(27/500:ℝ) := by
      have hc := hs.2.2
      norm_num [Q0] at hc
      have h1 : (19/10:ℝ)^2≤(a+1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      by_contra hn
      have h2 : (277/500:ℝ)^2≤(b+1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      norm_num at h1 h2
      linarith
    have hBhi : B<(1/50:ℝ) := by
      have hweight := mul_le_mul_of_nonneg_left ht.1.le hB
      have hcut : B*Real.sin φ≤a-(PrimaryZero.U φ-1/2) := by
        dsimp [PrimaryZero.U,PrimaryZero.m]
        linarith
      linarith
    have hT := T_increment_upper (by constructor <;> linarith [fine_outer_endpoint_bounds.2] :
      (0:ℝ)∈Icc 0 outerDiagonal) (NegativeTwo.source_mem hs) hs.1
    have hz : T 0=(167/10000:ℝ) := by norm_num [T,RoleLabel.outer,RoleLabel.eval,TLabel]
    rw [hz] at hT
    dsimp [value,c,g,γ]
    linarith
  · have hz : φ∈Zero.angles := ⟨by linarith,hφu⟩
    have hzstate := Zero.physical hz
    have hab : Zero.a φ≤a := hheight
    have hb : b≤Zero.b φ := by
      have hc := hs.2.2
      have hc0 := hzstate.2.2
      have hsq := pow_le_pow_left₀
        (show 0≤Zero.a φ+1/2 by linarith [hzstate.1,hzstate.2.1])
        (show Zero.a φ+1/2≤a+1/2 by linarith) 2
      by_contra hn
      have hlt := pow_lt_pow_left₀ (show Zero.b φ+1/2<b+1/2 by linarith)
        (by linarith [hzstate.1] : 0≤Zero.b φ+1/2) two_ne_zero
      linarith
    have hcutEq : primaryCut a φ*Real.sin φ=
        a-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut]
      field_simp [hsin.ne']
    have hcut : B≤primaryCut a φ := by
      apply (mul_le_mul_iff_left₀ hsin).mp
      linarith
    have hp := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := Zero.contact_antitone hz
      (show b∈Icc (0:ℝ) (Zero.b φ) from ⟨hs.1,hb⟩)
      (show Zero.b φ∈Icc (0:ℝ) (Zero.b φ) from ⟨hzstate.1,le_rfl⟩) hb
    dsimp only at hm
    rw [Zero.boundary_identity hz] at hm
    have hv := Zero.cost_lower hz
    dsimp [primaryContact] at hm
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hm
    dsimp [value]
    linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end
