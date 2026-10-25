module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreThreeZeroCurve

/-!
# One exact reference for the interior primary-contact minimum

The reference angle is rational. Taylor inequalities enclose its
harmonic height, and two squared rational radical cages control the
primary label and its first derivative. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore.Zero
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore.Zero
