module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSplit
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallEndpoints

/-!
# Eight squares: high-total negative-EH endpoints at every A/TD split

The E magnitude is fixed before the A/TD split varies. All D supports of the high family stay
full-circle lower bounds, and the B pair keeps its ordered coefficients (`coefficient_ratios`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def base (r : Regime) (θ a : ℝ) : ℝ := Explicit.baseline r .high a (θ-a)
def correction (r : Regime) (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c r .high θ)-fullSupport 1 (Explicit.c r .high θ)
def negative (r : Regime) (θ d : ℝ) (i : Fin 3) (a : ℝ) : ℝ :=
  base r θ a+Explicit.V r .high θ (θ-a) i d

theorem base_identity (r : Regime) (θ a : ℝ) :
    base r θ a=TwoPositive.splitBase (Explicit.k r .high θ) (Explicit.l r .high θ)
      (Explicit.c r .high θ) θ a+correction r θ := by
  simp only [base,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.sortedD,Bool.false_eq_true,ite_false,TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.eta,
    NegativeDEPositiveTD.Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem coefficient_ratios (r : Regime) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) :
    0<Explicit.l r .high θ ∧ 0<Explicit.c r .high θ ∧
      (9/10)*Explicit.l r .high θ≤Explicit.c r .high θ ∧
      Explicit.c r .high θ≤(11/10)*Explicit.l r .high θ := by
  cases r
  · have hr := NegativeDEPositiveTD.Explicit.high_ranges hθ
    have hc := NegativeDEPositiveTD.Explicit.high_ratios hθ
    simp only [Explicit.l,Explicit.c]
    exact ⟨by linarith [hr.2.2.1],by linarith [hr.2.2.2.2.1],hc.1.le,by linarith [hc.2,hr.2.2.1]⟩
  · have hr := Explicit.far_high_ranges hθ
    exact ⟨by linarith [hr.2.1.1],by linarith [hr.2.2.1.1],
      by linarith [hr.2.1.1,hr.2.2.2.1],by linarith [hr.2.1.1,hr.2.2.2.2]⟩

theorem coefficient_range (r : Regime) {θ a : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) (ha : a∈Icc 0 θ) :
    PositiveTD.tilted (Explicit.c r .high θ) (θ-a)∈
      Icc (Explicit.c r .high θ/2) ((23/20)*Explicit.l r .high θ) := by
  have hz : θ-a∈Icc 0 θ := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  cases r
  · exact NegativeDEPositiveTD.HighSplit.coefficient_range hθ ha
  · have hr := Explicit.far_high_ranges hθ
    have hm := Explicit.far_high_tilted hθ hz
    change Explicit.m .far .high θ (θ-a)∈Icc _ _
    exact ⟨by linarith [hm.1,hr.2.2.1.1],hm.2.2.2.2.le⟩

theorem base_concave (r : Regime) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) :
    ConcaveOn ℝ (Icc 0 θ) (base r θ) := by
  obtain ⟨hl,hc,hlo,hhi⟩ := coefficient_ratios r hθ
  have ht := Explicit.family_frame_domain r .high hθ
  have hh := TwoPositive.Split.high_increment_concave
    (k:=Explicit.k r .high θ) (s:=0) (g:=0) (e:=0)
    hl hlo hhi ht (by norm_num [frameCap])
    (show 0<Explicit.c r .high θ/2 by positivity) le_rfl le_rfl (by simp)
    (fun a ha => coefficient_range r hθ ha)
  have hb : ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k r .high θ) (Explicit.l r .high θ) (Explicit.c r .high θ) θ) := by
    simpa only [neg_zero,TwoPositive.Split.increment_zero,add_zero] using hh
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hb (correction r θ))
  intro a _
  exact (base_identity r θ a).symm

theorem negative_concave (r : Regime) {θ d : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high))
    (hd : d∈Icc 0 frameCap) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ) (negative r θ d i) := by
  obtain ⟨hl,hc,hlo,hhi⟩ := coefficient_ratios r hθ
  have ht := Explicit.family_frame_domain r .high hθ
  fin_cases i
  · exact TwoPositive.Split.add_constant (base_concave r hθ) (V R (Explicit.k r .high θ) 1 d)
  · exact TwoPositive.Split.add_constant (base_concave r hθ)
        (V R (Explicit.k r .high θ) (Explicit.l r .high θ) d)
  · have hh := TwoPositive.Split.high_increment_concave
      (k:=Explicit.k r .high θ) (s:=d) (g:=0) (e:=Real.cos d-1)
      hl hlo hhi ht hd (show 0<Explicit.c r .high θ/2 by positivity)
      le_rfl (sub_nonpos.mpr (Real.cos_le_one d)) le_rfl (fun a ha => coefficient_range r hθ ha)
    apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction r θ))
    intro a _
    rw [negative,base_identity,TwoPositive.Split.increment_V]
    dsimp [Explicit.V,Explicit.p,Explicit.q,Explicit.m,Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    ring

theorem small_baseline (a z : ℝ) :
    Explicit.baseline .small .high a z=NegativeDEPositiveTD.Explicit.fullBaseline .high a z 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,Bool.false_eq_true,ite_false,Explicit.k,Explicit.l,
    Explicit.c,Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.fullBaseline,
    NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.secant,
    NegativeDEPositiveTD.Explicit.m,
    Real.cos_zero,Real.tan_zero,div_one,mul_zero,sub_self,add_zero]
  ring

theorem small_zero_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+Explicit.V .small .high (a+z) z i (a+z) := by
  rw [small_baseline]
  exact NegativeDEPositiveTD.HighSplit.original_pure_at_zero_positive hθ ha hz i

theorem small_v_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+NegativeEH.g (1/10)+
      Explicit.V .small .high (a+z) z i (a+z-1/10) := by
  have hd : a+z-1/10∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (negative_concave .small hθ hd i) (NegativeEH.g (1/10))
  have h0 := Certificate.small_high_negative_positive .atT hθ i
  have h1 := Certificate.small_high_negative_positive .atA hθ i
  have hh := concave_gt_of_endpoints (c:=0) hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h0)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h1)
  simpa [negative,base,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm] using hh

theorem far_cut_positive (atUpper : Bool) {a z : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .far .high a z+NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10)+
      Explicit.V .far .high (a+z) z i (a+z-(if atUpper then (1/4:ℝ) else 1/10)) := by
  have hd : a+z-(if atUpper then (1/4:ℝ) else 1/10)∈Icc 0 frameCap := by
    cases atUpper <;> norm_num [frameCap] at * <;> constructor <;> linarith [hθ.1,hθ.2]
  have hc := TwoPositive.Split.add_constant (negative_concave .far hθ hd i)
    (NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10))
  have h0 := Certificate.far_high_negative_positive atUpper .atT hθ i
  have h1 := Certificate.far_high_negative_positive atUpper .atA hθ i
  have hh := concave_gt_of_endpoints (c:=0) hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h0)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h1)
  simpa [negative,base,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.HighSplit
