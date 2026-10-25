module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2UnaffectedCurvature
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Endpoints

/-!
# The high unaffected negative curves, with their original coefficients

Uncompiled transcription of Sections 11--12 of the angle companion.
The GA H/B and AB H/G curves are concave on their actual cuts. Their
two endpoints are discharged by the scalar companion, including the
equal-angle alternative and every actual-cut function. D uses the
identical H negative charge. No endpoint positivity is an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighUnaffected
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate SecantBounds UnaffectedCurvature

def Unaffected : Bool→Fin 4→Prop
  | true,i => i=0∨i=2∨i=3
  | false,i => i=0∨i=1∨i=3
def p (atG : Bool) (z : ℝ) (i : Fin 4) : ℝ :=
  Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 i
def q (atG : Bool) (z : ℝ) (i : Fin 4) : ℝ :=
  Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 i
def ratio (atG : Bool) (z : ℝ) : ℝ :=
  SecantBaseline.basicRatio atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z
def angleEnd (atG : Bool) (z : ℝ) : ℝ := min z (Explicit.angleCut atG)
def scalar (atG : Bool) (z : ℝ) (i : Fin 4) (x : ℝ) : ℝ :=
  pure (baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z)
    (Explicit.l .high z) (ratio atG z) (p atG z i) (q atG z i) z x

private lemma r71_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
  exact hz

theorem cut_domain (atG : Bool) : Explicit.angleCut atG∈Icc (0:ℝ) frameCap := by
  cases atG <;> norm_num [Explicit.angleCut,frameCap]

theorem angleEnd_domain (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    angleEnd atG z∈Icc 0 frameCap ∧ angleEnd atG z≤z ∧
      angleEnd atG z≤Explicit.angleCut atG := by
  have hc := cut_domain atG
  exact ⟨⟨le_min (by linarith [hz.1]) hc.1,(min_le_right _ _).trans hc.2⟩,
    min_le_left _ _,min_le_right _ _⟩

theorem weights_fixed (atG : Bool) (z s : ℝ) (i : Fin 4) (hi : Unaffected atG i) :
    Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i=p atG z i ∧
    Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i=q atG z i := by
  cases atG <;> fin_cases i <;>
    simp [Unaffected,p,q,Source.pWeights,Source.qWeights,lambdaG,lambdaB,secant] at hi ⊢

theorem ordered (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<p atG z i ∧ p atG z i≤q atG z i ∧ q atG z i≤2*p atG z i := by
  exact Explicit.ordered_pair_domain .high atG (r71_high_dom hz)
    (show (0:ℝ)∈Icc 0 (Explicit.angleCut atG) from ⟨le_rfl,(cut_domain atG).1⟩) i

theorem GA_pair_upper {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    q true z i≤(11/10)*Explicit.l .high z := by
  have hq := (Explicit.high_GA_pair_bounds hz
    (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) i).2.2
  have hl := (Explicit.high_ranges hz).2.2.1
  dsimp [q]
  linarith

theorem AB_pair_upper {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (i : Fin 4) (hi : Unaffected false i) :
    p false z i≤(21/25)*q false z i ∧ q false z i≤Explicit.l .high z := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi,hkc,hkl⟩ := Explicit.high_ranges hz
  have hkr := (Explicit.high_tilted hz).2.2
  rcases hi with rfl|rfl|rfl <;>
    norm_num [p,q,Source.pWeights,Source.qWeights,lambdaG,lambdaB,secant] <;>
    (try constructor) <;> linarith

theorem GA_ratio {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ratio true z∈Icc 0 (17/20:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .high (r71_high_dom hz)
  have hkr := (Explicit.high_tilted hz).2.2
  dsimp [ratio,SecantBaseline.basicRatio,SecantBaseline.affected]
  constructor
  · exact div_nonneg hk.le hl.le
  · apply (div_le_iff₀ hl).2
    linarith

theorem AB_ratio {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ratio false z∈Icc 0 (129/125:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .high (r71_high_dom hz)
  have hmr := (Explicit.high_tilted hz).2.1
  change Explicit.m .high z/Explicit.l .high z∈Icc 0 (129/125:ℝ)
  exact ⟨div_nonneg hm.le hl.le,(div_le_iff₀ hl).2 hmr.le⟩

theorem AB_ratio_late {z x : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hx : x∈Icc 0 (Real.tan (angleEnd false z))) (hlate : (7/20:ℝ)<x) :
    ratio false z∈Icc 0 (23/25:ℝ) := by
  have ha := angleEnd_domain false hz
  have hs := arctan_interval ha.1 hx
  have hsframe : Real.arctan x∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ha.1.2⟩
  have hthird : (1/3:ℝ)<Real.arctan x := by
    by_contra hh
    have hle : Real.arctan x≤1/3 := le_of_not_gt hh
    have ht := tan_monotone hsframe
      (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hle
    rw [Real.tan_arctan] at ht
    linarith [tan_third]
  have hzthird : z∈Icc (1/3:ℝ) (7/10:ℝ) :=
    ⟨by linarith [hs.2,ha.2.1],hz.2⟩
  have hmr := Explicit.high_tilted_third hzthird
  have hl := (Explicit.family_positive .high (r71_high_dom hz)).2.1
  have hbase := AB_ratio hz
  change Explicit.m .high z/Explicit.l .high z∈Icc 0 (23/25:ℝ)
  exact ⟨hbase.1,(div_le_iff₀ hl).2 hmr.le⟩

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap)
    (i : Fin 4) (hi : Unaffected atG i) :
    scalar atG z i (Real.tan s)=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
        V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
          (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  obtain ⟨hp,hq⟩ := weights_fixed atG z s i hi
  rw [hp,hq]
  exact pure_at_original atG (Explicit.family_positive .high (r71_high_dom hz)).2.1 hs

private lemma r71_scalar_zero_eq (atG : Bool) (z : ℝ) (i : Fin 4) :
    scalar atG z i 0=PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z)
      (Explicit.c .high z) z+V R (p atG z i) (q atG z i) z := by
  simp only [scalar,SecantCoordinate.pure,sub_self,mul_zero,Real.arctan_zero,sub_zero,add_zero,
    baseline_zero]

theorem scalar_zero (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i 0 := by
  rw [r71_scalar_zero_eq]
  obtain ⟨hH,hG,hB,hGA,hAB⟩ := Certificate.high_endpoints hz
  cases atG
  · rcases hi with rfl|rfl|rfl
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val,lambdaG,
        Bool.false_eq_true,↓reduceIte] using hG
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
  · rcases hi with rfl|rfl|rfl
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val,lambdaB,
        ↓reduceIte] using hB
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH

theorem scalar_equal (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  rw [scalar_at_original atG hz hzframe i hi]
  simp only [sub_self,V_zero,add_zero]
  cases atG
  · exact (Certificate.high_endpoints hz).2.2.2.2
  · exact (Certificate.high_endpoints hz).2.2.2.1

theorem scalar_cut (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hcut : Explicit.angleCut atG≤z)
    (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (Explicit.angleCut atG)) := by
  rw [scalar_at_original atG hz (cut_domain atG) i hi]
  cases atG
  · have hz' : z∈Icc (19/50:ℝ) (7/10:ℝ) := ⟨hcut,hz.2⟩
    obtain ⟨hG,hH⟩ := Certificate.AB_cut_endpoints hz'
    rcases hi with rfl|rfl|rfl
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hG
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
  · have hz' : z∈Icc (1/4:ℝ) (7/10:ℝ) := ⟨hcut,hz.2⟩
    obtain ⟨hH,hB⟩ := Certificate.GA_cut_endpoints hz'
    have hml := Explicit.high_tilted_quarter hz'
    rcases hi with rfl|rfl|rfl
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB,
        min_eq_right hml.le,max_eq_left hml.le] using hB
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH

theorem scalar_right (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (angleEnd atG z)) := by
  by_cases hh : z≤Explicit.angleCut atG
  · rw [angleEnd,min_eq_left hh]
    exact scalar_equal atG hz i hi
  · rw [angleEnd,min_eq_right (le_of_not_ge hh)]
    exact scalar_cut atG hz (le_of_not_ge hh) i hi

theorem scalar_concave (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    ConcaveOn ℝ (Icc 0 (Real.tan (angleEnd atG z))) (scalar atG z i) := by
  have ha := angleEnd_domain atG hz
  obtain ⟨hp,hpq,hqp⟩ := ordered atG hz i
  have hq := hp.trans_le hpq
  have hl := (Explicit.family_positive .high (r71_high_dom hz)).2.1
  apply pure_concave hp hq ha.1 ha.2.1 hz.2
  intro x hx
  have hs := arctan_interval ha.1 hx
  have hθ : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ha.2.1],by simp only [frameCap]; linarith [hz.2,hs.1]⟩
  have htan := tan_monotone ha.1 (cut_domain atG) ha.2.2
  cases atG
  · have hxcut : x∈Icc 0 (2/5:ℝ) :=
      ⟨hx.1,by simpa [Explicit.angleCut] using (hx.2.trans htan).trans tan_AB_cut.le⟩
    have hpair := AB_pair_upper hz i hi
    by_cases hearly : x≤7/20
    · exact (AB_early_total_curvature hl (AB_ratio hz) hp hpq hqp hpair.1 hpair.2
        ⟨hx.1,hearly⟩ hθ).le
    · have hlate : (7/20:ℝ)<x := lt_of_not_ge hearly
      have hh := AB_late_total_curvature hl (AB_ratio_late hz hx hlate)
        hp hpq hqp hpair.1 hpair.2 ⟨hlate.le,hxcut.2⟩ hθ
      linarith
  · have hxcut : x∈Icc 0 (32/125:ℝ) :=
      ⟨hx.1,by simpa [Explicit.angleCut] using (hx.2.trans htan).trans tan_GA_cut.le⟩
    have hh := GA_total_curvature hl (GA_ratio hz) hp hpq hqp (GA_pair_upper hz i) hxcut hθ
    linarith

/-- The actual high unaffected H/G/B/D alternative is strictly positive. -/
theorem original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z)
    (i : Fin 4) (hi : Unaffected atG i) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  have hsframe := (Explicit.angle_domain atG hs).2
  have ha := angleEnd_domain atG hz
  have hsa : s≤angleEnd atG z := le_min hsz hs.2
  have hx : Real.tan s∈Icc 0 (Real.tan (angleEnd atG z)) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe ha.1 hsa⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz i hi) hx
    (scalar_zero atG hz i hi) (scalar_right atG hz i hi)
  rwa [scalar_at_original atG hz hsframe i hi] at hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighUnaffected
