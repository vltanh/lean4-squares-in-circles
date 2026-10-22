module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowSeparated

/-!
# All low saturated alternatives with the original pairs

Uncompiled transcription of Section 8. The H and B same-block cases
use the displayed ratio `1.5`; G uses its increasing combined curve.
Every separated case, including the D linear term, uses the same
original positive allowance and one of the certified H/G endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowSaturated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD.Hybrid

def p (atG : Bool) (s z : ℝ) : Fin 4→ℝ :=
  Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s
def q (atG : Bool) (s z : ℝ) : Fin 4→ℝ :=
  Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s
def largerCap (z : ℝ) : ℝ := Explicit.m .low z+(2/5)*z

theorem B_coefficients (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    Explicit.l .low z≤lambdaB atG (Explicit.l .low z) s ∧
      lambdaB atG (Explicit.l .low z) s≤(27/25)*Explicit.l .low z := by
  have hl := (Explicit.family_positive .low hz).2.1
  have hsec := (Explicit.secant_bounds .low atG hz hs).1
  have hcos := Explicit.AB_cut_cosine (Explicit.angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hupper : NegativeAPositiveTD.secant (Explicit.l .low z) s≤(27/25)*Explicit.l .low z := by
    apply (div_le_iff₀ hc).2
    nlinarith [mul_lt_mul_of_pos_left hcos hl]
  cases atG <;> simp only [lambdaB,↓reduceIte]
  · exact ⟨hsec,hupper⟩
  · exact ⟨le_rfl,by nlinarith⟩

theorem pair_HB_ratio (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) : q atG s z i≤(3/2)*p atG s z i := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  obtain ⟨hB,hBhi⟩ := B_coefficients atG hz hs
  have hm := Explicit.low_tilted hz
  rcases hi with rfl|rfl
  · change 1≤(3/2)*Explicit.k .low z
    linarith
  · change max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤
      (3/2)*min (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)
    have hmin : Explicit.l .low z≤min (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z) :=
      le_min hB hm.1.le
    have hmax : max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤(3/2)*Explicit.l .low z := by
      exact max_le (by linarith) (by linarith [hm.2])
    exact hmax.trans (mul_le_mul_of_nonneg_left hmin (by norm_num))

theorem larger_bounds (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    1≤q atG s z i ∧ q atG s z i≤largerCap z := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hm := Explicit.low_tilted hz
  have hs' := (Explicit.angle_domain atG hs).1
  have hsec := (Explicit.secant_bounds .low atG hz hs).1
  have hcap := Explicit.low_secant hz hs'
  have hM : Explicit.m .low z≤largerCap z := by dsimp [largerCap]; linarith [hz.1]
  have hL : Explicit.l .low z≤largerCap z := hm.1.le.trans hM
  have hG : Explicit.l .low z≤lambdaG atG (Explicit.l .low z) s ∧
      lambdaG atG (Explicit.l .low z) s≤largerCap z := by
    cases atG <;> simp only [lambdaG,↓reduceIte]
    · exact ⟨le_rfl,hL⟩
    · exact ⟨hsec,hcap.le⟩
  have hB : Explicit.l .low z≤lambdaB atG (Explicit.l .low z) s ∧
      lambdaB atG (Explicit.l .low z) s≤largerCap z := by
    cases atG <;> simp only [lambdaB,↓reduceIte]
    · exact ⟨hsec,hcap.le⟩
    · exact ⟨le_rfl,hL⟩
  fin_cases i
  · change 1≤(1:ℝ) ∧ 1≤largerCap z
    exact ⟨le_rfl,by linarith⟩
  · change 1≤lambdaG atG (Explicit.l .low z) s ∧ lambdaG atG (Explicit.l .low z) s≤largerCap z
    exact ⟨by linarith [hG.1],hG.2⟩
  · change 1≤max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z) ∧
      max (lambdaB atG (Explicit.l .low z) s) (Explicit.m .low z)≤largerCap z
    exact ⟨(by linarith : (1:ℝ)≤lambdaB atG (Explicit.l .low z) s).trans (le_max_left _ _),max_le hB.2 hM⟩
  · change 1≤(1:ℝ) ∧ 1≤largerCap z
    exact ⟨le_rfl,by linarith⟩

theorem positive_allowance (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    -LowSeparated.allowance z≤positive R (diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z) := by
  have hc := Explicit.ordered_pair_domain .low atG hz hs i
  have hq := larger_bounds atG hz hs i
  have hP : frameCap-z∈Icc 0 frameCap := by
    dsimp [frameCap]
    constructor <;> linarith [hz.1,hz.2]
  have hu := HighSaturated.positive_lower (d:=(3:Fin 4))
    (by linarith [diagonal_bounds.2]) hc.1 hc.2.1 hc.2.2 hq.1 hP
  have hh := mul_le_mul_of_nonneg_right hq.2 hP.1
  dsimp [LowSeparated.allowance,largerCap] at hh ⊢
  nlinarith only [hu,hh]

theorem separated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (p atG s z j) (q atG s z j) (frameCap-s) := by
  have hu := positive_allowance atG hz hs i
  have hH := LowSeparated.H_positive atG hz hs
  have hG := LowSeparated.G_positive atG hz hs
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  fin_cases j
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s)
    linarith
  · have hB := LowNegativeComparison.B_dominates_H atG hz hs hN
    change V R (Explicit.k .low z) 1 (frameCap-s)≤V R (p atG s z 2) (q atG s z 2) (frameCap-s) at hB
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      positive R (diagonal-1/2) (p atG s z) (q atG s z) 3 i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith

theorem HB_pure_le_same (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) :
    Concentration.pure R (diagonal-1/2) (p atG s z) (q atG s z) 3 i i s z≤
      mixedBlock R (p atG s z i) (q atG s z i) (frameCap-z) (frameCap-s) := by
  have hc := Explicit.ordered_pair_domain .low atG hz hs i
  have hratio := pair_HB_ratio atG hz hs i hi
  have hsf := (Explicit.angle_domain atG hs).2
  have hP : frameCap-z∈Icc 0 frameCap := by
    dsimp [frameCap]
    constructor <;> linarith [hz.1,hz.2]
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hid : i≠3 := by rcases hi with rfl|rfl <;> decide
  by_cases hsz : s≤z
  · have hsin := (transport_trig hN).2.2.2.1
    have hq0 : 0≤q atG s z i := (hc.1.trans_le hc.2.1).le
    have hprod := mul_le_mul hratio hsin.le (transport_trig hN).2.2.1
      (show (0:ℝ)≤(3/2)*p atG s z i by exact mul_nonneg (by norm_num) hc.1.le)
    have hpay : q atG s z i*Real.sin (frameCap-s)≤p atG s z i := by
      nlinarith only [hprod,hc.1]
    have hh := SameBlock.negative_surplus hc.1.le
      (show frameCap-z∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN hpay
    simpa only [Concentration.pure,if_pos hsz,show frameCap-s-(frameCap-z)=z-s by ring] using hh
  · have hh := SameBlock.positive_surplus hc.1.le
      (show q atG s z i≤(17/10)*p atG s z i by nlinarith only [hratio,hc.1]) hP
      (show frameCap-s∈Icc 0 (frameCap-z) from ⟨hN.1,by linarith⟩)
    simpa only [Concentration.pure,if_neg hsz,positive,if_neg hid,
      show frameCap-z-(frameCap-s)=s-z by ring] using hh

theorem original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.saturated R (diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z := by
  by_cases hij : i=j
  · subst j
    by_cases hiD : i=3
    · subst i
      simpa only [Concentration.saturated,if_pos rfl,block,positive,add_assoc] using
        separated_positive atG hz hs 3 3
    by_cases hiG : i=1
    · subst i
      simpa [Concentration.saturated,block,p,q,Source.pWeights,Source.qWeights,
        LowSaturatedG.same] using LowSaturatedG.same_positive atG hz hs
    have hi : i=0∨i=2 := by fin_cases i <;> simp_all
    have hcomp := HB_pure_le_same atG hz hs i hi
    have hpure := LowPure.original atG hz hs i i
    change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.pure R (diagonal-1/2) (p atG s z) (q atG s z) 3 i i s z at hpure
    simp only [Concentration.saturated,if_pos rfl,block,if_neg hiD]
    linarith
  · simpa only [Concentration.saturated,if_neg hij,add_assoc] using separated_positive atG hz hs i j

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<Source.intrinsic atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z i j := by
  have hP := LowPure.original atG hz hs i j
  have hS := original atG hz hs i j
  change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
    min (Concentration.pure R (diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z)
      (Concentration.saturated R (diagonal-1/2) (p atG s z) (q atG s z) 3 i j s z)
  rw [add_min]
  exact lt_min hP hS

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowSaturated
