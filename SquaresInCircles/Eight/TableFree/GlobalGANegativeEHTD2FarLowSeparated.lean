module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarLowPure

/-!
# Every far-low separated signed-mass alternative

Uncompiled Section 4 of the far-low companion. The original B negative
part is compared with H, leaving the two fixed H/G negative coefficients.
Their angular slope is below .881 while the EH gain slope exceeds .8917.
Thus the whole EH interval reduces to its actual .1 endpoint. The two
possible total-angle ranges are paid by the already proved pure reserves.
The positive block is arbitrary, including the original DE2 singleton.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope

def negativeQ (θ : ℝ) : Fin 2→ℝ := ![1,Explicit.l .far .low θ]

def energy (q s : ℝ) : ℝ := NegativeEH.G s+V R (121/200) q (frameCap-s)

lemma negativeQ_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (j : Fin 2) :
    negativeQ θ j∈Icc (91/100:ℝ) 1 := by
  have hr := Explicit.far_low_ranges hθ
  fin_cases j
  · norm_num [negativeQ]
  · exact hr.2.1

lemma negative_representative {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (j : Fin 4) :
    ∃r : Fin 2,V R (121/200) (negativeQ θ r) t≤Blocks.negative .far .low θ z t j := by
  fin_cases j
  · exact ⟨0,le_rfl⟩
  · exact ⟨1,le_rfl⟩
  · exact ⟨0,FarLowSlopes.H_le_B hθ hz ht⟩
  · exact ⟨0,le_rfl⟩

lemma remaining_angle {s : ℝ} (hs : s∈Icc (1/10:ℝ) (1/4)) :
    frameCap-s∈Icc (9/20:ℝ) (3/5) := by
  norm_num [frameCap]
  exact ⟨by linarith [hs.2],by linarith [hs.1]⟩

lemma energy_hasDerivAt {q s : ℝ} (hq : q∈Icc (91/100:ℝ) 1)
    (hs : s∈Icc (1/10:ℝ) (1/4)) :
    HasDerivAt (energy q) (NegativeEH.GD s-Vd R (121/200) q (frameCap-s)) s := by
  have hx := remaining_angle hs
  have ht : frameCap-s∈Icc 0 frameCap := by
    simp only [frameCap] at hx ⊢
    exact ⟨by linarith [hx.1],by linarith [hx.2,hs.1]⟩
  have hV := HasDerivAt.comp_const_sub frameCap s (V_hasDerivAt (R:=R)
    (by norm_num : (0:ℝ)<121/200) (show 0<q by linarith [hq.1]) ht)
  convert (NegativeEH.G_hasDerivAt s).fun_add hV using 1
  rfl

lemma energy_monotone {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    MonotoneOn (energy q) (Icc (1/10:ℝ) (1/4)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (energy_hasDerivAt hq hs).continuousAt.continuousWithinAt)
    (fun s hs => energy_hasDerivAt hq (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf := Ioo_subset_Icc_self hs
  have hG := NegativeEH.far_slope hsf
  have hV := FarLowSlopes.negative_slope hq (remaining_angle hsf)
  linarith

lemma negative_at_six {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    (31581/70000:ℝ)≤V R (121/200) q (3/5) := by
  have hh := V_chord_lower (p:=(121/200:ℝ)) (q:=q)
    (by norm_num) (by linarith [hq.1]) (by linarith [hq.2])
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have e : (87/70:ℝ)*(121/200)*(3/5)=31581/70000 := by norm_num
  rw [e] at hh
  exact hh

lemma at_left_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) (j : Fin 2) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      Blocks.positive .far .low (a+z) z (frameCap-(a+z)) i+
        V R (121/200) (negativeQ (a+z) j) (3/5) := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hP : frameCap-(a+z)∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hθ.2],by linarith [hθ.1]⟩
  have hU := FarLowSlopes.positive_lower hθ hsplit hP i
  have hV := negative_at_six (negativeQ_bounds hθ j)
  by_cases he : a+z≤1/10
  · have hh := FarLowSplit.positive_H ⟨hθ.1,he⟩ ha hz
    have hHt := NegativeEH.PositiveD.H_linear_upper
      (k:=Explicit.k .far .low (a+z)) (by norm_num [Explicit.k])
      (show 1/10-(a+z)∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.1]⟩)
    dsimp [frameCap,NegativeEH.epsilon] at *
    nlinarith [hθ.1]
  · have hh := FarLowSplit.negative_H ⟨by linarith,hθ.2⟩ ha hz
    have hHt := FarLowSlopes.H_upper (θ:=a+z) (z:=z)
      (show a+z-1/10∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.2]⟩)
    change V R (Explicit.k .far .low (a+z)) 1 (a+z-1/10)≤(41/40)*(a+z-1/10) at hHt
    dsimp [frameCap] at hU
    nlinarith [hθ.2]

theorem original_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<Explicit.stressBase .far .low a z s+
      Blocks.positive .far .low (a+z) z (frameCap-(a+z)) i+
        Blocks.negative .far .low (a+z) z (frameCap-s) j := by
  have ht : frameCap-s∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  obtain ⟨r,hr⟩ := negative_representative hθ ⟨hz,by linarith⟩ ht j
  have hmono := energy_monotone (negativeQ_bounds hθ r)
    (show (1/10:ℝ)∈Icc (1/10) (1/4) by norm_num) hs hs.1
  have hleft := at_left_positive hθ ha hz i r
  have hcap : frameCap-(1/10:ℝ)=3/5 := by norm_num [frameCap]
  dsimp [energy] at hmono
  rw [hcap] at hmono
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowSeparated
