module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsTD0Source
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDGain

/-!
# Nonnegative A/E totals with a nonpositive TD2 error

Uncompiled transcription of Sections 1--3 of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_NEGATIVE_TD2_EXCLUSION.md`.
The new coefficients depend only on the original selected E total.
The sharp secant gain uses the same unchanged T and D points and the
same half-angle bound as the already written negative-TD theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev L : ℝ := 1/6
abbrev span : ℝ := 8/15
abbrev c : ℝ := 27/20
abbrev gamma : ℝ := 18247/20000
abbrev speed : ℝ := gamma*c
abbrev aD : ℝ := GlobalGA.Secondary.diagonal-1/2

def k (e : ℝ) : ℝ := 3/4+(7/50)*e
def l (e : ℝ) : ℝ := 19/20+(9/20)*e
def p (e : ℝ) : Fin 4→ℝ := ![k e,k e,l e,k e]
def q (e : ℝ) : Fin 4→ℝ := ![1,l e,c,1]
def base (e : ℝ) : ℝ :=
  k e+2*l e+2*c+2-fullSupport 1 (k e)-fullSupport (l e) (k e)-
    fullSupport c (l e)-(1+c)*GlobalGA.Secondary.diagonal

def Domain (t e : ℝ) : Prop := t∈Icc L frameCap ∧ e∈Icc 0 t

def primaryCost (t e : ℝ) : ℝ := l e*TwoPositive.ASupport.charge (t-e)+TwoPositive.ASupport.charge e

def negativeScalar (i : Fin 3) (t e : ℝ) : ℝ :=
  base e+primaryCost t e+V R (p e i.castSucc) (q e i.castSucc) t
def equalScalar (t e : ℝ) : ℝ := base e+primaryCost t e+speed*t
def positiveScalar (i : Fin 3) (t e : ℝ) : ℝ :=
  base e+primaryCost t e+speed*frameCap+U R (p e i.castSucc) (q e i.castSucc) (frameCap-t)
def DScalar (t e : ℝ) : ℝ := base e+primaryCost t e+speed*frameCap-aD*(frameCap-t)

theorem domain_angles {t e : ℝ} (hd : Domain t e) :
    t∈Icc 0 frameCap ∧ e∈Icc 0 frameCap ∧ t-e∈Icc 0 frameCap ∧
      frameCap-t∈Icc 0 span := by
  dsimp [Domain,L,span,frameCap] at hd ⊢
  exact ⟨⟨by linarith [hd.1.1],hd.1.2⟩,
    ⟨hd.2.1,by linarith [hd.2.2,hd.1.2]⟩,
    ⟨by linarith [hd.2.2],by linarith [hd.1.2,hd.2.1]⟩,
    ⟨by linarith [hd.1.2],by linarith [hd.1.1]⟩⟩

theorem ranges {e : ℝ} (he : e∈Icc 0 frameCap) :
    (3/4:ℝ)≤k e ∧ k e≤106/125 ∧ (19/20:ℝ)≤l e ∧ l e≤253/200 ∧
      k e<l e ∧ l e<c ∧ 2*l e<3*k e ∧ 2*c<3*l e := by
  dsimp [k,l,c,frameCap] at *
  exact ⟨by linarith [he.1],by linarith [he.2],by linarith [he.1],
    by linarith [he.2],by linarith [he.1],by linarith [he.2],
    by linarith [he.2],by linarith [he.1]⟩

theorem coefficients {e : ℝ} (he : e∈Icc 0 frameCap) (i : Fin 4) :
    0<p e i ∧ p e i≤q e i ∧ 2*q e i≤3*p e i ∧
      (19/20:ℝ)≤q e i ∧ q e i≤c := by
  obtain ⟨hk0,hk1,hl0,hl1,hkl,hlc,hbalG,hbalB⟩ := ranges he
  simp only [c] at hlc hbalB ⊢
  fin_cases i
  · change 0<k e ∧ k e≤1 ∧ 2*1≤3*k e ∧ (19/20:ℝ)≤1 ∧ (1:ℝ)≤27/20
    exact ⟨by linarith,by linarith,by linarith,by norm_num,by norm_num⟩
  · change 0<k e ∧ k e≤l e ∧ 2*l e≤3*k e ∧ (19/20:ℝ)≤l e ∧ l e≤27/20
    exact ⟨by linarith,hkl.le,hbalG.le,hl0,hlc.le⟩
  · change 0<l e ∧ l e≤27/20 ∧ 2*(27/20)≤3*l e ∧ (19/20:ℝ)≤27/20 ∧ (27/20:ℝ)≤27/20
    exact ⟨by linarith,hlc.le,hbalB.le,by norm_num,le_rfl⟩
  · change 0<k e ∧ k e≤1 ∧ 2*1≤3*k e ∧ (19/20:ℝ)≤1 ∧ (1:ℝ)≤27/20
    exact ⟨by linarith,by linarith,by linarith,by norm_num,by norm_num⟩

theorem sharp_gain {s A B w : ℝ} (hs : s∈Icc 0 frameCap)
    (hA : 447/800≤A) (hB : B≤9/10) (hw : 0≤w) :
    gamma*w*s≤PositiveANegativeTD.gain w s A B := by
  have ht := transport_trig hs
  have hc : 0<Real.cos s := by linarith [ht.1]
  have ha := mul_le_mul_of_nonneg_right hA ht.2.2.1
  have hb := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr (Real.cos_le_one s))
  have hhalf := PositiveANegativeTD.one_sub_cos_upper hs
  have htan := PositiveANegativeTD.sine_ge_angle_cos hs
  have hnum : gamma*s*Real.cos s≤
      (A+1/2)*Real.sin s+(1/2-B)*(1-Real.cos s) := by
    dsimp [gamma]
    nlinarith only [ha,hb,hhalf,htan]
  have hscaled := mul_le_mul_of_nonneg_left hnum hw
  rw [PositiveANegativeTD.gain,le_div_iff₀ hc]
  nlinarith only [hscaled]

theorem actual_sharp_gain {Q s w : ℝ} {T D : SignedPoint}
    (hT : T.Sorted) (hcore : T.AvoidsCore) (hTc : T.Contained Q)
    (hD : D.Sorted) (hDy : D.y≤0) (hDc : D.Contained Q) (hQ : Q≤qCap)
    (hs : s∈Icc 0 frameCap) (hw : 0≤w) :
    gamma*w*s≤PositiveANegativeTD.gain w s T.a (-D.y) := by
  have hTb := SignedPoint.coordinate_bounds hT hcore hTc hQ
  have hDb := actual_coordinate_bounds (P:=D.reflect)
    (by simpa using hD) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hDc) hQ
  apply sharp_gain hs hTb.1.le _ hw
  have hh := hDb.2.1
  dsimp [SignedPoint.reflect] at hh
  linarith [diagonal_bounds.2]

theorem base_norms (e : ℝ) :
    base e=2*k e+3*l e+(5/2)*c+5/2-(1+c)*GlobalGA.Secondary.diagonal-
      R*(pairNorm (k e) 1 0+pairNorm (k e) (l e) 0+pairNorm (l e) c 0) := by
  rw [base,fullSupport_pair (k e) 1,fullSupport_pair (k e) (l e),fullSupport_pair (l e) c]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
