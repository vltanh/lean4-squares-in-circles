module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Polynomial

/-!
# Positive tangent denominators for the negative-A scalar endpoints

Uncompiled transcription of the auxiliary-polynomial positivity in
Sections 8 and 9 of the scalar companion. Each bound is on the whole
coefficient interval. It applies the hand proof's centered monomial
coefficient norm to the displayed auxiliary polynomial itself.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial PowerTailBounds
open PositiveTD.Certificate (C4 h)

def mass (f : Family) : Fin 15→ℚ[X] :=
  ![RH f,RG f,RB f,RD f,RHminus f,RGminus f,RBminus f,
    C4*RH f,equalGAR f 1,C4*RB f,C4*RD f,C4*RG f,
    C (4/5)*l f+C (3/5)*mu f*C4,C (77/100),C (77/100)*l f]
def midpoint (f : Family) : ℚ := (left f+right f)/2
def radius (f : Family) : ℚ := (right f-left f)/2
def massCentered (f : Family) (i : Fin 15) : ℚ[X] :=
  DirectedPowerBounds.shift (midpoint f) (mass f i)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_identity (f : Family) (i : Fin 15) :
    massCentered f i=C ((massCentered f i).coeff 0)+tail (massCentered f i) 1 11 := by
  cases f <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_reserve (f : Family) (i : Fin 15) :
    (29/50:ℚ)<(massCentered f i).coeff 0-
      PowerTailBounds.norm (massCentered f i) 1 11 (radius f) := by
  cases f <;> fin_cases i <;> decide

theorem mass_lower (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    (29/50:ℝ)<aeval z (mass f i) := by
  have hx : |z-(midpoint f:ℝ)|≤(radius f:ℝ) := by
    apply abs_le.mpr
    norm_num [midpoint,radius]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (mass_identity f i) hx
  have hr : (29/50:ℝ)<((massCentered f i).coeff 0:ℝ)-
      (PowerTailBounds.norm (massCentered f i) 1 11 (radius f):ℝ) := by
    exact_mod_cast mass_reserve f i
  have he : aeval (z-(midpoint f:ℝ)) (massCentered f i)=aeval z (mass f i) := by
    simp [massCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem mass_positive (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) : 0<aeval z (mass f i) := by
  have hh := mass_lower f i hz
  linarith

theorem ordinary_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval z (RH f) ∧ 0<aeval z (RG f) ∧ 0<aeval z (RB f) ∧
    0<aeval z (RD f) ∧ 0<aeval z (RHminus f) ∧
    0<aeval z (RGminus f) ∧ 0<aeval z (RBminus f) := by
  exact ⟨by simpa [mass] using mass_positive f 0 hz,
    by simpa [mass] using mass_positive f 1 hz,
    by simpa [mass] using mass_positive f 2 hz,
    by simpa [mass] using mass_positive f 3 hz,
    by simpa [mass] using mass_positive f 4 hz,
    by simpa [mass] using mass_positive f 5 hz,
    by simpa [mass] using mass_positive f 6 hz⟩

theorem equal_GA_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) (i : Fin 4) :
    0<aeval z (equalGAR f i) := by
  fin_cases i
  · simpa [mass,equalGAR] using mass_positive f 7 hz
  · simpa [mass] using mass_positive f 8 hz
  · simpa [mass,equalGAR] using mass_positive f 9 hz
  · simpa [mass,equalGAR] using mass_positive f 10 hz

theorem equal_AB_masses_positive {z : ℝ}
    (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<aeval z (equalABR i) := by
  fin_cases i
  · simpa [mass,equalABR] using mass_positive .high 7 hz
  · simpa [mass,equalABR] using mass_positive .high 11 hz
  · simpa [mass,equalABR] using mass_positive .high 12 hz
  · simpa [mass,equalABR] using mass_positive .high 10 hz

def cutMidpoint (e : Cut) : ℚ := (cutAngle e+h)/2
def cutRadius (e : Cut) : ℚ := (h-cutAngle e)/2
def cutMassCentered (e : Cut) (i : Fin 4) : ℚ[X] :=
  DirectedPowerBounds.shift (cutMidpoint e) (cutR e i)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cut_mass_identity (e : Cut) (i : Fin 4) :
    cutMassCentered e i=C ((cutMassCentered e i).coeff 0)+
      tail (cutMassCentered e i) 1 8 := by
  cases e <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cut_mass_reserve (e : Cut) (i : Fin 4) :
    (93/100:ℚ)<(cutMassCentered e i).coeff 0-
      PowerTailBounds.norm (cutMassCentered e i) 1 8 (cutRadius e) := by
  cases e <;> fin_cases i <;> decide

theorem cut_mass_lower (e : Cut) (i : Fin 4) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) :
    (93/100:ℝ)<aeval z (cutR e i) := by
  have hx : |z-(cutMidpoint e:ℝ)|≤(cutRadius e:ℝ) := by
    apply abs_le.mpr
    norm_num [cutMidpoint,cutRadius]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (cut_mass_identity e i) hx
  have hr : (93/100:ℝ)<((cutMassCentered e i).coeff 0:ℝ)-
      (PowerTailBounds.norm (cutMassCentered e i) 1 8 (cutRadius e):ℝ) := by
    exact_mod_cast cut_mass_reserve e i
  have he : aeval (z-(cutMidpoint e:ℝ)) (cutMassCentered e i)=aeval z (cutR e i) := by
    simp [cutMassCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem cut_masses_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) :
    0<aeval z (cutR e i) := by
  have hh := cut_mass_lower e i hz
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
