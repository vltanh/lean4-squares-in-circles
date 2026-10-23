module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirst

/-!
# The target envelope of the reverse lower-secondary contact

The critical equation is the explicit scalar equation `S(B)=q(b)`.
Its envelope derivatives are defined and differentiated here without
assuming an inverse function or a stationary curve.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open LowerInverse LowerGeometry

def p (B : ℝ) : ℝ := LLabel.d1 B
def ell (B : ℝ) : ℝ := LLabel.d2 B
def z (B : ℝ) : ℝ := B+1/2
def S (B : ℝ) : ℝ := (z B)^2+1/(p B)^2
def h (B : ℝ) : ℝ := z B*p B
def h₁ (B : ℝ) : ℝ := p B+z B*ell B
def h₂ (B : ℝ) : ℝ := 2*ell B+z B*LLabel.d3 B
def D (B : ℝ) : ℝ := z B-ell B/(p B)^3
def D₁ (B : ℝ) : ℝ := 1-LLabel.d3 B/(p B)^3+3*(ell B)^2/(p B)^4
def g₁ (B : ℝ) : ℝ := -h B/(2*S B)
def g₂ (B : ℝ) : ℝ := h B/(2*(S B)^2)-h₁ B/(4*S B*D B)
def g₃ (B : ℝ) : ℝ :=
  -h₂ B/(8*S B*(D B)^2)+h₁ B/(2*(S B)^2*D B)+
    h₁ B*D₁ B/(8*S B*(D B)^3)-h B/(S B)^3
def marker (B : ℝ) : ℝ := -ell B-(3/2)*p B
def slopeRatio (B : ℝ) : ℝ := -ell B/(p B)^2

lemma p_positive {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<p B := by
  have hh := L_first_lower hB
  dsimp [p]
  linarith

lemma ell_negative {B : ℝ} (hB : B∈Icc 0 (83/200)) : ell B<0 := by
  have hh := L_second_early (show B∈Icc 0 (1/2) from ⟨hB.1,by linarith [hB.2]⟩)
  exact hh

lemma S_positive {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<S B := by
  have hp := p_positive hB
  dsimp [S]
  positivity

lemma D_positive {B : ℝ} (hB : B∈Icc 0 (83/200)) : 0<D B := by
  have hp := p_positive (LowerFirst.short_domain hB)
  have he := ell_negative hB
  have hz : 0<z B := by dsimp [z]; linarith [hB.1]
  have hq : ell B/(p B)^3<0 := div_neg_of_neg_of_pos he (pow_pos hp 3)
  dsimp [D]
  linarith

lemma p_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt p (ell B) B :=
  LLabel.d1_hasDerivAt (outer_domain hB)
lemma ell_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt ell (LLabel.d3 B) B := LLabel.d2_hasDerivAt (outer_domain hB)
lemma z_hasDerivAt (B : ℝ) : HasDerivAt z 1 B := (hasDerivAt_id B).add_const (1/2)

lemma S_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt S (2*D B) B := by
  have hp := p_positive hB
  have hd := ((z_hasDerivAt B).pow 2).add
    ((hasDerivAt_const B (1:ℝ)).div ((p_hasDerivAt hB).pow 2) (pow_ne_zero 2 hp.ne'))
  convert hd using 1
  · rfl
  · dsimp [D]
    field_simp [hp.ne']
    ring

lemma h_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt h (h₁ B) B := by
  convert (z_hasDerivAt B).mul (p_hasDerivAt hB) using 1 <;> dsimp [h,h₁] <;> ring

lemma h₁_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt h₁ (h₂ B) B := by
  convert (p_hasDerivAt hB).add ((z_hasDerivAt B).mul (ell_hasDerivAt hB))
    using 1 <;> dsimp [h₁,h₂] <;> ring

lemma D_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : HasDerivAt D (D₁ B) B := by
  have hp := p_positive hB
  have hd := (z_hasDerivAt B).sub
    ((ell_hasDerivAt hB).div ((p_hasDerivAt hB).pow 3) (pow_ne_zero 3 hp.ne'))
  convert hd using 1
  · rfl
  · dsimp [D₁]
    field_simp [hp.ne']
    ring

lemma g₁_hasDerivAt {B : ℝ} (hB : B∈Icc 0 (83/200)) :
    HasDerivAt g₁ (2*D B*g₂ B) B := by
  have hf := LowerFirst.short_domain hB
  have hs := S_positive hf
  have hd := D_positive hB
  convert (h_hasDerivAt hf).neg.div ((S_hasDerivAt hf).const_mul 2)
    (mul_ne_zero (by norm_num) hs.ne') using 1
  · rfl
  · dsimp [g₂]
    field_simp [hs.ne',hd.ne']
    ring

lemma g₂_hasDerivAt {B : ℝ} (hB : B∈Icc 0 (83/200)) :
    HasDerivAt g₂ (2*D B*g₃ B) B := by
  have hf := LowerFirst.short_domain hB
  have hs := S_positive hf
  have hd := D_positive hB
  have hleft := (h_hasDerivAt hf).div (((S_hasDerivAt hf).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs.ne'))
  have hright := (h₁_hasDerivAt hf).div
    (((S_hasDerivAt hf).const_mul 4).mul (D_hasDerivAt hf))
    (mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hd.ne')
  convert hleft.sub hright using 1
  · rfl
  · dsimp [g₃]
    field_simp [hs.ne',hd.ne']
    ring

lemma marker_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt marker (-LLabel.d3 B-(3/2)*ell B) B := by
  exact (ell_hasDerivAt hB).neg.sub ((p_hasDerivAt hB).const_mul (3/2))

lemma slopeRatio_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt slopeRatio ((2*(ell B)^2-p B*LLabel.d3 B)/(p B)^3) B := by
  have hp := p_positive hB
  convert (ell_hasDerivAt hB).neg.div ((p_hasDerivAt hB).pow 2) (pow_ne_zero 2 hp.ne') using 1
  · rfl
  · field_simp [hp.ne']
    ring

lemma S_monotone : MonotoneOn S (Icc 0 (83/200)) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (S_hasDerivAt (LowerFirst.short_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => S_hasDerivAt (LowerFirst.short_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => by linarith [D_positive (Ioo_subset_Icc_self hB)])

lemma p_antitone : AntitoneOn p (Icc 0 (83/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (p_hasDerivAt (LowerFirst.short_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => p_hasDerivAt (LowerFirst.short_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (ell_negative (Ioo_subset_Icc_self hB)).le)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
