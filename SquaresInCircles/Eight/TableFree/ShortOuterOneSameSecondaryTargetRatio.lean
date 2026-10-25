module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryNegativeData

/-!
# Decreasing target cost on both complete later-row contact domains

Uncompiled transcription of Section 3 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The actual target ratio is extended continuously to the diagonal ratio
one. A single positive derivative controls that extension. At its
endpoint the displayed quadratic and its exact discriminant give the
strict target descent for rows two and three.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.TargetRatio
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open SecondWord (U W)

def M : ℝ := 383/200
def root (w : ℝ) : ℝ := Real.sqrt (1+w^2)
def curveU (w : ℝ) : ℝ := Real.sqrt Q0/root w
def v (w x : ℝ) : ℝ := 1+Real.cos x+curveU w*(w*Real.sin x-Real.cos x)
def X (w x : ℝ) : ℝ := Real.sin x+w*Real.cos x
def E (r : Row) (w x : ℝ) : ℝ := (t r+P r*v w x/M)*X w x-p r*w-q r
def ED (r : Row) (w x : ℝ) : ℝ :=
  t r*Real.cos x-p r+(P r/M)*(Real.cos x*v w x+curveU w*(X w x)^2/(1+w^2))
def z (r : Row) : ℝ := -P r/M
def c0 (r : Row) : ℝ := t r-(3/5)*z r-p r-q r
def c1 (r : Row) : ℝ := t r-(441/250)*z r
def c2 (r : Row) : ℝ := t r/2+(13/10)*z r
def polynomial (r : Row) (s : ℝ) : ℝ := c0 r+c1 r*s-c2 r*s^2

lemma root_positive (w : ℝ) : 0<root w := Real.sqrt_pos.mpr (by positivity)
lemma root_sq (w : ℝ) : (root w)^2=1+w^2 := Real.sq_sqrt (by positivity)
lemma curveU_positive (w : ℝ) : 0<curveU w :=
  div_pos (Real.sqrt_pos.mpr (by norm_num [Q0])) (root_positive w)

lemma curveU_circle (w : ℝ) : (curveU w)^2*(1+w^2)=Q0 := by
  have hr := root_sq w
  have hR := Real.sq_sqrt (show 0≤Q0 by norm_num [Q0])
  dsimp [curveU]
  rw [←hr,div_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (root_positive w).ne')]
  exact hR

lemma curveU_upper {w : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) : curveU w<M := by
  have hc := curveU_circle w
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤261/1000) hw.1 2
  have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg (curveU w))
  norm_num [Q0,M] at *
  nlinarith [curveU_positive w]

lemma curveU_one : curveU 1=outerDiagonal+1/2 := by
  have hc := curveU_circle 1
  norm_num at hc
  nlinarith [diagonal_circle,curveU_positive 1,outer_endpoint_bounds.2.2.1]

lemma root_hasDerivAt (w : ℝ) : HasDerivAt root (w/root w) w := by
  have h := (((hasDerivAt_id w).pow 2).const_add 1).sqrt (show (1+w^2:ℝ)≠0 by positivity)
  convert h using 1
  · rfl
  change w/root w=((2:ℕ):ℝ)*w^(2-1)*1/(2*root w)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one,mul_one]
  rw [mul_div_mul_left _ _ two_ne_zero]

lemma curveU_hasDerivAt (w : ℝ) :
    HasDerivAt curveU (-curveU w*w/(1+w^2)) w := by
  have hp := root_positive w
  have hr := root_sq w
  convert (hasDerivAt_const w (Real.sqrt Q0)).div (root_hasDerivAt w) hp.ne' using 1
  · rfl
  · dsimp [curveU]
    field_simp [hp.ne',show (1+w^2:ℝ)≠0 by positivity]
    nlinarith only [congrArg (fun y : ℝ => Real.sqrt Q0*w*y) hr]

lemma v_hasDerivAt (w x : ℝ) :
    HasDerivAt (fun w => v w x) (curveU w*X w x/(1+w^2)) w := by
  convert ((curveU_hasDerivAt w).mul
    (((hasDerivAt_id w).mul_const (Real.sin x)).sub_const (Real.cos x))).const_add
      (1+Real.cos x) using 1
  · rfl
  · dsimp [X]
    field_simp [show (1+w^2:ℝ)≠0 by positivity]
    ring

lemma X_positive {w x : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) :
    0<X w x := by
  have ht := positive_trig hx
  have hp := mul_pos (show 0<w by linarith [hw.1]) (show 0<Real.cos x by linarith [ht.1])
  dsimp [X]
  linarith [ht.2.2.1]

lemma v_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun w => v w x) (Icc (261/1000:ℝ) 1) := monoOn_of_hasDeriv_nonneg
  (fun w _ => (v_hasDerivAt w x).continuousAt.continuousWithinAt)
  (fun w _ => v_hasDerivAt w x)
  (fun w hw => (div_pos (mul_pos (curveU_positive w)
    (X_positive (Ioo_subset_Icc_self hw) hx)) (by positivity)).le)

lemma v_one (x : ℝ) :
    v 1 x=1-(outerDiagonal-1/2)*Real.cos x+(outerDiagonal+1/2)*Real.sin x := by
  rw [v,curveU_one]
  ring

lemma v_upper {w x : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) :
    v w x<(8/5:ℝ) := by
  have hm := v_monotone hx hw (show (1:ℝ)∈Icc (261/1000) 1 by norm_num) hw.2
  beta_reduce at hm
  rw [v_one] at hm
  have ht := positive_trig hx
  have hneg := mul_le_mul
    (show (399/1000:ℝ)≤outerDiagonal-1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  have hpos := mul_le_mul
    (show outerDiagonal+1/2≤(7/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    (show Real.sin x≤(129/200:ℝ) by linarith [ht.2.2.2.1]) ht.2.2.1 (by norm_num)
  nlinarith

lemma X_square (w x : ℝ) : (X w x)^2≤1+w^2 := by
  have hs := sq_nonneg (Real.cos x-w*Real.sin x)
  have he : (X w x)^2+(Real.cos x-w*Real.sin x)^2=1+w^2 := by
    dsimp [X]
    linear_combination (1+w^2)*(Real.sin_sq_add_cos_sq x)
  linarith

lemma E_hasDerivAt (r : Row) (w x : ℝ) : HasDerivAt (fun w => E r w x) (ED r w x) w := by
  have hX : HasDerivAt (fun w => X w x) (Real.cos x) w := by
    have h := ((hasDerivAt_id w).mul_const (Real.cos x)).const_add (Real.sin x)
    rw [one_mul] at h
    exact h
  convert ((((((v_hasDerivAt w x).const_mul (P r)).div_const M).const_add (t r)).mul hX).sub
    ((hasDerivAt_id w).const_mul (p r))).sub_const (q r) using 1
  · rfl
  · dsimp [ED]
    field_simp [show M≠0 by norm_num [M],show (1+w^2:ℝ)≠0 by positivity]
    ring

lemma E_derivative (r : Row) (hr : r=1 ∨ r=2) {w x : ℝ}
    (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) : (1/25:ℝ)<ED r w x := by
  have ht := positive_trig hx
  have hcu := curveU_upper hw
  have hv := v_upper hw hx
  have hproj := mul_le_mul_of_nonneg_left hv.le (show 0≤Real.cos x by linarith [ht.1])
  have hcos : Real.cos x*v w x≤(8/5:ℝ) := by nlinarith [ht.2.1]
  have hterm : curveU w*(X w x)^2/(1+w^2)≤curveU w := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<1+w^2)).2
    exact mul_le_mul_of_nonneg_left (X_square w x) (curveU_positive w).le
  have hbrace : Real.cos x*v w x+curveU w*(X w x)^2/(1+w^2)<(703/200:ℝ) := by
    dsimp [M] at hcu
    linarith
  rcases hr with rfl | rfl <;> norm_num [ED,M,t,p,P] <;> linarith [ht.1]

lemma E_monotone (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun w => E r w x) (Icc (261/1000:ℝ) 1) := monoOn_of_hasDeriv_nonneg
  (fun w _ => (E_hasDerivAt r w x).continuousAt.continuousWithinAt)
  (fun w _ => E_hasDerivAt r w x)
  (fun w hw => by linarith [E_derivative r hr (Ioo_subset_Icc_self hw) hx])

lemma v_one_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1-(2/5)*Real.cos x+(7/5)*Real.sin x≤v 1 x := by
  have ht := positive_trig hx
  have hp := mul_nonneg
    (show 0≤9/10-outerDiagonal by linarith [outer_endpoint_bounds.2.2.2])
    (show 0≤Real.cos x-Real.sin x by linarith [ht.1,ht.2.2.2.1])
  rw [v_one]
  nlinarith

lemma polynomial_upper (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    E r 1 x≤polynomial r (Real.sin x) := by
  have ht := positive_trig hx
  have htrig := Real.sin_sq_add_cos_sq x
  have hz : 0<z r ∧ 0<t r-z r := by rcases hr with rfl | rfl <;> norm_num [z,M,P,t]
  have hsum : 0≤Real.cos x+Real.sin x := by linarith [ht.1,ht.2.2.1]
  have hv := mul_le_mul_of_nonneg_left (v_one_lower hx) (mul_nonneg hz.1.le hsum)
  have hcos : Real.cos x≤1-(Real.sin x)^2/2 := by
    nlinarith [sq_nonneg (1-Real.cos x)]
  have hlinear := mul_le_mul_of_nonneg_left hcos hz.2.le
  have hnegative := mul_le_mul_of_nonneg_left
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (mul_nonneg hz.1.le ht.2.2.1)
  rcases hr with rfl | rfl <;>
    norm_num [E,X,polynomial,c0,c1,c2,z,M,t,p,q,P] at * <;> nlinarith

lemma discriminant (r : Row) (hr : r=1 ∨ r=2) :
    0<c2 r ∧ (43/5000:ℝ)<4*c2 r*(-c0 r)-(c1 r)^2 := by
  rcases hr with rfl | rfl <;> norm_num [c0,c1,c2,z,M,t,p,q,P]

lemma polynomial_negative (r : Row) (hr : r=1 ∨ r=2) (s : ℝ) : polynomial r s<0 := by
  have hd := discriminant r hr
  have hs := sq_nonneg (2*c2 r*s-c1 r)
  have he : 4*c2 r*polynomial r s=
      4*c2 r*c0 r+(c1 r)^2-(2*c2 r*s-c1 r)^2 := by dsimp [polynomial]; ring
  have hn : 4*c2 r*polynomial r s<0 := by nlinarith
  by_contra! hnonneg
  have hh := mul_nonneg (show 0≤4*c2 r by linarith [hd.1]) hnonneg
  linarith

lemma endpoint_negative (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    E r 1 x<0 := (polynomial_upper r hr hx).trans_lt (polynomial_negative r hr (Real.sin x))

lemma actual_curveU {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : curveU (ratio B)=U B := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have hc := SecondWord.UW_circle (SecondWord.outer_domain hB)
  have ha : (U B)^2*(1+(ratio B)^2)=Q0 := by
    have h1 : U B*ratio B=W B := mul_div_cancel₀ _ hU.ne'
    rw [←hc]
    linear_combination (U B*ratio B+W B)*h1
  have hh := curveU_circle (ratio B)
  have he : ((curveU (ratio B))^2-(U B)^2)*(1+(ratio B)^2)=0 := by nlinarith only [ha,hh]
  have hs : (curveU (ratio B))^2=(U B)^2 := by
    rcases mul_eq_zero.mp he with he | he
    · linarith
    · exact False.elim ((show (1+(ratio B)^2:ℝ)≠0 by positivity) he)
  nlinarith [curveU_positive (ratio B)]

lemma actual_v {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) : v (ratio B) x=contact B x+1/2 := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have h1 : U B*ratio B=W B := mul_div_cancel₀ _ hU.ne'
  rw [v,actual_curveU hB]
  simp only [contact,U,W] at h1 ⊢
  linear_combination Real.sin x*h1

lemma original_upper (r : Row) {B x : ℝ} (hd : Domain B x) : targetFirst r B x≤E r (ratio B) x := by
  have hsource := outer_bounds (SameContact.arc_state hd.2.2)
  have hU := SecondWord.U_positive (SecondWord.outer_domain hd.2.2)
  have hupper : U (contact B x)≤M := by
    dsimp [U,M]
    linarith [hsource.2.1,ShortOuterZero.fine_axial_bounds.2]
  have hratio : (contact B x+1/2)/M≤ratio (contact B x) := by
    change (contact B x+1/2)/M≤(contact B x+1/2)/U (contact B x)
    apply (le_div_iff₀ hU).2
    have hh := mul_le_mul_of_nonneg_left hupper
      (show 0≤(contact B x+1/2)/M by dsimp [M]; linarith [hd.2.2.1])
    dsimp [M] at *
    nlinarith
  have hl := mul_le_mul_of_nonpos_left hratio (coefficient_bounds r).2.2.2.2.1
  have hk := K_positive hd.1 hd.2.1
  have hp := mul_le_mul_of_nonneg_right
    (show slope r (contact B x)≤t r+P r*(contact B x+1/2)/M by
      dsimp [slope]; rw [mul_div_assoc]; linarith only [hl]) hk.le
  rw [E,actual_v hd.1]
  dsimp [targetFirst,targetSlope,K,X] at *
  nlinarith only [hp]

/-- The entire physical target derivative is negative for the two later
rows; its actual source ratio and target circle are retained. -/
theorem target_negative (r : Row) (hr : r=1 ∨ r=2) {B x : ℝ} (hd : Domain B x) :
    targetFirst r B x<0 := by
  have hratio := SecondWord.outer_ratio_bounds hd.1
  have hw : ratio B∈Icc (261/1000:ℝ) 1 := ⟨hratio.1.le,hratio.2.1⟩
  have hm := E_monotone r hr hd.2.1 hw (show (1:ℝ)∈Icc (261/1000) 1 by norm_num) hw.2
  exact (original_upper r hd).trans_lt (hm.trans_lt (endpoint_negative r hr hd.2.1))

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.TargetRatio
