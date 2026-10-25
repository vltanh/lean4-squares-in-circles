module

public import SquaresInCircles.Eight.TableFree.OutsideERates

/-!
# The original D-circle term at a negative DE2 contact

Uncompiled source. The rotated D corner is recovered from its actual outer
q-circle. Its angular gain decreases over the complete allowed n interval,
so the endpoint n=7/10 provides the comparison required by the outside-E
transport. A separate rational reserve supplies the flat-core E case.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OutsideDContact

def ell (Y n : ℝ) : ℝ := 1+Real.cos n-Y
def root (q Y n : ℝ) : ℝ := Real.sqrt (q-(ell Y n)^2)
def gain (q Y n : ℝ) : ℝ := root q Y n-Real.sin n
def gainDerivative (q Y n : ℝ) : ℝ :=
  ell Y n*Real.sin n/root q Y n-Real.cos n

theorem bounds {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<ell Y n ∧ ell Y n≤3/2 ∧ 129/100<root q Y n ∧ 0<q-(ell Y n)^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hl0 : 0<ell Y n := by dsimp [ell]; linarith [hY.2]
  have hlU : ell Y n≤3/2 := by dsimp [ell]; linarith [hY.1]
  have hrad : (129/100 : ℝ)^2<q-(ell Y n)^2 := by
    dsimp [qLow] at hq
    nlinarith
  have hrad0 : 0<q-(ell Y n)^2 := (sq_nonneg _).trans_lt hrad
  have hroot : 129/100<root q Y n := by
    have hs := Real.sq_sqrt hrad0.le
    have hs0 := Real.sqrt_nonneg (q-(ell Y n)^2)
    dsimp [root]
    nlinarith
  exact ⟨hl0,hlU,hroot,hrad0⟩

theorem gain_hasDerivAt {q Y n : ℝ} (hrad : 0<q-(ell Y n)^2) :
    HasDerivAt (gain q Y) (gainDerivative q Y n) n := by
  have hl : HasDerivAt (ell Y) (-Real.sin n) n :=
    ((Real.hasDerivAt_cos n).const_add 1).sub_const Y
  have hr0 : root q Y n≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hr := ((hasDerivAt_const n q).fun_sub (hl.fun_pow 2)).sqrt hrad.ne'
  have F : HasDerivAt (gain q Y) _ n := hr.fun_sub (Real.hasDerivAt_sin n)
  convert F using 1
  dsimp [gainDerivative,root]
  field_simp
  push_cast
  ring

theorem gain_derivative_negative {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    gainDerivative q Y n<0 := by
  obtain ⟨hl0,hlU,hrL,hrad⟩ := bounds hq hY hn
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hlow : (129/100 : ℝ)*(7648/10000)<root q Y n*Real.cos n :=
    (mul_lt_mul_of_pos_right hrL (by norm_num : (0:ℝ)<7648/10000)).trans_le
      (mul_le_mul_of_nonneg_left hc.le (by linarith : 0≤root q Y n))
  have hupp := mul_le_mul hlU hs.le hs0 (by norm_num : (0:ℝ)≤3/2)
  unfold gainDerivative
  apply sub_neg.mpr
  apply (div_lt_iff₀ (by linarith : 0<root q Y n)).2
  nlinarith

theorem gain_antitone {q Y : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) :
    AntitoneOn (gain q Y) (Icc 0 (7/10 : ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro n hn
    exact (gain_hasDerivAt (bounds hq hY hn).2.2.2).continuousAt.continuousWithinAt
  · intro n hn
    exact gain_hasDerivAt (bounds hq hY (Ioo_subset_Icc_self hn)).2.2.2
  · intro n hn
    exact (gain_derivative_negative hq hY (Ioo_subset_Icc_self hn)).le

theorem gain_ge_cap {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    gain q Y (7/10)≤gain q Y n :=
  gain_antitone hq hY hn ⟨by norm_num,le_rfl⟩ hn.2

theorem gain_mono_tangent {q Y₁ Y₂ n : ℝ} (hq : qLow≤q)
    (hY₁ : Y₁∈Icc (1/2 : ℝ) (7/5)) (hY₂ : Y₂∈Icc (1/2 : ℝ) (7/5))
    (hn : n∈Icc 0 (7/10 : ℝ)) (hY : Y₁≤Y₂) :
    gain q Y₁ n≤gain q Y₂ n := by
  have hb₁ := bounds hq hY₁ hn
  have hb₂ := bounds hq hY₂ hn
  have hL : ell Y₂ n≤ell Y₁ n := by dsimp [ell]; linarith
  have hsq := pow_le_pow_left₀ hb₂.1.le hL 2
  have hroot := Real.sqrt_le_sqrt (show q-(ell Y₁ n)^2≤q-(ell Y₂ n)^2 by linarith)
  exact sub_le_sub_right hroot (Real.sin n)

theorem gain_gt_core_speed {q Y n : ℝ} (hq : qLow≤q)
    (hY : Y∈Icc (1/2 : ℝ) (7/5)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    87/100<gain q Y n := by
  have hcap := gain_ge_cap hq hY hn
  have hb := bounds hq hY (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
  have hc := cos_upper_four (show (0:ℝ)≤7/10 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hcomb : Real.cos (7/10 : ℝ)+(87/50)*Real.sin (7/10 : ℝ)<19/10 := by
    norm_num at hc hs
    linarith
  have hcos0 : 0<Real.cos (7/10 : ℝ) := transport_cos_pos (by norm_num)
  have hsin0 : 0≤Real.sin (7/10 : ℝ) :=
    (transport_trig (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).2.2.1
  have hell : ell Y (7/10)≤1/2+Real.cos (7/10 : ℝ) := by
    dsimp [ell]
    linarith [hY.1]
  have hellsq := pow_le_pow_left₀ hb.1.le hell 2
  have hrootSq := Real.sq_sqrt hb.2.2.2.le
  have hqL := hq
  dsimp [qLow] at hqL
  have hroot : Real.sin (7/10 : ℝ)+87/100<root q Y (7/10) := by
    dsimp [root] at hb hrootSq ⊢
    nlinarith [Real.sin_sq_add_cos_sq (7/10 : ℝ)]
  dsimp only [gain] at hcap ⊢
  linarith

/-- An actual DE2 equality identifies the positive rotated D coordinate
with the same-circle square root. Mere containment is not used here. -/
theorem actual_contact_gain {q b n : ℝ} {D : SignedPoint}
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hn : n∈Icc 0 (7/10 : ℝ))
    (hcontact : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n=gain q (b+1/2) n := by
  let X := D.a+1/2
  let Y := 1/2-D.y
  let V := X*Real.sin n+Y*Real.cos n
  have ht := transport_trig hn
  have hc : 0<Real.cos n := by linarith [ht.1]
  have hs : 0≤Real.sin n := ht.2.2.1
  have hX : 0<X := by dsimp [X]; linarith [hDs.1]
  have hY : 0<Y := by dsimp [Y]; linarith
  have hV : 0<V := add_pos_of_nonneg_of_pos (mul_nonneg hX.le hs) (mul_pos hY hc)
  have heq : X*Real.cos n-Y*Real.sin n=ell (b+1/2) n := by
    dsimp [X,Y,ell]
    linarith
  have hnorm : X^2+Y^2=q := by
    simpa [X,Y,SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hDy,
      sub_eq_add_neg,add_comm] using hDo
  have hrotation : (X*Real.cos n-Y*Real.sin n)^2+V^2=q := by
    have hid : (X*Real.cos n-Y*Real.sin n)^2+V^2=
        (X^2+Y^2)*(Real.sin n^2+Real.cos n^2) := by dsimp [V]; ring
    rw [hid,Real.sin_sq_add_cos_sq,hnorm]
    ring
  have hrad : q-(ell (b+1/2) n)^2=V^2 := by rw [heq] at hrotation; linarith
  unfold gain root
  rw [hrad,Real.sqrt_sq_eq_abs,abs_of_pos hV]
  dsimp [V,X,Y]
  ring

theorem fixed_rate_positive {n : ℝ} {D : SignedPoint}
    (hDa : 1/2<D.a) (hDy : D.y≤0) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<(D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hDa.le) hs0)
    (mul_pos (by linarith) (by linarith))

end OutsideDContact
end SquaresInCircles.Eight.TableFree
