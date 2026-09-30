module
public import SquaresInCircles.Six.Analytic.SouthOuterTail.Profile

@[expose] public section

/-!
# Retain the actual diagonal center during the two wing reductions

The OWN-W proof uses CW weight 5/8, CS weight 1, WD weight 2/5 and DS weight
3/10. The change from 3/5 is intentional. With 1/2<=aD<=1113/1000 and
|bD|<=23/100, the raw stress is a positive first harmonic in each wing angle.
Thus v in [0,11/25] and s in [11/25,2/3] reduce to four corners while the
same actual diagonal coordinates are retained. Only then are disk supports
used. This avoids the false OWN-W corner of the earlier scalar majorant.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail.Own

 def weightW : ℝ := 5/8
 def westRootUpper : ℝ := 371021/500000
 def constant : ℝ :=
  93/40-CandidateWestTail.radiusBound*(westRootUpper+southRootUpper)

 def raw (upper : Bool) (v s d a b : ℝ) : ℝ :=
  constant+weightW*(1/2-face upper)*Real.cos v+weightW*B*Real.sin v+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*((1/2-b)*Real.cos (d+v)+(1/2-a)*Real.sin (d+v))+
    nu*((1/2-a)*Real.cos (d-s)+(1/2+b)*Real.sin (d-s))

 def vA (upper : Bool) (d a b : ℝ) : ℝ :=
  weightW*(1/2-face upper)+mu*((1/2-b)*Real.cos d+(1/2-a)*Real.sin d)
 def vB (d a b : ℝ) : ℝ :=
  weightW*B+mu*(-(1/2-b)*Real.sin d+(1/2-a)*Real.cos d)
 def vK (upper : Bool) (s d a b : ℝ) : ℝ :=
  constant+A*Real.cos s+(1/2+face upper)*Real.sin s+
    nu*((1/2-a)*Real.cos (d-s)+(1/2+b)*Real.sin (d-s))

 def sA (d a b : ℝ) : ℝ :=
  A+nu*((1/2-a)*Real.cos d+(1/2+b)*Real.sin d)
 def sB (upper : Bool) (d a b : ℝ) : ℝ :=
  1/2+face upper+nu*((1/2-a)*Real.sin d-(1/2+b)*Real.cos d)
 def sK (upper : Bool) (v d a b : ℝ) : ℝ :=
  constant+weightW*(1/2-face upper)*Real.cos v+weightW*B*Real.sin v+
    mu*((1/2-b)*Real.cos (d+v)+(1/2-a)*Real.sin (d+v))

lemma raw_v_identity (upper : Bool) (v s d a b : ℝ) :
    raw upper v s d a b=vK upper s d a b+vA upper d a b*Real.cos v+
      vB d a b*Real.sin v := by
  dsimp [raw,vK,vA,vB]
  rw [Real.cos_add,Real.sin_add]
  ring

lemma raw_s_identity (upper : Bool) (v s d a b : ℝ) :
    raw upper v s d a b=sK upper v d a b+sA d a b*Real.cos s+
      sB upper d a b*Real.sin s := by
  dsimp [raw,sK,sA,sB]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma unit_harmonic_upper {x y : ℝ} (hxy : x^2+y^2=1) :
    (73/100)*x+(613/1000)*y ≤ 191/200 := by
  have hid : ((73/100)*x+(613/1000)*y)^2+
      ((73/100)*y-(613/1000)*x)^2=(73/100:ℝ)^2+(613/1000:ℝ)^2 := by
    linear_combination ((73/100:ℝ)^2+(613/1000:ℝ)^2)*hxy
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < (73/100)*x+(613/1000)*y+191/200 by linarith)
  nlinarith [sq_nonneg ((73/100)*y-(613/1000)*x)]

private lemma diagonal_trig {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    69/100 ≤ Real.cos d ∧ 0 ≤ Real.sin d := by
  have hsq := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0 ≤ 11/14+d by linarith [hd.1])
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := d)],
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hd.1])
      (by linarith [hd.2,Real.pi_gt_d2])⟩

/-- All four coefficients have uniform positive reserves on the entire rectangle. -/
lemma raw_coefficients (upper : Bool) {d a b : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (ha : 1/2 ≤ a ∧ a ≤ 1113/1000) (hb : -(23/100) ≤ b ∧ b ≤ 23/100) :
    (0 ≤ vA upper d a b ∧ 0 ≤ vB d a b) ∧
    (0 ≤ sA d a b ∧ 0 ≤ sB upper d a b) := by
  have ht := diagonal_trig hd
  have hc : 0 ≤ Real.cos d := by linarith [ht.1]
  have hs : 0 ≤ Real.sin d := ht.2
  have hamin : 0 ≤ a-1/2 := by linarith [ha.1]
  have has : (a-1/2)*Real.sin d ≤ 613/1000 := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_le_one d) hamin
    nlinarith only [h,ha.2]
  have hac : (a-1/2)*Real.cos d ≤ 613/1000 := by
    have h := mul_le_mul_of_nonneg_left (Real.cos_le_one d) hamin
    nlinarith only [h,ha.2]
  have hbc := mul_nonneg (show 0 ≤ (1/2-b)-27/100 by linarith [hb.2]) hc
  have hbs := mul_nonneg (show 0 ≤ 1/2+b by linarith [hb.1]) hs
  have v1 := mul_nonneg (show 0 ≤ 73/100-(1/2-b) by linarith [hb.1]) hs
  have v2 := mul_nonneg (show 0 ≤ 613/1000-(a-1/2) by linarith [ha.2]) hc
  have vu := unit_harmonic_upper (Real.sin_sq_add_cos_sq d)
  have vbound : (1/2-b)*Real.sin d+(a-1/2)*Real.cos d ≤ 191/200 := by
    nlinarith only [v1,v2,vu]
  have s1 := mul_nonneg (show 0 ≤ 73/100-(1/2+b) by linarith [hb.2]) hc
  have s2 := mul_nonneg (show 0 ≤ 613/1000-(a-1/2) by linarith [ha.2]) hs
  have su := unit_harmonic_upper (x := Real.cos d) (y := Real.sin d)
    (by nlinarith only [Real.sin_sq_add_cos_sq d])
  have sbound : (a-1/2)*Real.sin d+(1/2+b)*Real.cos d ≤ 191/200 := by
    nlinarith only [s1,s2,su]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · cases upper <;> dsimp [vA,weightW,face,mu] <;>
      nlinarith only [has,hbc,ht.1]
  · dsimp [vB,weightW,B,mu]
    nlinarith only [vbound]
  · dsimp [sA,A,nu]
    nlinarith only [hac,hbs]
  · cases upper <;> dsimp [sB,face,nu] <;>
      nlinarith only [sbound]

lemma extend_raw_south (upper : Bool) {v s d a b : ℝ}
    (hs : 11/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (ha : 1/2 ≤ a ∧ a ≤ 1113/1000) (hb : -(23/100) ≤ b ∧ b ≤ 23/100)
    (hl : 0 < raw upper v (11/25) d a b)
    (hu : 0 < raw upper v (2/3) d a b) :
    0 < raw upper v s d a b := by
  have hc := (raw_coefficients upper hd ha hb).2
  rw [raw_s_identity] at hl hu ⊢
  have h := trig_lower_of_endpoints hc.1 hc.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) hs (C := -sK upper v d a b)
    (by linarith) (by linarith)
  linarith

lemma extend_raw_west (upper : Bool) {v s d a b : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 11/25) (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (ha : 1/2 ≤ a ∧ a ≤ 1113/1000) (hb : -(23/100) ≤ b ∧ b ≤ 23/100)
    (hl : 0 < raw upper 0 s d a b)
    (hu : 0 < raw upper (11/25) s d a b) :
    0 < raw upper v s d a b := by
  have hc := (raw_coefficients upper hd ha hb).1
  rw [raw_v_identity] at hl hu ⊢
  have h := trig_lower_of_endpoints hc.1 hc.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) hv (C := -vK upper s d a b)
    (by linarith) (by linarith)
  linarith

end SquaresInCircles.Six.Analytic.SouthOuterTail.Own
