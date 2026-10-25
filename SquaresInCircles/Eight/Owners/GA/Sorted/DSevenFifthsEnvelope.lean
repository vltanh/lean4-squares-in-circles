module

public import SquaresInCircles.Eight.Owners.GA.Sorted.DSevenFifthsMixed

/-!
# Eight squares: the signed two-angle sorted-D minorant

At a fixed total of equal signs the force norm is constant. The interior support is concave in the
allocation, and the tangent-zero branch is either decreasing or absent. The endpoint theorems of
the two mixed quadrants therefore cover the two quadrants of equal signs (`positive_path_lower`,
`negative_path_lower`), weak ties included, and `lower` holds on the whole signed domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

def equalBase (c n t : ℝ) (positive : Bool) : ℝ :=
  c*(Real.cos t+Real.sin t-1)/2+(Real.cos (n-t)+Real.sin (n-t)-1)/2+
    (1+c)*GlobalGA.Secondary.diagonal+(if positive then slope*n else -vstar n)

theorem positive_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t true-sortedSupport (forceA c t (n-t)) (forceB c t (n-t))=
      D c t (n-t)+slope*n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂]
  simp only [equalBase,↓reduceIte]
  ring

theorem negative_base_identity {c n t : ℝ}
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    equalBase c n t false-sortedSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      D c (-t) (-(n-t))-vstar n := by
  have h₁ : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have h₂ : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  rw [PositiveBT3.D,edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂]
  simp only [equalBase,Bool.false_eq_true,↓reduceIte]
  ring

theorem positive_full_identity (c n t : ℝ) :
    equalBase c n t true-fullSupport (forceA c t (n-t)) (forceB c t (n-t))=
      c*(Real.cos t+Real.sin t-1)+Real.cos (n-t)+Real.sin (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n := by
  rw [fullSupport,force_norm,show t+(n-t)=n by ring]
  dsimp [equalBase,forceA,forceB]
  ring

theorem negative_full_identity (c n t : ℝ) :
    equalBase c n t false-fullSupport (forceA c (-t) (-(n-t))) (forceB c (-t) (-(n-t)))=
      c*(Real.cos t-1)+Real.cos (n-t)-1+
      (1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n := by
  rw [fullSupport,force_norm,show -t+(-(n-t))= -n by ring]
  dsimp [equalBase,forceA,forceB]
  rw [Real.cos_neg,Real.cos_neg,Real.sin_neg,Real.sin_neg]
  ring

def positiveDerivative (c n t : ℝ) : ℝ :=
  c*(Real.cos t-Real.sin t)-(Real.cos (n-t)-Real.sin (n-t))
def negativeDerivative (c n t : ℝ) : ℝ := -c*Real.sin t+Real.sin (n-t)

theorem positive_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-
      fullSupport (forceA c x (n-x)) (forceB c x (n-x))) (positiveDerivative c n t) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).fun_add (hy.cos.fun_add hy.sin)).sub_const 1 |>.add_const
      ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n)
  have he : (fun x => equalBase c n x true-
      fullSupport (forceA c x (n-x)) (forceB c x (n-x)))=fun x =>
      c*(Real.cos x+Real.sin x-1)+(Real.cos (n-x)+Real.sin (n-x))-1+
        ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c n+slope*n) := by
    funext x
    rw [positive_full_identity]
    ring
  rw [he]
  exact h.congr_deriv (by dsimp only [positiveDerivative]; ring)

theorem positive_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (positiveDerivative c n) (-c*PositiveAngularEnvelope.phi t-PositiveAngularEnvelope.phi (n-t)) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((Real.hasDerivAt_cos t).fun_sub (Real.hasDerivAt_sin t)).const_mul c).fun_sub
    (hy.cos.fun_sub hy.sin)
  show HasDerivAt (fun x => c*(Real.cos x-Real.sin x)-(Real.cos (n-x)-Real.sin (n-x))) _ t
  exact h.congr_deriv (by simp only [PositiveAngularEnvelope.phi]; ring)

theorem negative_full_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x false-
      fullSupport (forceA c (-x) (-(n-x))) (forceB c (-x) (-(n-x))))
      (negativeDerivative c n t) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have h := (((((Real.hasDerivAt_cos t).sub_const 1).const_mul c).fun_add hy.cos).sub_const
    1).add_const ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n)
  have he : (fun x => equalBase c n x false-
      fullSupport (forceA c (-x) (-(n-x))) (forceB c (-x) (-(n-x))))=fun x =>
      c*(Real.cos x-1)+Real.cos (n-x)-1+
        ((1+c)*(GlobalGA.Secondary.diagonal+1/2)-R*pairNorm 1 c (-n)-vstar n) := by
    funext x
    rw [negative_full_identity]
    ring
  rw [he]
  exact h.congr_deriv (by dsimp only [negativeDerivative]; ring)

theorem negative_derivative_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeDerivative c n) (-c*Real.cos t-Real.cos (n-t)) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  show HasDerivAt (fun x => -c*Real.sin x+Real.sin (n-x)) _ t
  exact (((Real.hasDerivAt_sin t).const_mul (-c)).fun_add hy.sin).congr_deriv (by ring)

theorem positive_axis_hasDerivAt (c n t : ℝ) :
    HasDerivAt (fun x => equalBase c n x true-forceA c x (n-x)*axial)
      (-c*((axial-1/2)*Real.cos t+(1/2)*Real.sin t)-
        ((axial-1/2)*Real.sin (n-t)+(1/2)*Real.cos (n-t))) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have hb := ((((((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).sub_const 1).const_mul
    c).div_const 2).fun_add (((hy.cos.fun_add hy.sin).sub_const 1).div_const 2)).add_const
      ((1+c)*GlobalGA.Secondary.diagonal+slope*n)
  have hf := ((Real.hasDerivAt_sin t).const_mul c).fun_add hy.cos
  have he : (fun x => equalBase c n x true-forceA c x (n-x)*axial)=fun x =>
      (c*(Real.cos x+Real.sin x-1)/2+(Real.cos (n-x)+Real.sin (n-x)-1)/2+
        ((1+c)*GlobalGA.Secondary.diagonal+slope*n))-(c*Real.sin x+Real.cos (n-x))*axial := by
    funext x
    simp only [equalBase,forceA,↓reduceIte]
    ring
  rw [he]
  exact (hb.fun_sub (hf.mul_const axial)).congr_deriv (by ring)

theorem positive_axis_antitone {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    AntitoneOn (fun x => equalBase c n x true-forceA c x (n-x)*axial) (Icc 0 n) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (positive_axis_hasDerivAt c n t).continuousAt.continuousWithinAt
  · intro t ht
    exact positive_axis_hasDerivAt c n t
  · intro t ht
    have ht' : t∈Icc 0 frameCap := ⟨ht.1.le,ht.2.le.trans hn.2⟩
    have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
    have hb := axis_bracket_lower ht'
    have hs := (transport_trig hy).2.2.1
    have hcos : 0≤Real.cos (n-t) := by linarith [(transport_trig hy).1]
    have hp := mul_nonneg (show 0≤axial-1/2 by linarith [axial_bounds.1]) hs
    have hcp := mul_nonneg (show 0≤c by linarith [hc.1]) (show
      0≤(axial-1/2)*Real.cos t+(1/2)*Real.sin t by linarith)
    linarith

theorem equal_domains {n t : ℝ} (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    SignedDomain t (n-t) ∧ SignedDomain (-t) (-(n-t)) := by
  have hy : 0≤n-t := by linarith [ht.2]
  have hf : (0:ℝ)≤frameCap := by norm_num [frameCap]
  simp only [SignedDomain,positiveTotal,negativeTotal,positivePart,negativePart,
    max_eq_left ht.1,max_eq_left hy,max_eq_right (neg_nonpos.mpr ht.1),
    max_eq_right (neg_nonpos.mpr hy),neg_neg]
  refine ⟨⟨by linarith [hn.2],by linarith⟩,⟨by linarith,by linarith [hn.2]⟩⟩

theorem positive_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : -slope*n≤D c t (n-t) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0≤equalBase c n 0 true-sortedSupport (forceA c 0 n) (forceB c 0 n) := by
    have hh := positive_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := mixed_reverse_lower hc hn hz
    simp only [sub_zero,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hright : 0≤equalBase c n n true-sortedSupport (forceA c n 0) (forceB c n 0) := by
    have hh := positive_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_forward_lower hc hn hz
    simp only [sub_self,neg_zero,vstar,V_zero] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x true) (f:=fun x => forceA c x (n-x)) (g:=fun x => forceB c x (n-x))
    (df:=positiveDerivative c n) (ddf:=fun x => -c*PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (n-x)) (κ:=1)
    (by dsimp [equalBase]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => positive_force_positive hc ⟨hx.1,hx.2.trans hn.2⟩
      ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).1
      rw [edgeWidth_positive_formula h₁,edgeWidth_positive_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),add_zero,vstar,V_zero,sub_zero] at hd
      dsimp [equalBase]
      linarith)
    (fun x hx _ => by
      have ha := positive_axis_antitone hc hn hx ⟨hn.1,le_rfl⟩ hx.2
      have hp := positive_force_positive (y:=0) hc hn (by norm_num [frameCap])
      have hs := axis_support_lower hp.1 hp.2
      simp only [sub_self] at ha
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => positive_full_hasDerivAt c n x)
    (fun x _ => positive_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := CorrelatedSameBlock.one_le_phi (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)
      have h₂ := CorrelatedSameBlock.one_le_phi (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])
      have hm := mul_le_mul_of_nonneg_left h₁ (by linarith [hc.1] : 0≤c)
      linarith [hc.1])
  rw [positive_base_identity hn ht] at hbound
  linarith

def negativeAxisGate (c n t : ℝ) : ℝ :=
  (axial+1/2)*forceB c (-t) (-(n-t))-forceA c (-t) (-(n-t))/2

theorem negative_axis_gate_hasDerivAt (c n t : ℝ) :
    HasDerivAt (negativeAxisGate c n)
      ((axial+1/2)*forceA c (-t) (-(n-t))+forceB c (-t) (-(n-t))/2) t := by
  have hy : HasDerivAt (fun x : ℝ => n-x) (-1) t := (hasDerivAt_id' t).const_sub n
  have hf := ((Real.hasDerivAt_sin t).const_mul (-c)).fun_add hy.cos
  have hg := ((Real.hasDerivAt_cos t).const_mul c).fun_sub hy.sin
  have he : negativeAxisGate c n=fun x =>
      (axial+1/2)*(c*Real.cos x-Real.sin (n-x))-(-c*Real.sin x+Real.cos (n-x))/2 := by
    funext x
    simp only [negativeAxisGate,forceA,forceB,Real.cos_neg,Real.sin_neg]
    ring
  rw [he]
  exact ((hg.const_mul (axial+1/2)).fun_sub (hf.div_const 2)).congr_deriv
    (by simp only [forceA,forceB,Real.cos_neg,Real.sin_neg]; ring)

theorem negative_axis_gate_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : 0<negativeAxisGate c n t := by
  have hmono : MonotoneOn (negativeAxisGate c n) (Icc 0 n) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (negative_axis_gate_hasDerivAt c n x).continuousAt.continuousWithinAt
    · intro x hx
      exact negative_axis_gate_hasDerivAt c n x
    · intro x hx
      have hp := negative_force_positive hc hn (Ioo_subset_Icc_self hx)
      have hm := mul_nonneg (show 0≤axial+1/2 by linarith [axial_bounds.1]) hp.1.le
      linarith [hp.2]
  have hs := (transport_trig hn).2.2.2.1
  have hA : (19/10:ℝ)<axial+1/2 := by linarith [axial_bounds.1]
  have hpos : 0<c-Real.sin n := by linarith [hc.1]
  have hm := mul_lt_mul_of_pos_right hA hpos
  have hz : 0<negativeAxisGate c n 0 := by
    simp only [negativeAxisGate,forceA,forceB,neg_zero,sub_zero,Real.cos_zero,
      Real.sin_zero,Real.cos_neg,Real.sin_neg,mul_zero,zero_add,mul_one]
    nlinarith [Real.cos_le_one n,hc.1]
  exact hz.trans_le (hmono ⟨le_rfl,hn.1⟩ ht ht.1)

theorem negative_path_lower {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) : vstar n≤D c (-t) (-(n-t)) := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hleft : 0≤equalBase c n 0 false-sortedSupport (forceA c 0 (-n)) (forceB c 0 (-n)) := by
    have hh := negative_base_identity (c:=c) hn (show (0:ℝ)∈Icc 0 n from ⟨le_rfl,hn.1⟩)
    have hs := one_angle_lower hc hn
    simp only [sub_zero,neg_zero] at hh
    linarith
  have hright : 0≤equalBase c n n false-sortedSupport (forceA c (-n) 0) (forceB c (-n) 0) := by
    have hh := negative_base_identity (c:=c) hn (show n∈Icc 0 n from ⟨hn.1,le_rfl⟩)
    have hs := mixed_reverse_lower hc hz hn
    simp only [sub_self,neg_zero,mul_zero,neg_zero,zero_add] at hh hs
    linarith
  have hbound := support_path_lower
    (base:=fun x => equalBase c n x false) (f:=fun x => forceA c (-x) (-(n-x)))
    (g:=fun x => forceB c (-x) (-(n-x))) (df:=negativeDerivative c n)
    (ddf:=fun x => -c*Real.cos x-Real.cos (n-x)) (κ:=1/2)
    (by dsimp [equalBase]; fun_prop) (by dsimp [forceA]; fun_prop)
    (by dsimp [forceB]; fun_prop) ht (by norm_num)
    (fun x hx => negative_force_positive hc hn hx)
    (fun x hx => by
      have h₁ : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hn.2⟩
      have h₂ : n-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [hx.1,hn.2]⟩
      have hd := diagonal_residual hc (equal_domains hn hx).2
      rw [edgeWidth_negative_formula h₁,edgeWidth_negative_formula h₂] at hd
      simp only [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left h₁.1,max_eq_left h₂.1,max_eq_right (neg_nonpos.mpr h₁.1),
        max_eq_right (neg_nonpos.mpr h₂.1),neg_neg,add_zero,mul_zero,
        show x+(n-x)=n by ring] at hd
      dsimp [equalBase]
      linarith)
    (fun x hx ha => by
      have hp := negative_axis_gate_positive hc hn hx
      dsimp [negativeAxisGate] at hp
      linarith)
    (by simpa using hleft) (by simpa using hright)
    (fun x _ => negative_full_hasDerivAt c n x)
    (fun x _ => negative_derivative_hasDerivAt c n x)
    (fun x hx => by
      have h₁ := (transport_trig (show x∈Icc 0 frameCap from ⟨hx.1.le,hx.2.le.trans hn.2⟩)).1
      have h₂ := (transport_trig (show n-x∈Icc 0 frameCap by
        constructor <;> linarith [hx.1,hx.2,hn.2])).1
      have hm := mul_le_mul_of_nonneg_right hc.1 (by linarith : 0≤Real.cos x)
      linarith)
  rw [negative_base_identity hn ht] at hbound
  linarith

/-- The minorant `-slope * positiveTotal x y + vstar (negativeTotal x y) ≤ D c x y` on the whole
signed domain, with the sorted zero-angle support and every equality transition. -/
theorem lower {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    -slope*positiveTotal x y+vstar (negativeTotal x y)≤D c x y := by
  have ha := signed_domain_angles hxy
  by_cases hx : 0≤x
  · by_cases hy : 0≤y
    · have hn : x+y∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx hy,?_⟩
        simpa [positiveTotal,positivePart,max_eq_left hx,max_eq_left hy] using hxy.1
      have hh := positive_path_lower hc hn (show x∈Icc 0 (x+y) by constructor <;> linarith)
      simp only [show x+y-x=y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy,max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (neg_nonpos.mpr hy),vstar] using hh
    · have hy' : 0≤ -y := by linarith
      have hh := mixed_forward_lower hc ⟨hx,(le_abs_self x).trans ha.1⟩
        ⟨hy',(neg_le_abs y).trans ha.2⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx,max_eq_left hy',max_eq_right (neg_nonpos.mpr hx),
        max_eq_right (le_of_not_ge hy)] using hh
  · have hx' : 0≤ -x := by linarith
    by_cases hy : 0≤y
    · have hh := mixed_reverse_lower hc ⟨hy,(le_abs_self y).trans ha.2⟩
        ⟨hx',(neg_le_abs x).trans ha.1⟩
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hy,max_eq_left hx',max_eq_right (neg_nonpos.mpr hy),
        max_eq_right (le_of_not_ge hx)] using hh
    · have hy' : 0≤ -y := by linarith
      have hn : -x+(-y)∈Icc 0 frameCap := by
        refine ⟨add_nonneg hx' hy',?_⟩
        simpa [negativeTotal,negativePart,max_eq_left hx',max_eq_left hy'] using hxy.2
      have hh := negative_path_lower hc hn
        (show -x∈Icc 0 (-x+(-y)) by constructor <;> linarith)
      simp only [neg_neg,show -x+(-y)-(-x)= -y by ring] at hh
      simpa [positiveTotal,negativeTotal,positivePart,negativePart,
        max_eq_left hx',max_eq_left hy',max_eq_right (le_of_not_ge hx),
        max_eq_right (le_of_not_ge hy)] using hh

end SquaresInCircles.Eight.GlobalGA.SortedDSevenFifths
