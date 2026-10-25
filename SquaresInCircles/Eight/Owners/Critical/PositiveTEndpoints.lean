module

public import SquaresInCircles.Eight.Owners.Critical.PositiveTDerivative
public import SquaresInCircles.Eight.Owners.Critical.PositiveTEnvelope
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport

/-!
# Eight squares: the two original fixed-z faces of the critical contact stress

The BT baseline is at least
the TD baseline by the exact comparison of norm increments. The G
face is at least the E face, strictly so when its G error is positive.
The remaining E/TD expression is exactly the derivative scalar.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTEndpoints
open Candidate CriticalPositiveTCoefficients ExceptionalContactStress
open ExceptionalContactSupport PositiveAngularEnvelope OrdinaryAngleConcavity

theorem contact_coefficient_negative {R eta : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) : 1+2*eta-R*Real.sqrt (1+eta^2)<0 := by
  have hs : (1:ℝ)≤Real.sqrt (1+eta^2) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤1+eta^2 by nlinarith [sq_nonneg eta])
  have hm := mul_le_mul_of_nonneg_left hs hR
  have hr := SoleAngleGrowth.radius_lower hR hQL
  linarith

theorem contact_le_three {R eta a : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) (ha : a∈Icc 0 (4/25:ℝ)) : contactScalar R eta a≤3 := by
  have hn := contact_coefficient_negative hR hQL heta
  have hs := (transport_trig (show a∈Icc 0 frameCap from
    ⟨ha.1,by dsimp [frameCap]; linarith [ha.2]⟩)).2.2.1
  have hp := mul_nonpos_of_nonpos_of_nonneg hn.le hs
  dsimp [contactScalar]
  linarith [Real.cos_le_one a]

theorem contact_lt_three {R eta a : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) (ha : a∈Ioc 0 (4/25:ℝ)) : contactScalar R eta a<3 := by
  have hn := contact_coefficient_negative hR hQL heta
  have hs0 := Real.sin_ge_sub_cube ha.1.le
  have ha2 : a^2≤(4/25:ℝ)^2 := pow_le_pow_left₀ ha.1.le ha.2 2
  have ha3 := mul_le_mul_of_nonneg_right ha2 ha.1.le
  have hs : 0<Real.sin a := by nlinarith [ha.1]
  have hp := mul_neg_of_neg_of_pos hn hs
  dsimp [contactScalar]
  linarith [Real.cos_le_one a]

theorem td_le_bt {R t z k l c m eta x e : ℝ} (hR : 0≤R)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) :
    ExceptionalPositiveTStress.baseline true R k l c eta z x e≤
      ExceptionalPositiveTStress.baseline false R k l c eta z x e := by
  have hn := PositiveSplitComparison.norm_increment_comparison h.ell_pos.le
    (show l≤1 by linarith [h.ell_upper]) (show 0<c by linarith [h.c_lower]) h.c_le_m
  have hh := mul_le_mul_of_nonneg_left hn hR
  simp only [ExceptionalPositiveTStress.baseline,ExceptionalPositiveTStress.bWeight,
    ExceptionalPositiveTStress.tWeight,ite_true,Bool.false_eq_true,ite_false,
    SoleEStress.zeroNorms,pairNorm_zero,one_pow,← hm]
  linarith

theorem td_le_row {R t z k l c m eta x e : ℝ} (td : Bool) (hR : 0≤R)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) :
    ExceptionalPositiveTStress.baseline true R k l c eta z x e≤
      ExceptionalPositiveTStress.baseline td R k l c eta z x e := by
  cases td
  · exact td_le_bt hR h hm
  · exact le_rfl

theorem split_difference (td : Bool) (R k l c eta z a : ℝ) :
    ExceptionalPositiveTStress.baseline td R k l c eta z a 0-
      ExceptionalPositiveTStress.baseline td R k l c eta z 0 a=
      (1-k)*(3-contactScalar R eta a)+
        R*(pairNorm (tilt eta a) k 0-pairNorm 1 (k*tilt eta a) 0) := by
  simp [ExceptionalPositiveTStress.baseline,SoleEStress.zeroNorms,ExceptionalContactStress.tilt,
    contactScalar]
  ring_nf

theorem E_le_G {R t z k l c m eta : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (h : Bounds t z k l c m eta) :
    ExceptionalPositiveTStress.baseline td R k l c eta z 0 (t-z)≤
      ExceptionalPositiveTStress.baseline td R k l c eta z (t-z) 0 := by
  have ha : t-z∈Icc 0 t := ⟨by linarith [h.z_le],by linarith [h.z_nonneg]⟩
  have hn := endpoint_norm_order
    (show k∈Icc 0 1 from ⟨by linarith [h.k_lower],by linarith [h.k_upper]⟩)
    (h.tilt ha).1
  have hC := contact_le_three hR hQL h.eta_upper.le ⟨ha.1,ha.2.trans h.angle_upper⟩
  have hfirst := mul_nonneg (show 0≤1-k by linarith [h.k_upper]) (sub_nonneg.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hn)
  have hid := split_difference td R k l c eta z (t-z)
  linarith

theorem E_lt_G {R t z k l c m eta : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (h : Bounds t z k l c m eta) (ha : 0<t-z) :
    ExceptionalPositiveTStress.baseline td R k l c eta z 0 (t-z)<
      ExceptionalPositiveTStress.baseline td R k l c eta z (t-z) 0 := by
  have ha' : t-z∈Icc 0 t := ⟨ha.le,by linarith [h.z_nonneg]⟩
  have hn := endpoint_norm_order
    (show k∈Icc 0 1 from ⟨by linarith [h.k_lower],by linarith [h.k_upper]⟩)
    (h.tilt ha').1
  have hC := contact_lt_three hR hQL h.eta_upper.le ⟨ha,ha'.2.trans h.angle_upper⟩
  have hfirst := mul_pos (show 0<1-k by linarith [h.k_upper]) (sub_pos.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hn)
  have hid := split_difference td R k l c eta z (t-z)
  linarith

theorem scalar_eq (q t z : ℝ) :
    CriticalPositiveTDerivative.scalar q t z=
      ExceptionalPositiveTStress.baseline true (Real.sqrt q)
        (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
        (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) z 0 (t-z)+
      V (Real.sqrt q) (CriticalPositiveTDerivative.ell q t z) (CriticalPositiveTDerivative.m q t z) t := by
  rw [CriticalPositiveTDerivative.scalar_formula]
  simp only [ExceptionalPositiveTStress.baseline,ExceptionalPositiveTStress.bWeight,
    ExceptionalPositiveTStress.tWeight,SoleEStress.zeroNorms,OrdinaryAngleConcavity.V,pairNorm,
    CriticalPositiveTDerivative.p,CriticalPositiveTDerivative.m,ExceptionalContactStress.tilt,
    contactScalar,↓reduceIte,Real.sin_zero,Real.cos_zero,Real.sin_neg]
  ring_nf

theorem value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R t z k l c m eta x : ℝ} (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) (hx : x∈Icc 0 (t-z))
    (hsource : ExceptionalPositiveTStress.primary C td=z)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t)
    (hcontact : Contact C) :
    ExceptionalPositiveTStress.baseline td R k l c eta z x (t-z-x)+V R l m t≤
      ExceptionalPositiveTStress.value C ab td R k l c eta t z x := by
  have hx' : x∈Icc 0 t := ⟨hx.1,by linarith [hx.2,h.z_nonneg]⟩
  have he : t-z-x∈Icc 0 t := ⟨by linarith [hx.2],by linarith [hx.1,h.z_nonneg]⟩
  have hT : 0≤ExceptionalPositiveTStress.primary C td := by rw [hsource]; exact h.z_nonneg
  have hi := CriticalPositiveTEnvelope.original_increment td hab hR hQL hQU h hx' he
    ha hvar hG hD hT htotal
  have hid : ExceptionalPositiveTBlocks.increment C ab td (weights td k l c m eta x (t-z-x)) R=
      ExceptionalPositiveTStress.increment C ab td R k l c eta z x (t-z-x) := by
    cases td <;> simp [ExceptionalPositiveTBlocks.increment,weights,
      ExceptionalPositiveTStress.increment,ExceptionalPositiveTStress.bWeight,
      ExceptionalPositiveTStress.tWeight,hm]
  rw [hid] at hi
  have hv := ExceptionalPositiveTSupport.value_lower (k:=k) (l:=l) (c:=c) td hab hR
    (show 0≤eta by linarith [h.eta_lower]) h.angle ⟨h.z_nonneg,h.z_le⟩ hx hsource hs hc hn ha hcontact
  linarith

theorem fixed_endpoints {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t)
    {C : SignedCycle} {ab : Fin 4} (td : Bool) (hab : ab=0 ∨ ab=2)
    (hsource : ExceptionalPositiveTStress.primary C td=z)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t)
    (hcontact : Contact C) :
    CriticalPositiveTDerivative.scalar q t z≤ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
      (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z 0 ∧
    CriticalPositiveTDerivative.scalar q t z≤ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
      (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z (t-z) ∧
    (0<t-z → CriticalPositiveTDerivative.scalar q t z<
      ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
        (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
        (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z (t-z)) := by
  have hb := CriticalPositiveTDerivative.coefficients hq ht hz
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt (show 0≤q by norm_num [qLow] at hq; linarith [hq.1])
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hq.1
  have hRU : (Real.sqrt q)^2≤qCap := by rw [hR2]; exact hq.2.trans uniform_radius_order.2.2.1.le
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hc
  have hzero : (0:ℝ)∈Icc 0 (t-z) := ⟨le_rfl,by linarith [hz.2]⟩
  have hright : t-z∈Icc 0 (t-z) := ⟨by linarith [hz.2],le_rfl⟩
  have hv0 := value_lower td hab hR hRL hRU hb rfl hzero hsource hs hc' hn ha hvar hG hD htotal hcontact
  have hv1 := value_lower td hab hR hRL hRU hb rfl hright hsource hs hc' hn ha hvar hG hD htotal hcontact
  simp only [sub_zero,sub_self] at hv0 hv1
  have hrow := td_le_row td (x:=0) (e:=t-z) hR hb rfl
  have hsplit := E_le_G td hR hRL hb
  have hid := scalar_eq q t z
  refine ⟨by linarith,by linarith,?_⟩
  intro hpos
  have hstrict := E_lt_G td hR hRL hb hpos
  linarith

end SquaresInCircles.Eight.CriticalPositiveTEndpoints
