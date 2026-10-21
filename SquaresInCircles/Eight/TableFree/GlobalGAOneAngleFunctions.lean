module

public import SquaresInCircles.Eight.TableFree.GlobalGAChargedPairs
public import SquaresInCircles.Eight.TableFree.GlobalGASortedSupport

/-!
# The actual one-angle H/G force and its axial comparison

Uncompiled source.  The full-circle and axial bounds below apply to the
unchanged source point.  The transition test, short-arc concavity, and
long-arc monotonicity are proved for their actual continuous formulas.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope OrdinaryAngleConcavity

def oneIncrement (p q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-(q*Real.cos x*P.a+(p+q*Real.sin x)*P.y)+
    fullSupport q p+charge*x

def negativeFull (p q w : ℝ) : ℝ := V R p q w-charge*w

def axialTest (p q w : ℝ) : ℝ :=
  q*Real.cos w/2-(axial+1/2)*(p-q*Real.sin w)

def axialOne (p q w : ℝ) : ℝ :=
  q*((1+Real.cos w+Real.sin w)/2-1)-q*axial*Real.cos w+
    fullSupport q p-charge*w

def axialOneD (q w : ℝ) : ℝ :=
  q*((axial-1/2)*Real.sin w+Real.cos w/2)-charge

theorem one_force_norm (p q x : ℝ) :
    Real.sqrt ((q*Real.cos x)^2+(p+q*Real.sin x)^2)=pairNorm p q x := by
  simpa [rotatedPair,pairNorm_symm,add_comm] using rotatedPair_norm q p 0 x

theorem one_full_identity {p q x : ℝ} (hx : |x|≤frameCap) :
    q*(edgeWidth x-1)-fullSupport (q*Real.cos x) (p+q*Real.sin x)+
      fullSupport q p+charge*x=chargedPair p q 0 x := by
  rw [fullSupport_pair p q]
  unfold fullSupport
  rw [one_force_norm]
  have hwidth := width_add_half_phi hx
  dsimp [chargedPair,phi] at *
  simp only [psi_zero,mul_zero,zero_add]
  nlinarith [congrArg (fun z : ℝ => q*z) hwidth]

theorem one_full_lower {r p q x : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap) (hx : |x|≤frameCap) :
    chargedPair p q 0 x≤oneIncrement p q x P := by
  have h := actual_full_support (f:=q*Real.cos x) (g:=p+q*Real.sin x) hy hc hr
  rw [← one_full_identity hx]
  dsimp [oneIncrement]
  linarith

theorem negative_full_identity {p q w : ℝ} (hw : w∈Icc 0 frameCap) :
    chargedPair p q 0 (-w)=negativeFull p q w := by
  simp only [chargedPair,psi_zero,mul_zero,zero_add,psi_negative hw,negativeFull,V]
  ring

theorem negativeFull_concave {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (negativeFull p q) := by
  simpa [negativeFull,V,chargedMixed,mixedBlock] using
    chargedMixed_concave_N (P:=0) hp hpq hqp (by norm_num [frameCap])

theorem negative_full_short_nonneg {p q w c : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hc : c≤frameCap) (hw : w∈Icc 0 c) (hend : 0≤negativeFull p q c) :
    0≤negativeFull p q w := by
  have hc0 : 0≤c := hw.1.trans hw.2
  have hconc := (negativeFull_concave hp hpq hqp).subset
    (Icc_subset_Icc le_rfl hc) (convex_Icc 0 c)
  have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hc0⟩ ⟨hc0,le_rfl⟩ hw
  have hz : negativeFull p q 0=0 := by simp [negativeFull]
  rw [hz,min_eq_left hend] at hmin
  exact hmin

theorem positive_one_nonneg {r p q x : ℝ} {P : SignedPoint}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hx : x∈Icc 0 frameCap) (hend : 0≤chargedMixed p q frameCap 0) :
    0≤oneIncrement p q x P := by
  have hconc := chargedMixed_concave_P (N:=0) hp hpq hqp (by norm_num [frameCap])
  have hmin := hconc.min_le_of_mem_Icc (by norm_num [frameCap]) (by norm_num [frameCap]) hx
  rw [chargedMixed_zero,min_eq_left hend] at hmin
  have hm := charged_pair_minorant (a:=0) (b:=x) hp.le hpq
    (by simpa [positivePart,max_eq_left hx.1] using hx.2)
    (by simp [negativePart,max_eq_right (by linarith : -x≤0)]; norm_num [frameCap])
  simp only [positivePart_zero,negativePart_zero,zero_add] at hm
  rw [show positivePart x=x by exact max_eq_left hx.1,
    show negativePart x=0 by exact max_eq_right (by linarith : -x≤0)] at hm
  exact (hmin.trans hm).trans (one_full_lower hy hc hr
    (by rw [abs_of_nonneg hx.1]; exact hx.2))

theorem axialTest_hasDerivAt (p q w : ℝ) :
    HasDerivAt (axialTest p q)
      (q*((axial+1/2)*Real.cos w-Real.sin w/2)) w := by
  convert (((Real.hasDerivAt_cos w).const_mul q).div_const 2).sub
    (((hasDerivAt_const w p).sub ((Real.hasDerivAt_sin w).const_mul q)).const_mul
      (axial+1/2)) using 1 <;> dsimp [axialTest] <;> ring

theorem axialTest_monotone {p q : ℝ} (hq : 0≤q) :
    MonotoneOn (axialTest p q) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro w hw
    exact (axialTest_hasDerivAt p q w).continuousAt.continuousWithinAt
  · intro w hw
    exact axialTest_hasDerivAt p q w
  · intro w hw
    obtain ⟨hc,_,_,hs,_⟩ := transport_trig (Ioo_subset_Icc_self hw)
    have hm := mul_le_mul (show (19/10:ℝ)≤axial+1/2 by linarith [axial_bounds.1])
      hc.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [axial_bounds.1])
    exact mul_nonneg hq (by nlinarith)

theorem axial_test_endpoint_lower {p q w S C : ℝ}
    (hq : 0≤q) (hS : S≤Real.sin w) (hC : C≤Real.cos w)
    (hcoef : 0≤p-q*S) :
    q*C/2-(14145757/10000000+1/2)*(p-q*S)≤axialTest p q w := by
  have ha0 : 0≤axial+1/2 := by linarith [axial_bounds.1]
  have hsin := mul_le_mul_of_nonneg_left hS hq
  have hinner := mul_le_mul_of_nonneg_left
    (show p-q*Real.sin w≤p-q*S by linarith) ha0
  have houter := mul_le_mul_of_nonneg_right
    (show axial+1/2≤14145757/10000000+1/2 by linarith [axial_bounds.2]) hcoef
  have hcos := mul_le_mul_of_nonneg_left hC hq
  dsimp [axialTest]
  linarith

theorem axialOne_hasDerivAt (p q w : ℝ) :
    HasDerivAt (axialOne p q) (axialOneD q w) w := by
  convert ((((((((Real.hasDerivAt_cos w).const_add 1).add (Real.hasDerivAt_sin w)).
      div_const 2).sub_const 1).const_mul q).sub
      ((Real.hasDerivAt_cos w).const_mul (q*axial))).add_const (fullSupport q p)).sub
      ((hasDerivAt_id w).const_mul charge) using 1 <;>
    dsimp [axialOne,axialOneD] <;> ring

theorem axialOneD_hasDerivAt (q w : ℝ) :
    HasDerivAt (axialOneD q)
      (q*((axial-1/2)*Real.cos w-Real.sin w/2)) w := by
  convert ((((Real.hasDerivAt_sin w).const_mul (axial-1/2)).add
    ((Real.hasDerivAt_cos w).div_const 2)).const_mul q).sub_const charge using 1 <;>
    dsimp [axialOneD] <;> ring

theorem axialOneD_monotone {q : ℝ} (hq : 0≤q) :
    MonotoneOn (axialOneD q) (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro w hw
    exact (axialOneD_hasDerivAt q w).continuousAt.continuousWithinAt
  · intro w hw
    exact axialOneD_hasDerivAt q w
  · intro w hw
    obtain ⟨hc,_,_,hs,_⟩ := transport_trig (Ioo_subset_Icc_self hw)
    have hm := mul_le_mul (show (9/10:ℝ)≤axial-1/2 by linarith [axial_bounds.1])
      hc.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [axial_bounds.1])
    exact mul_nonneg hq (by nlinarith)

theorem one_axial_lower {r p q w : ℝ} {P : SignedPoint}
    (hq : 0≤q) (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hw : w∈Icc 0 frameCap) (htest : 0≤axialTest p q w) :
    axialOne p q w≤oneIncrement p q (-w) P := by
  have hcos : 0≤Real.cos w := by linarith [(transport_trig hw).1]
  have haxis : (axial+1/2)*(p-q*Real.sin w)≤(q*Real.cos w)/2 := by
    dsimp [axialTest] at htest
    linarith
  have hsupport := actual_axial_support hy hc hr (mul_nonneg hq hcos) haxis
  rw [oneIncrement,edgeWidth_negative_formula hw]
  simp only [Real.cos_neg,Real.sin_neg]
  dsimp [axialOne]
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
