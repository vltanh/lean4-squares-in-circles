module

public import SquaresInCircles.Eight.TableFree.PositiveSmallScalar
public import SquaresInCircles.Eight.TableFree.ContactContinuation
public import SquaresInCircles.Eight.TableFree.PositiveCancelingOuter

/-!
# The full crossed HG2/GA0 composite at the original circle

Uncompiled source draft.  The circle inequality for the original H
bounds its rotated derivative directly, by a positive square comparison.
A feasible-contact continuation then lowers G to the common A/B frame.
The opposite intermediate does not occur in this argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedCancelingScalar
open PositiveSmallScalar EndpointRotationPenalty

def S (H : SignedPoint) (h : ℝ) : ℝ :=
  (H.a-1/2)*Real.sin h+(H.y-1/2)*Real.cos h

def U_H (H : SignedPoint) (h : ℝ) : ℝ :=
  (H.a-1/2)*Real.cos h-(H.y-1/2)*Real.sin h

def composite (H : SignedPoint) (P Y r z : ℝ) : ℝ := V P Y z+S H (z+r)
def compositeD (H : SignedPoint) (P Y r z : ℝ) : ℝ := -U P Y z+U_H H (z+r)

structure CapData (q P Y : ℝ) : Prop where
  P_mem : P∈Icc (1/2 : ℝ) (177/250)
  Y_lower : 1≤Y
  circle : (P+1)^2+Y^2≤q
  ceiling : q≤qCap

theorem trig_seven_tenths {h : ℝ} (hh : h∈Icc 0 frameCap) :
    Real.sin h≤6443/10000 ∧ 478/625≤Real.cos h := by
  have he : (7/10:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := CorrelatedSameBlock.sin_mono hh he hh.2
  have hc := CorrelatedSameBlock.cos_anti hh he hh.2
  have hs' := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc' := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  constructor <;> norm_num at hs' hc' ⊢ <;> linarith

theorem trig_sixty_six {h : ℝ} (hh : h∈Icc 0 (33/50:ℝ)) :
    Real.sin h≤1533/2500 ∧ 7899/10000≤Real.cos h := by
  have hi : h∈Icc 0 frameCap := ⟨hh.1,by dsimp [frameCap]; linarith [hh.2]⟩
  have he : (33/50:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := CorrelatedSameBlock.sin_mono hi he hh.2
  have hc := CorrelatedSameBlock.cos_anti hi he hh.2
  have hs' := sin_upper_five (show (0:ℝ)≤33/50 by norm_num)
  have hc' := cos_lower_six (show (0:ℝ)≤33/50 by norm_num)
  constructor <;> norm_num at hs' hc' ⊢ <;> linarith

/-- The original H circle bounds the second rotated support.  This
single square reserve applies to the complete angle interval. -/
theorem rotated_support_upper {H : SignedPoint} {h : ℝ}
    (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hh : h∈Icc 0 frameCap) (hS : 73/250≤S H h) : U_H H h<447/500 := by
  have ht := transport_trig hh
  have hb := trig_seven_tenths hh
  let m := Real.cos h+Real.sin h
  let n := Real.cos h-Real.sin h
  have hm : 0≤m := by dsimp [m]; linarith [ht.1,ht.2.2.1]
  have hn : 0≤n := by dsimp [n]; linarith [ht.2.2.2.2]
  have hmn : m^2+n^2=2 := by
    dsimp [m,n]
    nlinarith [Real.sin_sq_add_cos_sq h]
  have hid : (S H h+m)^2+(U_H H h+n)^2=H.circle := by
    dsimp [S,U_H,m,n,SignedPoint.circle]
    rw [abs_of_nonneg hHy]
    linear_combination (((H.a+1/2)^2+(H.y+1/2)^2)*Real.sin_sq_add_cos_sq h)
  have hlinear : (2595921/5000000:ℝ)≤(73/250)*m+(447/500)*n := by
    dsimp [m,n]
    linarith [hb.1,hb.2]
  by_contra! hbad
  have hs := pow_le_pow_left₀ (show 0≤73/250+m by linarith)
    (show 73/250+m≤S H h+m by linarith) 2
  have hu := pow_le_pow_left₀ (show 0≤447/500+n by linarith)
    (show 447/500+n≤U_H H h+n by linarith) 2
  have hq : H.circle≤9789/2500 := hHq
  nlinarith

theorem V_upper {q P Y z : ℝ} (C : CapData q P Y)
    (hz : z∈Icc 0 frameCap) : V P Y z≤P := by
  have ht := transport_trig hz
  have hc := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤P by linarith [C.P_mem.1])
  have hs := mul_nonneg (show 0≤Y by linarith [C.Y_lower]) ht.2.2.1
  dsimp [V]
  linarith

theorem V_antitone {q P Y : ℝ} (C : CapData q P Y) :
    AntitoneOn (V P Y) (Icc 0 frameCap) := by
  intro x hx z hz hxz
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hx hz hxz)
    (show 0≤P by linarith [C.P_mem.1])
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hx hz hxz)
    (show 0≤Y by linarith [C.Y_lower])
  dsimp [V]
  linarith

theorem U_lower {q P Y z : ℝ} (C : CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : 1≤U P Y z := by
  have ht := transport_trig hz
  have hp := mul_nonneg (show 0≤P by linarith [C.P_mem.1]) ht.2.2.1
  have hy := mul_nonneg (show 0≤Y by linarith [C.Y_lower])
    (show 0≤Real.cos z by linarith [ht.1])
  have hu : 0≤U P Y z := by dsimp [U]; linarith
  have hv := V_upper C hz
  have hv2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hv 2
  nlinarith [rotation_identity P Y z,C.Y_lower]

theorem S_hasDerivAt (H : SignedPoint) (h : ℝ) :
    HasDerivAt (S H) (U_H H h) h := by
  convert ((Real.hasDerivAt_sin h).const_mul (H.a-1/2)).add
    ((Real.hasDerivAt_cos h).const_mul (H.y-1/2)) using 1 <;> dsimp [S,U_H] <;> ring

theorem composite_hasDerivAt (H : SignedPoint) (P Y r z : ℝ) :
    HasDerivAt (composite H P Y r) (compositeD H P Y r z) z := by
  have hd := (S_hasDerivAt H (z+r)).comp z ((hasDerivAt_id z).add_const r)
  convert (V_hasDerivAt P Y z).add hd using 1 <;> dsimp [composite,compositeD] <;> ring

/-- The source HG2 and GA0 inequalities eliminate the original signed G
coordinate exactly.  G is not raised to any comparison circle. -/
theorem original_pair {H G A : SignedPoint} {r z : ℝ}
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤frameCap)
    (hHG : zeroFeasible H G (z+r) 2)
    (hGA : quarterFeasible G A (-z) 0) :
    1≤composite H (A.a-1/2) (A.y+1/2) r z := by
  have hh : z+r∈Icc 0 frameCap := ⟨by linarith,hspan⟩
  have hi : z∈Icc 0 frameCap := ⟨hz,by linarith⟩
  rw [zeroFeasible,edgeWidth_positive_formula hh] at hHG
  rw [quarterFeasible,edgeWidth_negative_formula hi] at hGA
  simp [zeroProjection,quarterProjection,Real.sin_neg,Real.cos_neg] at hHG hGA
  dsimp [composite,V,S]
  linarith

/-- The entire feasible composite improves toward zero.  Feasibility
on the motion is derived by continuation, rather than assumed. -/
theorem alignment_reserve {q P Y r z : ℝ} {H : SignedPoint}
    (C : CapData q P Y) (hHy : 0≤H.y) (hHq : H.Contained q)
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤frameCap)
    (hV : 1/2≤V P Y z) (hpair : 1≤composite H P Y r z) :
    ∀x∈Icc 0 z, 1≤composite H P Y r x ∧
      (53/500)*(z-x)≤composite H P Y r x-composite H P Y r z := by
  apply feasible_left_reserve hz (by norm_num : (0:ℝ)<53/500)
  · dsimp [composite,V,S]
    fun_prop
  · intro x hx
    exact composite_hasDerivAt H P Y r x
  · intro x hx hfeasible
    have hxi : x∈Icc 0 frameCap := ⟨hx.1,by linarith [hx.2]⟩
    have hzi : z∈Icc 0 frameCap := ⟨hz,by linarith⟩
    have hhi : x+r∈Icc 0 frameCap := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxV : 1/2≤V P Y x := hV.trans (V_antitone C hxi hzi hx.2)
    have hxU := U_lower C hxi hxV
    have hxupper := (V_upper C hxi).trans C.P_mem.2
    have hxS : 73/250≤S H (x+r) := by dsimp [composite] at hfeasible; linarith
    have hhU := rotated_support_upper hHy (hHq.trans C.ceiling) hhi hxS
    dsimp [compositeD]
    linarith
  · exact hpair

end SquaresInCircles.Eight.TableFree.CrossedCancelingScalar
