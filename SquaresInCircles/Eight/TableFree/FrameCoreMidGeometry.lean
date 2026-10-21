module

public import SquaresInCircles.Eight.TableFree.FrameCoreMidPrimaryContinuation
public import SquaresInCircles.Eight.TableFree.FrameCoreMidContact

/-!
# Original core/middle coordinates and coarse feasible-angle cuts

These are supports on the original complete core and middle arcs.  The
only separation hypotheses are the actual weak forward margins.  The
cuts are consequences of those margins; none is a frame-window premise.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars

def coreMidCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*M B
def midCoreCost (i k : Bool) (b A B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*M b-sign k*coreLabel A B
def coreMidSecondary (i k : Bool) (a b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def coreMidPrimary (k : Bool) (a B x : ℝ) : ℝ :=
  a-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x
def midCoreSecondary (i k : Bool) (b a B x : ℝ) : ℝ :=
  sign i*b+a*Real.sin x-sign k*B*Real.cos x-pairWidth x
def midCorePrimary (k : Bool) (b a B x : ℝ) : ℝ :=
  A b-a*Real.cos x-sign k*B*Real.sin x-pairWidth x

theorem middle_bounds {b : ℝ} (hb : b∈Icc b1 b2) :
    (3246/10000:ℝ)<b ∧ b<(257/500:ℝ) ∧
      (1199/1000:ℝ)<A b ∧ A b<(1299/1000:ℝ) := by
  have ha := A_mid_bounds hb
  exact ⟨by linarith [hb.1,b1_bounds.1],by linarith [hb.2,b2_bounds.2],
    by linarith [ha.1,a2_bounds.1],by linarith [ha.2,a1_precise.2]⟩

theorem signed_middle_bounds (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    -M2≤sign i*M b ∧ sign i*M b≤M2 := by
  have hh := M_bounds hb
  have hp : 0<M b := lt_of_lt_of_le M_endpoints.1 hh.1
  cases i <;> norm_num [sign] <;> constructor <;> linarith

theorem middle_minus_label (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    -M b≤sign i*M b := by
  have hp : 0≤M b := (lt_of_lt_of_le M_endpoints.1 (M_bounds hb).1).le
  cases i <;> norm_num [sign] <;> linarith

theorem signed_le (i : Bool) {b : ℝ} (hb : 0≤b) : sign i*b≤b := by
  cases i <;> norm_num [sign] <;> linarith

theorem negative_signed_sin_le (i : Bool) {b x : ℝ} (hb : 0≤b) :
    -sign i*b*Real.sin x≤b*|Real.sin x| := by
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin x)) hb
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin x)) hb
  cases i <;> norm_num [sign] <;> nlinarith

theorem nonpositive_signs {x : ℝ} (hx : x∈Icc (-(54/125:ℝ)) 0) :
    Real.sin x≤0 ∧ 0≤Real.cos x := by
  have hh := FrameLowPair.quadrant
    (show -x∈Icc 0 (Real.pi/2) from
      ⟨by linarith [hx.2],by linarith [hx.1,FrameLowPair.pi_lower]⟩)
  simpa only [Real.sin_neg,Real.cos_neg,neg_nonneg] using And.intro hh.1 hh.2.2.1

theorem core_mid_tail (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2) (hx : (109/50:ℝ)≤x) :
    (1801/2000:ℝ)<coreMidCost i k a b B x := by
  have hs := (FrameCoreArc.signed_label_bounds i hc).1
  have ht := (signed_middle_bounds k hB).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [coreMidCost]
  linarith [M_endpoints.2.2.2]

theorem mid_core_tail (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B) (hx : (109/50:ℝ)≤x) :
    (1801/2000:ℝ)<midCoreCost i k b a B x := by
  have hs := (signed_middle_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [midCoreCost]
  linarith [M_endpoints.2.2.2]

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hm : 0≤coreMidSecondary i k a b B x) :
    0≤sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := middle_projection_lt k hB x
      have hw := width_one_le x
      have hb : b<1/2 := by
        dsimp [coreMidSecondary,sign] at hm
        nlinarith
      rw [(label_side hc hb).2]
      simp

theorem mid_secondary_source_positive (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hm : 0≤midCoreSecondary i k b a B x) : i=true := by
  cases i with
  | true => rfl
  | false =>
      have hproj := core_projection_lt k hc x
      have hw := width_one_le x
      have hb0 := (middle_bounds hb).1
      dsimp [midCoreSecondary,sign] at hm
      linarith

theorem core_secondary_positive_cut (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤coreMidSecondary i true a b B x) :
    (7/10:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hB
  have hsb := signed_le i hcore.2.2.1
  by_contra! hsmall
  by_cases hneg : x≤0
  · have ht := nonpositive_signs ⟨hx,hneg⟩
    have h1 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hmid.2.2.1] : 0≤A B) ht.1
    have h2 := mul_nonneg (by linarith [hmid.1] : 0≤B) ht.2
    have hw := width_one_le x
    dsimp [coreMidSecondary,sign] at hm
    linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hneg).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_self hxq.1
    have hco := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show A B-1/2≤799/1000 by linarith [hmid.2.2.2]) ht.1
    have hB' := mul_le_mul_of_nonneg_right
      (show (4123/5000:ℝ)≤B+1/2 by linarith [hmid.1]) ht.2.2.1
    have hw := (first_width hxq).1
    dsimp [coreMidSecondary,sign] at hm
    rw [hw] at hm
    nlinarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem mid_secondary_positive_cut {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤midCoreSecondary true true b a B x) :
    (6/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  by_contra! hsmall
  by_cases hneg : x≤0
  · have ht := nonpositive_signs ⟨hx,hneg⟩
    have h1 := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1] : 0≤a) ht.1
    have h2 := mul_nonneg hcore.2.2.1 ht.2
    have hw := width_one_le x
    dsimp [midCoreSecondary,sign] at hm
    linarith
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hneg).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_self hxq.1
    have hco := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show a-1/2≤1/12 by linarith [hcore.2.1]) ht.1
    have hB' := mul_nonneg hcore.2.2.1 ht.2.2.1
    rw [midCoreSecondary,show sign true=(1:ℝ) by rfl,(first_width hxq).1] at hm
    nlinarith

theorem core_primary_cut (k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤coreMidPrimary k a B x) :
    (3/2:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hB
  by_contra! hsmall
  have habs : |x|≤3/2 := abs_le.mpr ⟨by linarith,hsmall⟩
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (by linarith [FrameLowPair.pi_lower] : (3/2:ℝ)≤Real.pi) habs
  rw [Real.cos_abs] at hcL
  have hcpos : 0≤Real.cos x := by linarith [trig_three_halves.1]
  have hsg := negative_signed_sin_le k (by linarith [hmid.1] : 0≤B)
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hmid.2.2.1]) hcpos
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [hmid.2.1]) (abs_nonneg (Real.sin x))
  have hsU := Real.abs_sin_le_one x
  dsimp [coreMidPrimary,pairWidth] at hm
  rw [abs_of_nonneg hcpos] at hm
  nlinarith [trig_three_halves.1]

theorem middle_primary_cut (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤midCorePrimary k b a B x) :
    (3/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  by_contra! hsmall
  have habs : |x|≤3/5 := abs_le.mpr ⟨by linarith,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/5:ℝ)^2 := by nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) habs 2]
  have hcL : (41/50:ℝ)≤Real.cos x := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1])
    (by linarith : 0≤Real.cos x)
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤59/1000 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp [midCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  nlinarith

theorem core_primary_positive_false {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (3/2:ℝ) (109/50)) (hm : 0≤coreMidPrimary true a B x) : False := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hB
  have hsL := sin_endpoint_lower (by norm_num : (0:ℝ)≤3/2)
    (by linarith [FrameLowPair.pi_lower] : (109/50:ℝ)≤Real.pi) hx
    (by linarith [trig_three_halves.2] : (41/50:ℝ)<Real.sin (3/2:ℝ)) trig_last.1
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hcU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤3/2) (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hco := cos_upper_four (show (0:ℝ)≤3/2 by norm_num)
  norm_num at hco
  have habs : |Real.cos x|<573/1000 :=
    abs_lt.mpr ⟨by linarith [trig_last.2],by linarith⟩
  have hca := mul_le_mul_of_nonneg_left (neg_le_abs (Real.cos x))
    (by linarith [hmid.2.2.1] : 0≤A B)
  have hamp := mul_le_mul_of_nonneg_right
    (show A B-1/2≤799/1000 by linarith [hmid.2.2.2]) (abs_nonneg (Real.cos x))
  have hbp := mul_le_mul_of_nonneg_right
    (show (4123/5000:ℝ)≤B+1/2 by linarith [hmid.1]) (by linarith : 0≤Real.sin x)
  dsimp [coreMidPrimary,pairWidth,sign] at hm
  rw [abs_of_pos (by linarith : 0<Real.sin x)] at hm
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameCoreMidGeometry
