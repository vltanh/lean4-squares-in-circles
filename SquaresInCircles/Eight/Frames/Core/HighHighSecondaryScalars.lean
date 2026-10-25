module

public import SquaresInCircles.Eight.Frames.Core.LowCancellation
public import SquaresInCircles.Eight.Frames.High.Arc

/-!
# Eight squares: the two high-source transverse scalar supports

The negative core tangent is controlled by the same parallel value on
both sides of zero.  On the negative interval the derivative numerator
is positive by one completed square.  The positive core tangent has a
strictly increasing affine trigonometric support in both quadrants.
-/

section
/-!
## Original core/middle coordinates and coarse feasible-angle cuts

These are supports on the original complete core and middle arcs.  The
only separation hypotheses are the actual weak forward margins.  The
cuts are consequences of those margins; none is a frame-window premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars

def coreMidCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*M B
def midCoreCost (i k : Bool) (b A B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*M b-sign k*coreLabel A B
def coreMidSecondary (i k : Bool) (_a b B x : ℝ) : ℝ :=
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
    -M2≤ sign i*M b ∧ sign i*M b≤M2 := by
  have hh := M_bounds hb
  have hp : 0<M b := by linarith [M_endpoints.1,hh.1]
  cases i
  · rw [show sign false=-1 from rfl]
    constructor <;> linarith
  · rw [show sign true=1 from rfl]
    constructor <;> linarith

theorem middle_minus_label (i : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    -M b≤ sign i*M b := by
  have hp : 0≤M b := by linarith [M_endpoints.1,(M_bounds hb).1]
  cases i
  · rw [show sign false=-1 from rfl]
    linarith
  · rw [show sign true=1 from rfl]
    linarith

theorem signed_le (i : Bool) {b : ℝ} (hb : 0≤b) : sign i*b≤b := by
  cases i <;> norm_num [sign]
  linarith

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
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  have hs := (signed_middle_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [midCoreCost]
  linarith [M_endpoints.2.2.2]

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hm : 0≤coreMidSecondary i k a b B x) :
    0≤ sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := middle_projection_lt k hB x
      have hw := width_one_le x
      have hb : b<1/2 := by
        dsimp only [coreMidSecondary] at hm
        rw [show sign false=-1 from rfl] at hm
        linarith
      rw [(label_side hc hb).2]
      simp

theorem mid_secondary_source_positive (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hm : 0≤ midCoreSecondary i k b a B x) : i=true := by
  cases i with
  | true => rfl
  | false =>
      exfalso
      have hproj := core_projection_lt k hc x
      have hw := width_one_le x
      have hb0 := (middle_bounds hb).1
      dsimp only [midCoreSecondary] at hm
      rw [show sign false=-1 from rfl] at hm
      linarith

theorem core_secondary_positive_cut (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤coreMidSecondary i true a b B x) :
    (7/10:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hB
  have hsb := signed_le i hcore.2.2.1
  dsimp only [coreMidSecondary] at hm
  rw [show sign true=1 from rfl] at hm
  by_contra! hsmall
  by_cases hneg : x≤0
  · have ht := nonpositive_signs ⟨hx,hneg⟩
    have h1 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hmid.2.2.1] : 0≤A B) ht.1
    have h2 := mul_nonneg (by linarith [hmid.1] : 0≤B) ht.2
    have hw := width_one_le x
    linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hneg).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le hxq.1
    have hco := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show A B-1/2≤799/1000 by linarith [hmid.2.2.2]) ht.1
    have hB' := mul_le_mul_of_nonneg_right
      (show (4123/5000:ℝ)≤B+1/2 by linarith [hmid.1]) ht.2.2.1
    have hw := (first_width hxq).1
    rw [hw] at hm
    linarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem mid_secondary_positive_cut {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤ midCoreSecondary true true b a B x) :
    (6/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  dsimp only [midCoreSecondary] at hm
  rw [show sign true=1 from rfl] at hm
  by_contra! hsmall
  by_cases hneg : x≤0
  · have ht := nonpositive_signs ⟨hx,hneg⟩
    have h1 := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1] : 0≤a) ht.1
    have h2 := mul_nonneg hcore.2.2.1 ht.2
    have hw := width_one_le x
    linarith
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hneg).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le hxq.1
    have hco := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show a-1/2≤1/12 by linarith [hcore.2.1]) ht.1
    have hB' := mul_nonneg hcore.2.2.1 ht.2.2.1
    rw [(first_width hxq).1] at hm
    linarith

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
  have hsg := negative_signed_sin_le k (x := x) (by linarith [hmid.1] : 0≤B)
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hmid.2.2.1]) hcpos
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [hmid.2.1]) (abs_nonneg (Real.sin x))
  have hsU := Real.abs_sin_le_one x
  dsimp [coreMidPrimary,pairWidth] at hm
  rw [abs_of_nonneg hcpos] at hm
  linarith [trig_three_halves.1]

theorem middle_primary_cut (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : -(54/125:ℝ)≤x) (hm : 0≤ midCorePrimary k b a B x) :
    (3/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hmid := middle_bounds hb
  by_contra! hsmall
  have habs : |x|≤3/5 := abs_le.mpr ⟨by linarith,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/5:ℝ)^2 := by nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) habs 2]
  have hcL : (41/50:ℝ)≤Real.cos x := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k (x := x) hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1])
    (by linarith : 0≤Real.cos x)
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤59/1000 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp [midCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  linarith

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

end SquaresInCircles.Eight.FrameCoreMidGeometry
end
end
end

section
/-!
## Original core/high geometry and feasible-angle cuts

The four signed source margins are kept in their original coordinates.
All coarse cuts below follow directly from those weak margins and the
exact state arcs; no concentrated frame interval is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighGeometry
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (a2 b2 g K)
open FrameCoreMidGeometry (signed_le negative_signed_sin_le)

def coreHighCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*H B
def highCoreCost (i k : Bool) (b a B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*H b-sign k*coreLabel a B
def coreHighSecondary (i k : Bool) (_a b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def coreHighPrimary (k : Bool) (a B x : ℝ) : ℝ :=
  a-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x
def highCoreSecondary (i k : Bool) (b a B x : ℝ) : ℝ :=
  sign i*b+a*Real.sin x-sign k*B*Real.cos x-pairWidth x
def highCorePrimary (k : Bool) (b a B x : ℝ) : ℝ :=
  A b-a*Real.cos x-sign k*B*Real.sin x-pairWidth x

theorem negative_trig {x : ℝ} (hx : x∈Icc (-(203/250:ℝ)) 0) :
    Real.sin x≤0 ∧ (86/125:ℝ)<Real.cos x := by
  have hz : -x∈Icc 0 (203/250:ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,FrameLowPair.pi_lower])
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (by linarith [FrameLowPair.pi_lower] : (203/250:ℝ)≤Real.pi) hz.2
  have hc0 := cos_lower_six (show (0:ℝ)≤203/250 by norm_num)
  norm_num at hc0
  simp only [Real.sin_neg,Real.cos_neg] at hs hc
  exact ⟨by linarith,by linarith⟩

theorem negative_width {x : ℝ} (hx : x∈Icc (-(203/250:ℝ)) 0) :
    pairWidth x=(1-Real.sin x+Real.cos x)/2 ∧
      periodicFrameCost x=(-Real.sin x+Real.cos x-1)/2 := by
  have ht := negative_trig hx
  have hs : |Real.sin x|= -Real.sin x := abs_of_nonpos ht.1
  have hc : |Real.cos x|=Real.cos x := abs_of_nonneg (by linarith [ht.2])
  constructor <;> simp only [pairWidth,periodicFrameCost,hs,hc] <;> ring

theorem high_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc b2 c0) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(4/3:ℝ) := by
  have hh := (high_norm_sq hb).2
  cases i
  · have h := projection_lt (b := b) (by norm_num : (0:ℝ)<4/3) hh x
    simp only [sign,Bool.false_eq_true,↓reduceIte]
    linarith
  · have he : (A b)^2+(-b)^2<(4/3:ℝ)^2 := by nlinarith
    have h := projection_lt (b := -b) (by norm_num : (0:ℝ)<4/3) he x
    simp only [sign,↓reduceIte]
    linarith

theorem core_high_tail (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (5/2:ℝ)≤x) :
    (8833/10000:ℝ)<coreHighCost i k a b B x := by
  have hs := (FrameCoreArc.signed_label_bounds i hc).1
  have ht := (FrameHighArc.signed_label_bounds k hB).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [coreHighCost]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem high_core_tail (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : (5/2:ℝ)≤x) :
    (8833/10000:ℝ)<highCoreCost i k b a B x := by
  have hs := (FrameHighArc.signed_label_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [highCoreCost]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hm : 0≤coreHighSecondary i k a b B x) :
    0≤ sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := high_projection_lt k hB x
      have hw := width_one_le x
      have hsf : sign false= -1 := by simp [sign]
      have hb : b<1/2 := by
        dsimp only [coreHighSecondary] at hm
        rw [hsf] at hm
        linarith
      rw [(label_side hc hb).2]
      simp

theorem high_secondary_source_positive (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hm : 0≤highCoreSecondary i k b a B x) : i=true := by
  cases i with
  | true => rfl
  | false =>
      exfalso
      have hp := core_projection_lt k hc x
      have hw := width_one_le x
      have hb0 := (high_bounds hb).1
      have hsf : sign false= -1 := by simp [sign]
      dsimp only [highCoreSecondary] at hm
      rw [hsf] at hm
      linarith

theorem core_primary_angle (k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : -(203/250:ℝ)≤x)
    (hm : 0≤coreHighPrimary k a B x) : (6/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  by_contra! hsmall
  have habs : |x|≤6/5 := abs_le.mpr ⟨by linarith,hsmall⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (by linarith [FrameLowPair.pi_lower] : (6/5:ℝ)≤Real.pi) habs
  rw [Real.cos_abs] at hcos
  have hc0 := FrameCoreMidScalars.trig_six_fifths.2.2.1
  have hcpos : 0≤Real.cos x := by linarith
  have hsg := negative_signed_sin_le k (x := x) (by linarith [hhigh.1] : 0≤B)
  have hA := mul_le_mul_of_nonneg_right
    (show (1399/1000:ℝ)≤A B+1/2 by linarith [hhigh.2.2.1]) hcpos
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤2/5 by linarith [hhigh.2.1]) (abs_nonneg (Real.sin x))
  dsimp only [coreHighPrimary,pairWidth] at hm
  rw [abs_of_nonneg hcpos] at hm
  linarith [Real.abs_sin_le_one x,hcore.2.1]

theorem high_secondary_positive_angle {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : -(203/250:ℝ)≤x)
    (hm : 0≤highCoreSecondary true true b a B x) : (9/20:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have hst : sign true=1 := by simp [sign]
  dsimp only [highCoreSecondary] at hm
  rw [hst] at hm
  by_contra! hsmall
  by_cases hn : x≤0
  · have ht := negative_trig ⟨hx,hn⟩
    have hA := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1] : 0≤a) ht.1
    have hB := mul_nonneg hcore.2.2.1 (by linarith [ht.2] : 0≤Real.cos x)
    have hw := width_one_le x
    linarith [hhigh.2.1]
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hn).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le hxq.1
    have hcL := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show a-1/2≤1/12 by linarith [hcore.2.1]) ht.1
    have hB := mul_nonneg hcore.2.2.1 ht.2.2.1
    rw [(first_width hxq).1] at hm
    linarith [hhigh.2.1]

theorem high_primary_angle (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : -(203/250:ℝ)≤x)
    (hpositive : k=true → -(13/500:ℝ)≤x)
    (hm : 0≤highCorePrimary k b a B x) : (3/4:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have ha : (5589/10000:ℝ)≤a := by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hxlower : -(3/4:ℝ)≤x := by
    cases k with
    | true => linarith [hpositive rfl]
    | false =>
        by_contra! hnegative
        have ht := negative_trig ⟨hx,by linarith⟩
        have hA := mul_le_mul_of_nonneg_right ha
          (by linarith [ht.2] : 0≤Real.cos x)
        have hB := mul_nonpos_of_nonneg_of_nonpos hcore.2.2.1 ht.1
        have hw := width_one_le x
        have hsf : sign false= -1 := by simp [sign]
        dsimp only [highCorePrimary] at hm
        rw [hsf] at hm
        linarith [hhigh.2.2.2,ht.2]
  by_contra! hsmall
  have habs : |x|≤3/4 := abs_le.mpr ⟨hxlower,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/4:ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) habs 2
    rwa [sq_abs] at h
  have hcL : (23/32:ℝ)≤Real.cos x := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k (x := x) hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith)
    (by linarith : 0≤Real.cos x)
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤3/50 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp only [highCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  linarith [hhigh.2.2.2]

end SquaresInCircles.Eight.FrameCoreHighGeometry
end
end
end

section
/-!
## The core/low pairs and the cuts of their angles

A low state `(A b, b)`, `0 ≤ b ≤ b1`, has `b < 13/40` and `12987/10000 < A b < 283/200`, a label
between `(v - u) b` and `v b`, and projections below `283/200` in every direction (`low_bounds`,
`low_label_linear`, `low_projection_lt`). Beyond the angle `41/20` the cost of a core/low pair
exceeds `91/100` in either order (`core_low_tail`, `low_core_tail`). For frame angles
`x ≥ -3/10`, a weak margin on the secondary axis of a low source against a core target is
impossible (`low_secondary_false`); on the secondary axis of a core source it leaves a
nonnegative core residual and forces `x > 0` (`core_secondary_source_floor`,
`core_secondary_angle`); on the primary axis of a core source it forces `x > π/2`
(`core_primary_angle`), and on that of a low source `x > 3/10` (`low_primary_angle`). The whole
low arc and the rounded core are covered, with both signs of the tangents.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreLowGeometry
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreMidGeometry (signed_le negative_signed_sin_le nonpositive_signs)

def coreLowCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*L B
def lowCoreCost (i k : Bool) (b a B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*L b-sign k*coreLabel a B
def coreLowSecondary (i k : Bool) (_a b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def coreLowPrimary (k : Bool) (a B x : ℝ) : ℝ :=
  a-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x
def lowCoreSecondary (i k : Bool) (b a B x : ℝ) : ℝ :=
  sign i*b+a*Real.sin x-sign k*B*Real.cos x-pairWidth x
def lowCorePrimary (k : Bool) (b a B x : ℝ) : ℝ :=
  A b-a*Real.cos x-sign k*B*Real.sin x-pairWidth x

theorem low_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤b ∧ b<(13/40:ℝ) ∧ (12987/10000:ℝ)<A b ∧ A b<283/200 := by
  have ha := A_low_bounds hb
  exact ⟨hb.1,by linarith [hb.2,b1_bounds.2],
    by linarith [ha.1,a1_bounds.1],by linarith [ha.2,a0_bounds.2]⟩

theorem low_coordinate_sum {b : ℝ} (hb : b∈Icc 0 b1) : a0≤A b+b := by
  have hh := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) (by norm_num : (0:ℝ)≤0) b1_mem.2 hb
  have he : a0≤a1+b1 := by linarith [a0_bounds.2,a1_bounds.1,b1_bounds.1]
  simpa [linear,A_zero,A_b1,min_eq_left he] using hh

theorem low_label_linear {b : ℝ} (hb : b∈Icc 0 b1) :
    (v-u)*b≤L b ∧ L b≤v*b := by
  have hlo := mul_le_mul_of_nonneg_left (low_coordinate_sum hb)
    (show (0:ℝ)≤u by norm_num [u])
  have hhi := mul_le_mul_of_nonneg_left (A_low_bounds hb).2
    (show (0:ℝ)≤u by norm_num [u])
  dsimp [L]
  constructor <;> nlinarith

theorem low_norm_sq {b : ℝ} (hb : b∈Icc 0 b1) :
    (A b)^2+b^2<(283/200:ℝ)^2 := by
  have hc := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hc0 := A_circle (show (0:ℝ)∈Icc 0 c0 from ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩)
  rw [A_zero] at hc0
  have hsum := low_coordinate_sum hb
  have ha := a0_bounds
  have ha2 : a0^2<(283/200:ℝ)^2 := by nlinarith
  nlinarith

theorem low_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(283/200:ℝ) := by
  have hh := low_norm_sq hb
  cases i
  · have h := projection_lt (a := A b) (b := b) (by norm_num : (0:ℝ)<283/200) hh x
    have hs : sign false=-1 := rfl
    rw [hs]
    linarith
  · have he : (A b)^2+(-b)^2<(283/200:ℝ)^2 := by rw [neg_sq]; exact hh
    have h := projection_lt (b := -b) (by norm_num : (0:ℝ)<283/200) he x
    have hs : sign true=1 := rfl
    rw [hs]
    linarith

theorem core_low_tail (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : (41/20:ℝ)≤x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hs := (FrameCoreArc.signed_label_bounds i hc).1
  have ht := (FrameLowPair.signed_label_bounds k hB).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [coreLowCost]
  linarith [L1_bounds.2]

theorem low_core_tail (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hx : (41/20:ℝ)≤x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hs := (FrameLowPair.signed_label_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [lowCoreCost]
  linarith [L1_bounds.2]

theorem low_secondary_false (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B)
    (hm : 0≤lowCoreSecondary i k b a B x) : False := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  have hsb := signed_le i hb.1
  have ha0 : 0≤a := by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hsin := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin x)) ha0
  have hA := mul_le_mul_of_nonneg_right hcore.2.1 (abs_nonneg (Real.sin x))
  have hB := mul_le_mul_of_nonneg_right
    (show B≤7/12 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.cos x))
  have hcos : -sign k*B*Real.cos x≤B*|Real.cos x| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos x)) hcore.2.2.1
    have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.cos x)) hcore.2.2.1
    cases k <;> norm_num [sign] <;> nlinarith
  have hsum := CorePairGeometry.charge_upper x
  dsimp [periodicFrameCost] at hsum
  dsimp [lowCoreSecondary,pairWidth] at hm
  nlinarith

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hm : 0≤coreLowSecondary i k a b B x) :
    0≤ sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := low_projection_lt k hB x
      have hw := width_one_le x
      have hb : b<1/2 := by
        have hs : sign false=-1 := rfl
        dsimp only [coreLowSecondary] at hm
        rw [hs] at hm
        linarith
      rw [(label_side hc hb).2]
      simp

theorem core_secondary_angle (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤coreLowSecondary i k a b B x) : 0<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hsb := signed_le i hcore.2.2.1
  by_contra! hneg
  have ht := nonpositive_signs ⟨by linarith,hneg⟩
  have hA := mul_nonpos_of_nonneg_of_nonpos (by linarith [hlow.2.2.1] : 0≤A B) ht.1
  have hBcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hB.1
  have hcos : -sign k*B*Real.cos x≤B := by
    have hnonneg := mul_nonneg hB.1 ht.2
    cases k <;> norm_num [sign] <;> nlinarith
  have hw := width_one_le x
  dsimp [coreLowSecondary] at hm
  linarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem core_primary_angle (k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤coreLowPrimary k a B x) : Real.pi/2<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  by_contra! hsmall
  have hcos : 0≤Real.cos x := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [FrameLowPair.pi_lower],hsmall⟩
  have hA := mul_nonneg (by linarith [hlow.2.2.1] : 0≤A B) hcos
  have hsb := negative_signed_sin_le k (x := x) hB.1
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) hB.1
  have hw := width_one_le x
  dsimp [coreLowPrimary] at hm
  linarith

theorem low_primary_angle (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤lowCorePrimary k b a B x) : (3/10:ℝ)<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  by_contra! hsmall
  have habs : |x|≤3/10 := abs_le.mpr ⟨hx,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/10:ℝ)^2 := by
    nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) habs 2]
  have hcL : (191/200:ℝ)≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k (x := x) hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1])
    (by linarith : 0≤Real.cos x)
  have hB := mul_le_mul_of_nonneg_right
    (show B-1/2≤3/50 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp [lowCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  linarith [abs_nonneg (Real.sin x)]

end SquaresInCircles.Eight.FrameCoreLowGeometry
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighHighSecondaryScalars
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreMidScalars (ap cp trigAffine trigAffine_monotone)

def parallelValue : ℝ := Real.pi/4+g*(1-c0)
def negativeCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+g*pairWidth x+Real.pi/4-g*c0-g*(7/12)*Real.sin x
def negativeAngle (z : ℝ) : ℝ :=
  -z-(9/100)*(Real.sin z+Real.cos z-1)+Real.pi/4+g/2+
    g*((1/2-c0)+(13/12)*Real.sin z)/Real.cos z
def negativeAngleD (z : ℝ) : ℝ :=
  -1-(9/100)*(Real.cos z-Real.sin z)+
    g*((13/12)+(1/2-c0)*Real.sin z)/(Real.cos z)^2
def positiveCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+pairWidth x+Real.pi/4-c0-
    coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal+
      FrameCoreArc.diagonal*(Real.cos x-Real.sin x)

theorem parallel_lower : (8939/10000:ℝ)<parallelValue := by
  have hd := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [parallelValue,g]
  linarith

theorem negativeCore_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (8939/10000:ℝ)<negativeCore x := by
  let C : ℝ := ap+Real.pi/4-g*c0
  let b : ℝ := cp-g*(7/12)
  have hb : -(1/5:ℝ)<b ∧ b<0 := by norm_num [b,cp,g]
  have hfirst : MonotoneOn (trigAffine 1 C cp b) (Icc (0:ℝ) (Real.pi/2)) :=
    trigAffine_monotone (by norm_num) (by norm_num [cp,g,b])
  have hsecond : MonotoneOn (trigAffine 1 C (-cp) b) (Icc (Real.pi/2) Real.pi) :=
    trigAffine_monotone (by norm_num) (by norm_num [cp,g,b])
  have he1 {t : ℝ} (ht : t∈Icc 0 (Real.pi/2)) :
      negativeCore t=trigAffine 1 C cp b t := by
    dsimp [negativeCore,trigAffine,C,b,ap,cp]
    rw [(first_width ht).1,(first_width ht).2]
    ring
  have he2 {t : ℝ} (ht : t∈Icc (Real.pi/2) Real.pi) :
      negativeCore t=trigAffine 1 C (-cp) b t := by
    dsimp [negativeCore,trigAffine,C,b,ap,cp]
    rw [(second_width ht).1,(second_width ht).2]
    ring
  have he0 : negativeCore 0=parallelValue := by
    simp [negativeCore,parallelValue,pairWidth,periodicFrameCost]
    ring
  by_cases hq : x≤Real.pi/2
  · have hh := hfirst ⟨le_rfl,by positivity⟩ ⟨hx.1,hq⟩ hx.1
    rw [← he1 ⟨le_rfl,by positivity⟩,← he1 ⟨hx.1,hq⟩,he0] at hh
    exact parallel_lower.trans_le hh
  · have h1 := hfirst ⟨le_rfl,by positivity⟩ ⟨by positivity,le_rfl⟩ (by positivity)
    have h2 := hsecond ⟨le_rfl,by linarith [Real.pi_pos]⟩
      ⟨(lt_of_not_ge hq).le,hx.2⟩ (lt_of_not_ge hq).le
    rw [← he1 ⟨le_rfl,by positivity⟩,← he1 ⟨by positivity,le_rfl⟩,he0] at h1
    rw [← he2 ⟨le_rfl,by linarith [Real.pi_pos]⟩,
      ← he2 ⟨(lt_of_not_ge hq).le,hx.2⟩] at h2
    exact parallel_lower.trans_le (h1.trans h2)

theorem negativeAngle_deriv {z : ℝ} (hc : Real.cos z≠0) :
    HasDerivAt negativeAngle (negativeAngleD z) z := by
  have hbase := (((((hasDerivAt_id' z).neg).fun_sub
    ((((Real.hasDerivAt_sin z).fun_add (Real.hasDerivAt_cos z)).sub_const 1).const_mul
      (9/100))).add_const (Real.pi/4)).add_const (g/2))
  have hquot := ((((Real.hasDerivAt_sin z).const_mul (13/12)).const_add (1/2-c0)).const_mul
    g).fun_div (Real.hasDerivAt_cos z) hc
  convert hbase.fun_add hquot using 1
  · rfl
  · dsimp [negativeAngleD]
    field_simp
    linear_combination (-2600*g)*Real.sin_sq_add_cos_sq z

theorem negativeAngleD_positive {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    0<negativeAngleD z := by
  have hq := FrameLowPair.quadrant
    (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩)
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (by linarith [FrameLowPair.pi_lower] : (203/250:ℝ)≤Real.pi) hz.2
  have hc0 := cos_lower_six (show (0:ℝ)≤203/250 by norm_num)
  norm_num at hc0
  have hcpos : 0<Real.cos z := by linarith
  have hcs : Real.cos z-Real.sin z≤1 := by linarith [hq.1,hq.2.2.2]
  have hprod := mul_le_mul_of_nonneg_right hcs (sq_nonneg (Real.cos z))
  have hd := mul_le_mul_of_nonneg_right FrameHighArc.diagonal_bounds.2.le hq.1
  have hsquare := sq_nonneg ((109/100)*Real.sin z-g/5)
  have he : negativeAngleD z*(Real.cos z)^2=
      (-1-(9/100)*(Real.cos z-Real.sin z))*(Real.cos z)^2+
        g*((13/12)+(1/2-c0)*Real.sin z) := by
    dsimp [negativeAngleD]
    field_simp [hcpos.ne']
  have hnum : 0<negativeAngleD z*(Real.cos z)^2 := by
    dsimp [g] at *
    nlinarith [Real.sin_sq_add_cos_sq z]
  exact (mul_pos_iff_of_pos_right (pow_pos hcpos 2)).mp hnum

theorem negativeAngle_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    (8939/10000:ℝ)<negativeAngle z := by
  have hcos {t : ℝ} (ht : t∈Icc (0:ℝ) (203/250)) : Real.cos t≠0 := by
    have hh := FrameCoreHighGeometry.negative_trig
      (show -t∈Icc (-(203/250:ℝ)) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    rw [Real.cos_neg] at hh
    linarith [hh.2]
  have hm : MonotoneOn negativeAngle (Icc (0:ℝ) (203/250)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (negativeAngle_deriv (hcos ht)).continuousAt.continuousWithinAt
    · exact fun t ht => negativeAngle_deriv (hcos (Ioo_subset_Icc_self ht))
    · exact fun t ht => (negativeAngleD_positive (Ioo_subset_Icc_self ht)).le
  have hh := hm ⟨le_rfl,by norm_num⟩ hz hz.1
  have he : negativeAngle 0=parallelValue := by simp [negativeAngle,parallelValue]; ring
  rw [he] at hh
  exact parallel_lower.trans_le hh

theorem core_diagonal_state : CoreState FrameCoreArc.diagonal FrameCoreArc.diagonal := by
  right
  exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl,
    by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩

theorem positiveCore_lower {x : ℝ} (hx : x∈Icc (9/20:ℝ) Real.pi) :
    (47/50:ℝ)<positiveCore x := by
  let C : ℝ := 59/100+Real.pi/4-c0-
    coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal
  let a : ℝ := 41/100+FrameCoreArc.diagonal
  let b : ℝ := 41/100-FrameCoreArc.diagonal
  have ha : (121/125:ℝ)<a ∧ a<97/100 := by
    dsimp [a]
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1,CoreAngleEndpoint.diagonal_bounds.2]
  have hb : -(3/20:ℝ)<b ∧ b<0 := by
    dsimp [b]
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1,CoreAngleEndpoint.diagonal_bounds.2]
  have hamp : a^2+b^2<(1:ℝ)^2 := by nlinarith
  have hamp2 : (-b)^2+b^2<(1:ℝ)^2 := by nlinarith
  have hm1 : MonotoneOn (trigAffine 1 C a b) (Icc (9/20:ℝ) (Real.pi/2)) :=
    trigAffine_monotone (by norm_num) hamp
  have hm2 : MonotoneOn (trigAffine 1 C (-b) b) (Icc (Real.pi/2) Real.pi) :=
    trigAffine_monotone (by norm_num) hamp2
  have he1 {t : ℝ} (ht : t∈Icc 0 (Real.pi/2)) :
      positiveCore t=trigAffine 1 C a b t := by
    dsimp [positiveCore,trigAffine,C,a,b]
    rw [(first_width ht).1,(first_width ht).2]
    ring
  have he2 {t : ℝ} (ht : t∈Icc (Real.pi/2) Real.pi) :
      positiveCore t=trigAffine 1 C (-b) b t := by
    dsimp [positiveCore,trigAffine,C,a,b]
    rw [(second_width ht).1,(second_width ht).2]
    ring
  have hstart : (47/50:ℝ)<positiveCore (9/20) := by
    rw [he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩]
    have hc := Real.one_sub_sq_div_two_le_cos (x := (9/20:ℝ))
    have hs := Real.sin_le (show (0:ℝ)≤9/20 by norm_num)
    have ht := FrameLowPair.quadrant
      (show (9/20:ℝ)∈Icc 0 (Real.pi/2) by constructor <;> linarith [FrameLowPair.pi_lower])
    have hA := mul_le_mul_of_nonneg_right ha.1.le ht.2.2.1
    have hB := mul_le_mul_of_nonneg_right hb.1.le ht.1
    have hlabel := (label_bounds core_diagonal_state).2
    dsimp [trigAffine,C]
    nlinarith [FrameHighArc.diagonal_bounds.2,Arithmetic.pi_hand_enclosure.1]
  by_cases hq : x≤Real.pi/2
  · have hh := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx.1,hq⟩ hx.1
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by linarith [hx.1],hq⟩] at hh
    exact hstart.trans_le hh
  · have h1 := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ (by linarith [FrameLowPair.pi_lower])
    have h2 := hm2 ⟨le_rfl,by linarith [Real.pi_pos]⟩
      ⟨(lt_of_not_ge hq).le,hx.2⟩ (lt_of_not_ge hq).le
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by positivity,le_rfl⟩] at h1
    rw [← he2 ⟨le_rfl,by linarith [Real.pi_pos]⟩,
      ← he2 ⟨(lt_of_not_ge hq).le,hx.2⟩] at h2
    exact hstart.trans_le (h1.trans h2)

end SquaresInCircles.Eight.FrameCoreHighHighSecondaryScalars
end
end
end
