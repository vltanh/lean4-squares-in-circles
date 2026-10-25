module

public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Mixed.LHeightGrowth
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerCalculus
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCornerReferences
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoSide
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide

/-!
# Eight squares: both complete lower owners of the negative target row

A whole-interval transverse support handles angles through 1.5. At
later angles, small source coordinates have a direct bound; large
source coordinates convert the original secondary separator to the
already closed primary separator at exactly the same two points.
-/

section
/-!
## Circle supports for negative outer to negative core at role three

The transverse owner has one concave full-circle support.  The side
primary owner has one decreasing unsquared support on the entire
lower quarter window.  Its endpoint comparison is an exact rational
Taylor and square-root comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def g : ℝ := 7789/12500
def c₀ : ℝ := 16823/100000
abbrev q := MixedTEnvelope.q
abbrev k := MixedTEnvelope.k
def γ : ℝ := 17953/20000
def value (b B φ : ℝ) : ℝ := φ-T b+c₀+g*B

def N (φ : ℝ) : ℝ := CircularNorm.norm (g^2+q^2) (-2*g*q) 0 φ
def transverse (φ : ℝ) : ℝ := φ+c₀-k+(g+q)/2+g*Real.sin φ-CommonQuarter.radius*N φ
def transverseD (φ : ℝ) : ℝ := 1+g*Real.cos φ-
  CommonQuarter.radius*CircularNorm.d1 (g^2+q^2) (-2*g*q) 0 φ
def transverseDD (φ : ℝ) : ℝ := -g*Real.sin φ-
  CommonQuarter.radius*CircularNorm.d2 (g^2+q^2) (-2*g*q) 0 φ

lemma norm_domain (φ : ℝ) : 0<CircularNorm.energy (g^2+q^2) (-2*g*q) 0 φ := by
  have hc := Real.cos_le_one φ
  norm_num [CircularNorm.energy,g,q,MixedTEnvelope.q]
  nlinarith

lemma norm_sq (φ : ℝ) : (N φ)^2=g^2+q^2-2*g*q*Real.cos φ := by
  have h := CircularNorm.norm_sq (norm_domain φ).le
  dsimp only [N]
  rw [h]
  dsimp only [CircularNorm.energy]
  ring

lemma norm_positive (φ : ℝ) : 0<N φ := CircularNorm.norm_pos (norm_domain φ)

lemma transverse_hasDerivAt (φ : ℝ) : HasDerivAt transverse (transverseD φ) φ := by
  have hN : HasDerivAt N (CircularNorm.d1 (g^2+q^2) (-2*g*q) 0 φ) φ :=
    CircularNorm.norm_hasDerivAt (norm_domain φ)
  exact (((((hasDerivAt_id' φ).add_const c₀).sub_const k).add_const ((g+q)/2)).add
    ((Real.hasDerivAt_sin φ).const_mul g)).sub (hN.const_mul CommonQuarter.radius)

lemma transverseD_hasDerivAt (φ : ℝ) : HasDerivAt transverseD (transverseDD φ) φ := by
  have hD : HasDerivAt (fun x => CircularNorm.d1 (g^2+q^2) (-2*g*q) 0 x)
      (CircularNorm.d2 (g^2+q^2) (-2*g*q) 0 φ) φ :=
    CircularNorm.d1_hasDerivAt (norm_domain φ)
  exact ((((Real.hasDerivAt_cos φ).const_mul g).const_add 1).sub
    (hD.const_mul CommonQuarter.radius)).congr_deriv (by dsimp only [transverseDD]; ring)

lemma transverse_curvature {φ : ℝ} (hφ : Lower φ) : transverseDD φ<0 := by
  have ht := lower_trig hφ
  have hn := norm_sq φ
  have hp := norm_positive φ
  have hN : N φ<(89/100:ℝ) := by
    norm_num [g,q,MixedTEnvelope.q] at hn
    nlinarith [ht.2.2.1]
  have hc := CircularNorm.curvature_lower (norm_domain φ)
    (show (-2*g*q)^2+(0:ℝ)^2≤(g^2+q^2)^2 by nlinarith [sq_nonneg (g^2-q^2)])
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hh := mul_le_mul_of_nonneg_left hc hR.le
  have hRN := (mul_lt_mul_of_pos_left hN hR).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<89/100))
  change CommonQuarter.radius*(-N φ/4)≤CommonQuarter.radius*CircularNorm.d2 (g^2+q^2) (-2*g*q) 0 φ at hh
  have hgs : g*(19121/25000)<g*Real.sin φ := mul_lt_mul_of_pos_left ht.1 (by norm_num [g])
  have hg : g=7789/12500 := rfl
  dsimp only [transverseDD]
  nlinarith

lemma transverse_left : (49/50:ℝ)<transverse lowerAngle := by
  have ht := MixedAffine.left_trig
  have hn := norm_sq lowerAngle
  have hp := norm_positive lowerAngle
  have hN : N lowerAngle<(53/100:ℝ) := by
    norm_num [g,q,MixedTEnvelope.q] at hn
    nlinarith [ht.2.2.1]
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<53/100))
  have ha : (87079/100000:ℝ)<lowerAngle := by
    dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hgs : g*(19121/25000)<g*Real.sin lowerAngle :=
    mul_lt_mul_of_pos_left ht.1 (by norm_num [g])
  have hg : g=7789/12500 := rfl
  dsimp only [transverse]
  norm_num [c₀,q,k,MixedTEnvelope.q,MixedTEnvelope.k]
  nlinarith

lemma transverse_right : (1:ℝ)<transverse (1409/1000) := by
  have hs := HighOrderTaylor.S11_le_sin (x := (1409/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1409/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8] at hs hc
  have hs0 : (9869/10000:ℝ)<Real.sin (1409/1000) := by linarith
  have hc0 : (161/1000:ℝ)<Real.cos (1409/1000) := by linarith
  have hn := norm_sq (1409/1000)
  have hp := norm_positive (1409/1000)
  have hN : N (1409/1000)<(407/500:ℝ) := by
    norm_num [g,q,MixedTEnvelope.q] at hn
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<407/500))
  dsimp [transverse,g,c₀,q,k,MixedTEnvelope.q,MixedTEnvelope.k]
  nlinarith

lemma transverse_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (1409/1000)) :
    (49/50:ℝ)<transverse φ := by
  have hc : ConcaveOn ℝ (Icc lowerAngle (1409/1000)) transverse :=
    concave_of_deriv2 (fun x _ => transverse_hasDerivAt x)
      (fun x _ => transverseD_hasDerivAt x)
      (fun x hx => (transverse_curvature
        (show Lower x from ⟨hx.1,by linarith [hx.2,pi_hand_enclosure.1]⟩)).le)
  exact concave_gt_of_endpoints hc hφ transverse_left (by linarith [transverse_right])

def sideK : ℝ := Real.pi/2+c₀-k+(g+q)/2-γ
def sideN (x : ℝ) : ℝ := Real.sqrt (g^2+q^2*(Real.cos x)^2)
def side (x : ℝ) : ℝ := (sideK-x)*Real.cos x+g*(1+(13/12)*Real.sin x)-CommonQuarter.radius*sideN x
def sideD (x : ℝ) : ℝ := ((13/12)*g-1)*Real.cos x-(sideK-x)*Real.sin x+
  CommonQuarter.radius*q^2*Real.sin x*Real.cos x/sideN x

lemma side_domain (x : ℝ) : 0<g^2+q^2*(Real.cos x)^2 := by
  have hs := sq_nonneg (q*Real.cos x)
  norm_num [g]
  nlinarith

lemma sideN_positive (x : ℝ) : 0<sideN x := Real.sqrt_pos.mpr (side_domain x)
lemma sideN_sq (x : ℝ) : (sideN x)^2=g^2+q^2*(Real.cos x)^2 :=
  Real.sq_sqrt (side_domain x).le

lemma sideN_hasDerivAt (x : ℝ) :
    HasDerivAt sideN (-q^2*Real.sin x*Real.cos x/sideN x) x := by
  have hp := (sideN_positive x).ne'
  exact ((((Real.hasDerivAt_cos x).pow 2).const_mul (q^2)).const_add (g^2)).sqrt
    (side_domain x).ne' |>.congr_deriv (by
      change q^2*(((2:ℕ):ℝ)*Real.cos x^(2-1)*-Real.sin x)/(2*sideN x)=_
      norm_num
      field_simp)

lemma side_hasDerivAt (x : ℝ) : HasDerivAt side (sideD x) x := by
  exact ((((hasDerivAt_id' x).const_sub sideK).mul (Real.hasDerivAt_cos x)).add
    ((((Real.hasDerivAt_sin x).const_mul (13/12)).const_add 1).const_mul g)).sub
      ((sideN_hasDerivAt x).const_mul CommonQuarter.radius) |>.congr_deriv (by dsimp only [sideD]; ring)

lemma sideK_bounds : (135853/100000:ℝ)<sideK ∧ sideK<(67927/50000:ℝ) := by
  dsimp [sideK,g,c₀,q,k,γ,MixedTEnvelope.q,MixedTEnvelope.k]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma sideD_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : sideD x<0 := by
  have ht := positive_trig hx
  have hc0 : 0<Real.cos x := by linarith [ht.1]
  have hs0 := ht.2.2.1
  have hn := sideN_sq x
  have hp := sideN_positive x
  have hN : (789/1000:ℝ)<sideN x := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19121/25000) ht.1.le 2
    norm_num [g,q,MixedTEnvelope.q] at hn
    by_contra hc
    have hcc := mul_le_mul (le_of_not_gt hc) (le_of_not_gt hc) hp.le (by norm_num : (0:ℝ)≤789/1000)
    linarith
  have hratio : CommonQuarter.radius*q^2<(503/500)*sideN x := by
    norm_num [q,MixedTEnvelope.q]
    linarith [radius_bounds.2]
  have hsc := mul_nonneg hs0 hc0.le
  have hterm : CommonQuarter.radius*q^2*Real.sin x*Real.cos x/sideN x≤
      (503/500)*Real.sin x*Real.cos x := by
    apply (div_le_iff₀ hp).2
    have hm := mul_le_mul_of_nonneg_right hratio.le hsc
    linarith
  have hK0 : 0≤ sideK-7/10 := by linarith [sideK_bounds.1]
  have hcut := mul_le_mul_of_nonneg_left ht.2.1 (mul_nonneg hK0 hs0)
  have hangle := mul_nonneg (show 0≤7/10-x by linarith [hx.2]) hs0
  have hloss : (sideK-7/10)*Real.sin x*Real.cos x≤(sideK-x)*Real.sin x := by
    linarith
  have hKs := mul_nonneg (show 0≤ sideK-135853/100000 by linarith [sideK_bounds.1]) hs0
  have hcoef : (13/12)*g-1+((503/500)-(sideK-7/10))*Real.sin x<0 := by
    norm_num [g]
    linarith [ht.2.2.2.1]
  have hnegative := mul_neg_of_neg_of_pos hcoef hc0
  dsimp only [sideD]
  linarith

lemma side_right : (1/5000:ℝ)<side (7/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (8052721/12500000:ℝ)<Real.sin (7/10) := by linarith [ht.1.1]
  have hc : (38242109/50000000:ℝ)<Real.cos (7/10) ∧
      Real.cos (7/10)<76484219/100000000 :=
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩
  have hN : sideN (7/10)<(986372/1250000:ℝ) := by
    have he := sideN_sq (7/10)
    have hp := sideN_positive (7/10)
    have hsq := pow_le_pow_left₀ (by linarith [hc.1] : 0≤Real.cos (7/10)) hc.2.le 2
    norm_num [g,q,MixedTEnvelope.q] at he
    nlinarith
  have hR : CommonQuarter.radius<(494697/250000:ℝ) := by
    have h := radius_sq
    norm_num [Q0] at h
    nlinarith [radius_bounds.1]
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right hR (by norm_num : (0:ℝ)<986372/1250000))
  have hK : (65853632679/100000000000:ℝ)<sideK-7/10 := by
    dsimp [sideK,g,c₀,q,k,γ,MixedTEnvelope.q,MixedTEnvelope.k]
    linarith [pi_hand_enclosure.1]
  have hproduct := (mul_lt_mul_of_pos_left hc.1
    (by norm_num : (0:ℝ)<65853632679/100000000000)).trans
      (mul_lt_mul_of_pos_right hK (by linarith [hc.1] : 0<Real.cos (7/10)))
  dsimp [side,g]
  nlinarith

lemma side_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0<side x := by
  have hm : AntitoneOn side (Icc (0:ℝ) (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => (side_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => side_hasDerivAt x)
      (fun x hx => (sideD_negative (Ioo_subset_Icc_self hx)).le)
  have hh := hm hx (by norm_num) hx.2
  linarith [side_right]

end SquaresInCircles.Eight.SecondWord.MixedOuterNegative
end
end
end

section
/-!
## Whole-corner curvature, with one complete early and one late range

The early growth inequality makes the cost concave in the core
coordinate. On the late rectangle its core curvature increases in
angle, and its entire terminal edge lies below 7/4. No coordinate
or angle enclosure table is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lower_trig)

lemma early_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) (he : φ≤11/10) :
    fBB B φ<0 := by
  have hu := early_height hB hφ he
  have hg := PHeightTaylor.early_growth hu
  have hdom : u B φ∈PHeightBounds.heights := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hd := PHeightTaylor.d2_positive hdom
  have hfirst := PHeightTaylor.d1_positive hdom
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hc := PositiveThree.lower_cos_antitone (lower_mem hφ) (lower_mem hi) he
  have hcos : (9/20:ℝ)<Real.cos φ := by linarith [transition_trig.2.2.1]
  have hprod := mul_lt_mul_of_pos_left hcos hfirst
  have hdelta : 0<PHeightTaylor.d1 (u B φ)*Real.cos φ-h := by dsimp [h]; nlinarith
  have hpay : PHeightTaylor.d2 (u B φ)<12*(PHeightTaylor.d1 (u B φ)*Real.cos φ-h) := by
    dsimp [h]
    nlinarith
  have hLsq : (L B φ)^2≤1+(MixedCorner.w B)^2 := by
    nlinarith [LN_circle B φ,sq_nonneg (N B φ)]
  have hp := mul_le_mul_of_nonneg_left hLsq hd.le
  have hq := mul_le_mul_of_nonneg_left (D_bounds hB).2.1 hdelta.le
  have hr := mul_lt_mul_of_pos_right hpay (by positivity : 0<1+(MixedCorner.w B)^2)
  dsimp [fBB,z]
  nlinarith

lemma late_angle_curvature_positive {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    0<fBBAngle B φ := by
  have hu := PHeightTaylor.late_bounds (late_height hB hφ)
  have hsp := speed_bounds hB (late_subset hφ)
  have hD := D_bounds hB
  have ht := lower_trig (lower_mem (late_subset hφ))
  have hi : (11/10:ℝ)∈angles := ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have hsm := PositiveThree.lower_sin_monotone (lower_mem hi) (lower_mem (late_subset hφ)) hφ.1
  have hsin : (89/100:ℝ)<Real.sin φ := by linarith [transition_trig.1]
  have hmass : 0<1+(MixedCorner.w B)^2 := by positivity
  have hLsq : (L B φ)^2≤1+(MixedCorner.w B)^2 := by
    nlinarith [LN_circle B φ,sq_nonneg (N B φ)]
  have hLN : -(1+(MixedCorner.w B)^2)≤2*L B φ*N B φ := by
    nlinarith [LN_circle B φ,sq_nonneg (L B φ+N B φ)]
  have hc3 : 0≤PHeightTaylor.c3*speed B φ := mul_nonneg (by norm_num [PHeightTaylor.c3]) hsp.1.le
  have hc3u : PHeightTaylor.c3*speed B φ≤(109/50:ℝ) := by
    dsimp [PHeightTaylor.c3]
    linarith [hsp.1,hsp.2]
  have h1 := (mul_le_mul_of_nonneg_left hLsq hc3).trans
    (mul_le_mul_of_nonneg_right hc3u hmass.le)
  have h2 := mul_le_mul_of_nonneg_left hLN hu.2.1.le
  have h2u := mul_le_mul_of_nonneg_right hu.2.2.le hmass.le
  have hsinprod := mul_le_mul hu.1.le hsin.le (by norm_num : (0:ℝ)≤89/100)
    (by linarith [hu.1] : 0≤PHeightTaylor.d1 (u B φ))
  have h3 := mul_le_mul_of_nonneg_left hsinprod hD.1.le
  have h3lo := mul_le_mul_of_nonneg_left hD.2.1 (by norm_num : (0:ℝ)≤(909/1000)*(89/100))
  have hremain := mul_nonneg hD.1.le
    (mul_nonneg (mul_nonneg hu.2.1.le hsp.1.le) ht.2.2.1)
  dsimp [fBBAngle]
  nlinarith

lemma late_curvature_monotone {B : ℝ} (hB : B∈MixedCorner.domain) :
    MonotoneOn (fBB B) lateAngles :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (fBB_angle_hasDerivAt B φ).continuousAt.continuousWithinAt)
    (fun φ _ => fBB_angle_hasDerivAt B φ)
    (fun _ hφ => (late_angle_curvature_positive hB (Ioo_subset_Icc_self hφ)).le)

lemma terminal_curvature {B : ℝ} (hB : B∈MixedCorner.domain) : fBB B (1191/1000)<(7/4:ℝ) := by
  have hu := PHeightTaylor.terminal_bounds (terminal_height hB)
  have hD := D_bounds hB
  have hw := MixedCorner.w_bounds hB
  have hcos : 0≤Real.cos (1191/1000) := by linarith [terminal_trig.2.2.1]
  have hsin : 0≤Real.sin (1191/1000) := by linarith [terminal_trig.1]
  have hwc := mul_le_mul_of_nonneg_right hw.2 hcos
  have hL : 0≤L B (1191/1000) ∧ L B (1191/1000)<(13/10:ℝ) := by
    have hp := mul_nonneg hw.1 hcos
    dsimp [L]
    exact ⟨by linarith,by linarith [terminal_trig.2.1,terminal_trig.2.2.2]⟩
  have hL2 : (L B (1191/1000))^2<(13/10:ℝ)^2 := by nlinarith
  have hd : 0<PHeightTaylor.d2 (u B (1191/1000)) := PHeightTaylor.d2_positive
    ⟨by linarith [(terminal_height hB).1],by linarith [(terminal_height hB).2]⟩
  have hfirst := (mul_le_mul_of_nonneg_left hL2.le hd.le).trans
    (mul_le_mul_of_nonneg_right hu.2.le (by norm_num : (0:ℝ)≤(13/10:ℝ)^2))
  have hdc := mul_le_mul hu.1.le terminal_trig.2.2.1.le
    (by norm_num : (0:ℝ)≤370731/1000000) (by linarith [hu.1] : 0≤PHeightTaylor.d1 (u B (1191/1000)))
  have hdelta : -(27/5000:ℝ)≤PHeightTaylor.d1 (u B (1191/1000))*Real.cos (1191/1000)-h := by
    dsimp [h]
    linarith
  have hp := mul_le_mul_of_nonneg_right hdelta hD.1.le
  dsimp [fBB,z]
  nlinarith [hD.2.2]

theorem late_curvature {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈lateAngles) :
    fBB B φ<(7/4:ℝ) :=
  (late_curvature_monotone hB hφ (show (1191/1000:ℝ)∈lateAngles by norm_num [lateAngles]) hφ.2).trans_lt
    (terminal_curvature hB)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
end
end
end

section
/-!
## The complete negative-core corner primary owner

The two endpoint curves are bounded by their exact interior references
and a uniform positive angular curvature. Concavity in the core
coordinate handles the whole early corner, and the explicit chord
loss handles the whole late corner. The final comparison uses only
the original weak separator and original physical source.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

lemma join_mem : (1/2:ℝ)∈MixedCorner.domain :=
  ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
lemma diagonal_mem : dc∈MixedCorner.domain :=
  ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩

theorem diagonal_lower {φ : ℝ} (hφ : φ∈angles) : (3591/4000:ℝ)<f dc φ := by
  have hr : (1049/1000:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f dc) (d := fAngle dc) (dd := fAngleD dc)
    (κ := (1/20:ℝ)) hφ hr (fun φ _ => f_angle_hasDerivAt dc φ)
    (fun φ _ => fAngle_hasDerivAt dc φ) (fun _ hx => (angle_curvature diagonal_mem hx).le)
  have hd := abs_lt.mp diagonal_reference.2
  have hs : (fAngle dc (1049/1000))^2<(1/1000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((1/20)*(φ-1049/1000)+fAngle dc (1049/1000))
  nlinarith [diagonal_reference.1]

theorem join_lower {φ : ℝ} (hφ : φ∈angles) : (4501/5000:ℝ)<f (1/2) φ := by
  have hr : (29/25:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f (1/2)) (d := fAngle (1/2)) (dd := fAngleD (1/2))
    (κ := (1/20:ℝ)) hφ hr (fun φ _ => f_angle_hasDerivAt (1/2) φ)
    (fun φ _ => fAngle_hasDerivAt (1/2) φ) (fun _ hx => (angle_curvature join_mem hx).le)
  have hd := abs_lt.mp join_reference.2
  have hs : (fAngle (1/2) (29/25))^2<(1/2500:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((1/20)*(φ-29/25)+fAngle (1/2) (29/25))
  nlinarith [join_reference.1]

theorem diagonal_late {φ : ℝ} (hφ : φ∈lateAngles) : (89849/100000:ℝ)<f dc φ := by
  have hr : (11/10:ℝ)∈angles :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith [pi_hand_enclosure.2],by norm_num⟩
  have ht := curvature_tangent (f := f dc) (d := fAngle dc) (dd := fAngleD dc)
    (κ := (1/20:ℝ)) (late_subset hφ) hr (fun φ _ => f_angle_hasDerivAt dc φ)
    (fun φ _ => fAngle_hasDerivAt dc φ) (fun _ hx => (angle_curvature diagonal_mem hx).le)
  have hp := mul_nonneg late_reference.2.le (sub_nonneg.mpr hφ.1)
  nlinarith [late_reference.1,sq_nonneg (φ-11/10)]

theorem lower {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈angles) : γ<f B φ := by
  by_cases he : φ≤11/10
  · have hc : ConcaveOn ℝ (Icc (1/2) dc) (fun B => f B φ) :=
      concave_of_deriv2 (fun _ hB => f_core_hasDerivAt hB)
        (fun _ hB => fB_hasDerivAt hB) (fun _ hB => (early_curvature hB hφ he).le)
    exact concave_gt_of_endpoints (f := fun B => f B φ) hc hB
      (by dsimp only [γ]; linarith [join_lower hφ]) (by dsimp only [γ]; linarith [diagonal_lower hφ])
  · have hlate : φ∈lateAngles := ⟨by linarith,hφ.2⟩
    have hh := curvature_chord_lower (f := fun B => f B φ) (d := fun B => fB B φ)
      (dd := fun B => fBB B φ) (l := 1/2) (u := dc) (κ := (7/4:ℝ)) (m := (89849/100000:ℝ))
      hB (by norm_num)
      (fun _ hB => f_core_hasDerivAt hB) (fun _ hB => fB_hasDerivAt hB)
      (fun _ hB => (late_curvature hB hlate).le)
      (by linarith [join_lower hφ]) (diagonal_late hlate)
    have hlength : 0≤dc-1/2 ∧ dc-1/2<(59/1000:ℝ) := by
      exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],
        by linarith [CoreAngleEndpoint.diagonal_bounds.2]⟩
    have hs : (dc-1/2)^2<(59/1000:ℝ)^2 := by nlinarith
    dsimp only [γ] at hh ⊢
    linarith

theorem original_primary {a b A B φ : ℝ} (hs : OuterState a b)
    (hB : 1/2≤B) (hBA : B≤A) (hcircle : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2)
    (hφ : PositiveThree.Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    γ<value b A B φ := by
  have ht : CoreState A B := Or.inr ⟨hB,hBA,hcircle⟩
  by_cases he : (1191/1000:ℝ)≤φ
  · exact corner_tail hs ht hB he
  · have hangle : φ∈angles := ⟨hφ.1,by linarith⟩
    obtain ⟨hdom,rfl⟩ := MixedCorner.actual hB hBA hcircle
    have hu := u_bounds hdom hangle
    have heq : 1+(MixedCorner.a B+1/2)*Real.cos φ+(1/2-B)*Real.sin φ=u B φ := by
      dsimp [u]
      ring
    have hh := primary_height_lower hs
      (show 1+(MixedCorner.a B+1/2)*Real.cos φ+(1/2-B)*Real.sin φ∈PHeightBounds.heights by
        rw [heq]
        exact ⟨by linarith [hu.1],by linarith [hu.2]⟩) hsep
    rw [heq] at hh
    exact (lower hdom hangle).trans hh

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Corner
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)
open MixedTransverseSupport

def support (φ : ℝ) : ℝ := lower (1909/2000) (853/1000) (e-1239/50000) φ

lemma support_left : (97/100:ℝ)<support lowerAngle := by
  have ht := MixedAffine.left_trig
  have hn := lower_sq_wide (g := (1909/2000:ℝ)) (p := (853/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) lowerAngle
  have hp : 0<lowerN (1909/2000) (853/1000) lowerAngle := CircularNorm.norm_pos
    (lower_domain_wide (by norm_num) (by norm_num) (by norm_num) lowerAngle)
  have hN : lowerN (1909/2000) (853/1000) lowerAngle<(96/125:ℝ) := by nlinarith [ht.2.2.1]
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<96/125))
  have hL : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [support,lower,e]
  linarith [ht.1,pi_hand_enclosure.1]

lemma support_right : (907/1000:ℝ)<support (3/2) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (3/2:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (3/2:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  have hn := lower_sq_wide (g := (1909/2000:ℝ)) (p := (853/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (3/2)
  have hp : 0<lowerN (1909/2000) (853/1000) (3/2) := CircularNorm.norm_pos
    (lower_domain_wide (by norm_num) (by norm_num) (by norm_num) (3/2))
  have hN : lowerN (1909/2000) (853/1000) (3/2)<(12343/10000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<12343/10000))
  dsimp [support,lower,e]
  linarith

lemma support_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (3/2)) : γ<support φ := by
  have hc : ConcaveOn ℝ (Icc lowerAngle (3/2)) support :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt_wide (by norm_num) (by norm_num) (by norm_num) (e-1239/50000) x)
      (fun x _ => lowerD_hasDerivAt_wide (by norm_num) (by norm_num) (by norm_num) x)
      (fun x hx => (lower_curvature_wide (by norm_num) (by norm_num) (by norm_num)
        (show Lower x from ⟨hx.1,by linarith [hx.2,pi_hand_enclosure.1]⟩)).le)
  exact concave_gt_of_endpoints hc hφ
    (by dsimp [γ]; linarith [support_left]) (by dsimp [γ]; linarith [support_right])

theorem lower_primary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) : γ<value b A B φ := by
  rcases ht with ⟨rfl,hB,hBu⟩ | ⟨hB,hBA,hcircle⟩
  · exact Side.original_primary hs ⟨hB,hBu⟩ hφ hsep
  · exact Corner.original_primary hs hB hBA hcircle hφ hsep

theorem lower_secondary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) : γ<value b A B φ := by
  by_cases he : φ≤3/2
  · have hP := P_chord (NegativeTwo.source_mem hs)
    have hcore := core_affine ht
    have hc := outer_circle_lower (X := -(1909/2000)*Real.sin φ)
      (Y := (1909/2000)*Real.cos φ-853/1000) hs
    have hnorm : Real.sqrt ((-(1909/2000)*Real.sin φ)^2+
        ((1909/2000)*Real.cos φ-853/1000)^2)=lowerN (1909/2000) (853/1000) φ := by
      dsimp [lowerN,CircularNorm.norm,CircularNorm.energy]
      congr 1
      linear_combination (1909/2000:ℝ)^2*(Real.sin_sq_add_cos_sq φ)
    rw [hnorm] at hc
    have hh := support_lower ⟨hφ.1,he⟩
    dsimp [support,lower,value] at *
    nlinarith
  · by_cases hb : b≤7/10
    · have hP := MixedTwo.PositiveCore.P_seven_chord ⟨hs.1,hb⟩
      have hcore := core_minimum ht
      dsimp [value,e,γ] at *
      linarith
    · have htφ := lower_trig hφ
      have hEnd : Lower (3/2:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
        by linarith [pi_hand_enclosure.1]⟩
      have hsm := PositiveThree.lower_sin_monotone hEnd hφ (by linarith)
      have hsref := HighOrderTaylor.S15_le_sin (x := (3/2:ℝ)) (by norm_num)
      norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7] at hsref
      have hsin : (997/1000:ℝ)<Real.sin φ := by linarith
      have hA := (CoreAngleEndpoint.state_bounds ht).2.1
      have ha : 0≤a-1/2 := by linarith [(NegativeTwo.primary_mem hs).1,fine_outer_endpoint_bounds.2]
      have hac := mul_nonneg ha htφ.2.2.1
      have hbs := mul_le_mul (show (6/5:ℝ)≤b+1/2 by linarith) hsin.le
        (by norm_num : (0:ℝ)≤997/1000) (by linarith [hs.1] : 0≤b+1/2)
      have hreserve : 0≤(a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ-A-1/2 := by nlinarith
      have hp := mul_nonneg htφ.2.2.1 hreserve
      have hpaid := mul_le_mul_of_nonneg_right hsep (by linarith [htφ.1] : 0≤Real.sin φ)
      have hid : a-A*Real.cos φ+B*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2-
          Real.sin φ*(a*Real.sin φ-b*Real.cos φ+B-(1+Real.sin φ+Real.cos φ)/2)=
        Real.cos φ*((a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ-A-1/2) := by
        linear_combination (-(a-1/2))*(Real.sin_sq_add_cos_sq φ)
      exact lower_primary hs ht hφ (by nlinarith)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget
end
end
end
