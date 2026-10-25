module

public import SquaresInCircles.Eight.TableFree.SecondMixedTEnvelope
public import SquaresInCircles.Eight.TableFree.SecondMixedAffineScalars
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Circle supports for negative outer to negative core at role three

The transverse owner has one concave full-circle support.  The side
primary owner has one decreasing unsquared support on the entire
lower quarter window.  Its endpoint comparison is an exact rational
Taylor and square-root comparison.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
