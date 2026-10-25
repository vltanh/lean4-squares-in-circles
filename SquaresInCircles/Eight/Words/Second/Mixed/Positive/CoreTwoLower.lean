module

public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.SupportThird
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStripContact
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds

/-!
# Eight squares: lower owners for negative outer to positive core

The low-source regimes use the two supports on the whole angle interval. In each high-source
regime a relaxed contact cost decreases all the way to alignment at the same original outer point
(`secondaryContact_antitone`, `primaryContact_antitone`). The two owners are `lower_secondary`
and `lower_primary`.
-/

section
/-!
## Original P-label chords for the positive core target

Convexity of P gives both restricted chords from one fixed physical
circle point apiece.  The aligned cost uses the already proved
primary-coordinate derivative and the actual unit-primary point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def g : ℝ := 1303/1250
def e : ℝ := 1449/100000
def c : ℝ := 1029/100000
def γ : ℝ := 17953/20000
def value (b B φ : ℝ) : ℝ := φ+e-P b-g*B
def aligned (a b : ℝ) : ℝ := Real.pi/2+e-P b-g*(a-1)

lemma P_restricted_chord {l q b : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hend : P l≤1239/50000+q*l) (hb : b∈Icc 0 l) :
    P b≤1239/50000+q*b := by
  let f : ℝ→ℝ := fun y => (1239/50000:ℝ)+q*y-P y
  have hdom {y : ℝ} (hy : y∈Icc 0 l) : y∈Icc 0 outerDiagonal := ⟨hy.1,hy.2.trans hl.2⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) l) f :=
    concave_of_deriv2
      (fun y hy => by
        convert (PLabel.affine_difference_hasDerivAt q (outer_domain (hdom hy))).const_add
          (1239/50000) using 1
        dsimp [f,P]; ring_nf)
      (fun y hy => (PLabel.d1_hasDerivAt (outer_domain (hdom hy))).const_sub q)
      (fun y hy => neg_nonpos.mpr (P_second_positive (hdom hy)).le)
  have hz : f 0=0 := by dsimp [f]; rw [P_zero]; ring
  have he : 0≤f l := by dsimp [f]; linarith
  have hh := hc.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 l from ⟨le_rfl,hl.1⟩)
    (show l∈Icc 0 l from ⟨hl.1,le_rfl⟩) hb
  rw [hz,min_eq_left he] at hh
  dsimp [f] at hh
  linarith

lemma P_half_reference : P (1/2)<1239/50000+(1617/2000)*(1/2) := by
  have hh := shifted_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (show (1/2:ℝ)∈Icc 0 (899/1000) by norm_num)))
    (l := (683/400:ℝ)) (u := (4269/2500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  change 683/400<arc (1/2)+1/2 ∧ arc (1/2)+1/2<4269/2500 at hh
  norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  linarith [hh.1]

lemma P_seven_reference : P (7/10)<1239/50000+(8281/10000)*(7/10) := by
  have hh := shifted_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (show (7/10:ℝ)∈Icc 0 (899/1000) by norm_num)))
    (l := (7867/5000:ℝ)) (u := (3147/2000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  change 7867/5000<arc (7/10)+1/2 ∧ arc (7/10)+1/2<3147/2000 at hh
  norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  linarith [hh.1]

lemma P_half_chord {b : ℝ} (hb : b∈Icc (0:ℝ) (1/2)) :
    P b≤1239/50000+(1617/2000)*b :=
  P_restricted_chord (Asymmetric.rational_outer_mem (by norm_num)) P_half_reference.le hb

lemma P_seven_chord {b : ℝ} (hb : b∈Icc (0:ℝ) (7/10)) :
    P b≤1239/50000+(8281/10000)*b :=
  P_restricted_chord (Asymmetric.rational_outer_mem (by norm_num)) P_seven_reference.le hb

lemma aligned_zero : (89777/100000:ℝ)<Real.pi/2+e-P OppositeTwo.bOne := by
  have hh := OppositeTwo.aligned_axial_value
  have hv := V_zero_bounds.1
  dsimp [e]
  linarith

lemma primary_contact_monotone :
    MonotoneOn (fun a => PPrimaryLabel.outer a-g*(a-1)) (Icc (1:ℝ) outerAxial) := by
  have hdom {a : ℝ} (ha : a∈Icc (1:ℝ) outerAxial) : a∈Icc outerDiagonal outerAxial :=
    ⟨primary_one_mem.1.trans ha.1,ha.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun a ha => ((PPrimaryLabel.outer_hasDerivAt (primary_domain (hdom ha))).sub
      (((hasDerivAt_id a).sub_const 1).const_mul g)).continuousAt.continuousWithinAt)
    (fun a ha => (PPrimaryLabel.outer_hasDerivAt (primary_domain (hdom (Ioo_subset_Icc_self ha)))).sub
      (((hasDerivAt_id a).sub_const 1).const_mul g))
  intro a ha
  have hh := OppositeTwo.M_first_above_one (Ioo_subset_Icc_self ha)
  norm_num [g]
  linarith

theorem aligned_lower {a b : ℝ} (hs : OuterState a b) (ha : 1≤a) :
    (89777/100000:ℝ)<aligned a b := by
  have hh := primary_contact_monotone
    (show (1:ℝ)∈Icc 1 outerAxial from ⟨le_rfl,primary_one_mem.2⟩)
    (show a∈Icc 1 outerAxial from ⟨ha,(NegativeTwo.primary_mem hs).2⟩) ha
  have hm : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  have h0 : PPrimaryLabel.outer 1= -P OppositeTwo.bOne :=
    PLabel.primary_actual (primary_state primary_one_mem)
  simp only at hh
  rw [hm,h0] at hh
  dsimp [aligned]
  linarith [aligned_zero]

lemma upper_displacement_cost {a b B x k : ℝ} (hs : OuterState a b)
    (hB : 0≤B) (hx : 0≤x) (_hk : 0≤k) (hku : k≤53/100)
    (hcut : B≤a-1+k*x) : (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases ha : 1≤a
  · have hh := aligned_lower hs ha
    have hpay := mul_nonneg hx (show 0≤1-g*k by dsimp [g]; linarith)
    have hweight := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    dsimp [value,aligned] at *
    nlinarith
  · have hh := OppositeTwo.source_primary_loss_below_one
      (show a∈Icc outerDiagonal 1 from ⟨(NegativeTwo.primary_mem hs).1,by linarith⟩)
    have hm : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    have h0 : PPrimaryLabel.outer 1= -P OppositeTwo.bOne :=
      PLabel.primary_actual (primary_state primary_one_mem)
    rw [hm,h0] at hh
    have hweight := mul_le_mul_of_nonneg_left hcut (by norm_num : (0:ℝ)≤271/250)
    have hpay := mul_nonneg hx (show 0≤1-(271/250)*k by linarith)
    have hBpay := mul_nonneg hB (show 0≤271/250-g by norm_num [g])
    dsimp [value]
    nlinarith [aligned_zero]

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end

section
/-!
## Two complete lower-half supports for the positive core target

The restricted transverse chord gives a strictly concave circle
support.  The restricted primary chord gives one square completion
on the entire half.  The constants are proved from single radicals
and the actual angle endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower)

def q : ℝ := 1617/2000
def p : ℝ := 8281/10000
def K : ℝ := Real.pi/2-c+(g+p)/2-γ
def transverse (φ : ℝ) : ℝ := MixedTransverseSupport.lower g q (-c) φ

lemma transverse_left : (91/100:ℝ)<transverse lowerAngle := by
  have ht := MixedAffine.left_trig
  have hn := MixedTransverseSupport.lower_sq (g := g) (p := q)
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) lowerAngle
  have hp : 0<MixedTransverseSupport.lowerN g q lowerAngle :=
    CircularNorm.norm_pos (MixedTransverseSupport.lower_domain
      (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) lowerAngle)
  have hn' : (MixedTransverseSupport.lowerN g q lowerAngle)^2=
      174027001/100000000-2106951/1250000*Real.cos lowerAngle := by
    rw [hn]; norm_num [g,q]
  have hN : MixedTransverseSupport.lowerN g q lowerAngle<(41/50:ℝ) := by
    nlinarith [ht.2.2.1]
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<41/50))
  have ha : (87079/100000:ℝ)<lowerAngle := by
    dsimp [lowerAngle]; linarith [pi_hand_enclosure.1]
  have hgs : g*(19121/25000)<g*Real.sin lowerAngle :=
    mul_lt_mul_of_pos_left ht.1 (by norm_num [g])
  have hg : g=1303/1250 := rfl
  have hq : q=1617/2000 := rfl
  have hc : c=1029/100000 := rfl
  dsimp only [transverse,MixedTransverseSupport.lower]
  linarith

lemma transverse_right : (91/100:ℝ)<transverse (Real.pi/2) := by
  have hn := MixedTransverseSupport.lower_sq (g := g) (p := q)
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (Real.pi/2)
  have hp : 0<MixedTransverseSupport.lowerN g q (Real.pi/2) :=
    CircularNorm.norm_pos (MixedTransverseSupport.lower_domain
      (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (Real.pi/2))
  have hn' : (MixedTransverseSupport.lowerN g q (Real.pi/2))^2=174027001/100000000 := by
    rw [hn,Real.cos_pi_div_two]; norm_num [g,q]
  have hN : MixedTransverseSupport.lowerN g q (Real.pi/2)<(33/25:ℝ) := by
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<33/25))
  have hg : g=1303/1250 := rfl
  have hq : q=1617/2000 := rfl
  have hc : c=1029/100000 := rfl
  dsimp only [transverse,MixedTransverseSupport.lower]
  rw [Real.sin_pi_div_two]
  linarith [pi_hand_enclosure.1]

theorem transverse_lower {φ : ℝ} (hφ : Lower φ) : (91/100:ℝ)<transverse φ :=
  concave_gt_of_endpoints (MixedTransverseSupport.lower_concave
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (-c))
    hφ transverse_left transverse_right

lemma K_bounds : (799/500:ℝ)<K ∧ K<(1599/1000:ℝ) := by
  dsimp [K,c,g,p,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma primary_norm_zero :
    (1331/1000:ℝ)<MixedPrimarySupport.N g p 0 ∧
      MixedPrimarySupport.N g p 0<(333/250:ℝ) := by
  have hh := MixedPrimarySupport.N_sq (p := p) (x := 0)
    (show 0<g by norm_num [g])
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  have hh' : (MixedPrimarySupport.N g p 0)^2=177234737/100000000 := by
    rw [hh]; norm_num [g,p]
  constructor <;> nlinarith

lemma primary_gain :
    (509/1000:ℝ)<MixedPrimarySupport.gain g p ∧ MixedPrimarySupport.gain g p<(51/100:ℝ) := by
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  constructor
  · apply (lt_div_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_bounds.1
    have hN := primary_norm_zero.2
    norm_num [g,p] at *
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_bounds.2
    have hN := primary_norm_zero.1
    norm_num [g,p] at *
    nlinarith

lemma primary_zero : 0<MixedPrimarySupport.minus g p K 0 := by
  have hRN := (mul_lt_mul_of_pos_left primary_norm_zero.2
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<333/250))
  rw [MixedPrimarySupport.minus_zero]
  have hg : g=1303/1250 := rfl
  linarith [K_bounds.1]

theorem primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.minus g p K x := by
  apply MixedPrimarySupport.minus_positive
    (α := 129/1000) (β := 291/1000) (ε := 111/500)
    (by norm_num [g]) (by linarith [K_bounds.1])
  · linarith [K_bounds.2,primary_gain.1]
  · norm_num [g]
  · norm_num [g]
  · exact primary_zero
  · norm_num [MixedPrimarySupport.linearCoefficient,g]
  · dsimp [MixedPrimarySupport.quadraticCoefficient]
    linarith [K_bounds.2,primary_gain.1]
  · dsimp only [MixedPrimarySupport.cubicCoefficient]
    have hg : g=1303/1250 := rfl
    linarith [K_bounds.1,K_bounds.2,primary_gain.2]
  · norm_num
  · norm_num
  · exact hx

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def secondaryCut (a b φ : ℝ) : ℝ :=
  (a-1/2)*Real.sin φ-(b+1/2)*Real.cos φ-1/2
def secondaryCutD (a b φ : ℝ) : ℝ :=
  (a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ
def secondaryContact (a b φ : ℝ) : ℝ := φ+e-P b-g*secondaryCut a b φ
def primaryCut (a φ : ℝ) : ℝ :=
  ((a-1/2)-(13/12)*Real.cos φ)/Real.sin φ-1/2
def primaryCutD (a φ : ℝ) : ℝ :=
  (13/12-(a-1/2)*Real.cos φ)/(Real.sin φ)^2
def primaryContact (a b φ : ℝ) : ℝ := φ+e-P b-g*primaryCut a φ

lemma harmonic_reserve {φ : ℝ} (hφ : Lower φ) :
    1≤Real.sin φ+Real.cos φ/2 := by
  have ht := lower_trig hφ
  have hp := mul_nonneg ht.2.2.1
    (show 0≤1-(5/4)*Real.cos φ by linarith [ht.2.2.2.1])
  by_contra hn
  have hs := mul_pos (show 0<1-Real.sin φ-Real.cos φ/2 by linarith)
    (show 0<1+Real.sin φ-Real.cos φ/2 by linarith [ht.1,ht.2.2.2.1])
  nlinarith [Real.sin_sq_add_cos_sq φ]

lemma secondaryCut_hasDerivAt (a b φ : ℝ) :
    HasDerivAt (secondaryCut a b) (secondaryCutD a b φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (a-1/2)).sub
    ((Real.hasDerivAt_cos φ).const_mul (b+1/2))).sub_const (1/2) using 1
  · funext x
    simp only [secondaryCut,Pi.sub_apply]
  · dsimp [secondaryCutD]
    ring

lemma secondaryContact_hasDerivAt (a b φ : ℝ) :
    HasDerivAt (secondaryContact a b) (1-g*secondaryCutD a b φ) φ := by
  convert (((hasDerivAt_id φ).add_const e).sub_const (P b)).sub
    ((secondaryCut_hasDerivAt a b φ).const_mul g) using 1
  funext x
  simp only [secondaryContact,Pi.sub_apply,id]

lemma secondaryContact_antitone {a b : ℝ} (ha : 1≤a) (hb : 1/2≤b) :
    AntitoneOn (secondaryContact a b) (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ _ => (secondaryContact_hasDerivAt a b φ).continuousAt.continuousWithinAt)
    (fun φ _ => secondaryContact_hasDerivAt a b φ)
  intro φ hφ
  have ht := lower_trig (Ioo_subset_Icc_self hφ)
  have hac := mul_nonneg (show 0≤a-1 by linarith) ht.2.2.1
  have hbs := mul_nonneg (show 0≤b-1/2 by linarith) (by linarith [ht.1] : 0≤Real.sin φ)
  have hd : 1≤ secondaryCutD a b φ := by
    dsimp [secondaryCutD]
    nlinarith [harmonic_reserve (Ioo_subset_Icc_self hφ)]
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤g by norm_num [g])
  norm_num [g] at *
  linarith

lemma primaryCut_hasDerivAt (a : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (primaryCut a) (primaryCutD a φ) φ := by
  have hs : Real.sin φ≠0 := ne_of_gt (by linarith [(lower_trig hφ).1])
  convert ((((Real.hasDerivAt_cos φ).const_mul (13/12)).const_sub (a-1/2)).div
    (Real.hasDerivAt_sin φ) hs).sub_const (1/2) using 1
  · rfl
  · dsimp [primaryCutD]
    field_simp [hs]
    nlinarith [Real.sin_sq_add_cos_sq φ]

lemma primaryContact_hasDerivAt (a b : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (primaryContact a b) (1-g*primaryCutD a φ) φ := by
  convert (((hasDerivAt_id φ).add_const e).sub_const (P b)).sub
    ((primaryCut_hasDerivAt a hφ).const_mul g) using 1
  funext x
  simp only [primaryContact,Pi.sub_apply,id]

lemma primaryContact_antitone {a b : ℝ} (ha : a≤537/500) :
    AntitoneOn (primaryContact a b) (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ hφ => (primaryContact_hasDerivAt a b hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => primaryContact_hasDerivAt a b (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have ht := lower_trig (Ioo_subset_Icc_self hφ)
  have hsine : 0<Real.sin φ := by linarith [ht.1]
  have hm := mul_le_mul_of_nonneg_right
    (show a-1/2≤287/500 by linarith) ht.2.2.1
  have hpaid := mul_le_mul_of_nonneg_left hm (show 0≤g by norm_num [g])
  have hnum : (Real.sin φ)^2<g*(13/12-(a-1/2)*Real.cos φ) := by
    have hh := sq_nonneg (Real.cos φ-g*(287/500)/2)
    dsimp [g] at *
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have he : g*primaryCutD a φ=
      g*(13/12-(a-1/2)*Real.cos φ)/(Real.sin φ)^2 := by dsimp [primaryCutD]; ring
  have hd : 1<g*primaryCutD a φ := by
    rw [he]
    exact (one_lt_div (sq_pos_of_pos hsine)).2 hnum
  linarith

theorem lower_secondary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) :
    γ<value b B φ := by
  by_cases hb : b≤1/2
  · have hP := P_half_chord ⟨hs.1,hb⟩
    have hsupp := outer_circle_lower (X := -g*Real.sin φ) (Y := g*Real.cos φ-q) hs
    have he : Real.sqrt ((-g*Real.sin φ)^2+(g*Real.cos φ-q)^2)=
        MixedTransverseSupport.lowerN g q φ := by
      dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
      congr 1
      linear_combination g^2*(Real.sin_sq_add_cos_sq φ)
    rw [he] at hsupp
    have hmargin := mul_le_mul_of_nonneg_left hsep (show 0≤g by norm_num [g])
    have hh := transverse_lower hφ
    dsimp [transverse,MixedTransverseSupport.lower,value,q,c,e,γ] at *
    nlinarith
  · have htr := lower_trig hφ
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    have hbcos := mul_nonneg hs.1 htr.2.2.1
    have haSin := mul_le_mul_of_nonneg_left (Real.sin_le_one φ)
      (show 0≤a by linarith [hs.1,hs.2.1])
    have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
    have ha : 1≤a := by linarith
    have hcut : B ≤ secondaryCut a b φ := by dsimp only [secondaryCut]; linarith
    have hweight := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := secondaryContact_antitone ha (show 1/2≤b by linarith)
      hφ (show Lower (Real.pi/2) from ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩) hφ.2
    have he : secondaryContact a b (Real.pi/2)=aligned a b := by
      simp only [secondaryContact,secondaryCut,aligned,Real.sin_pi_div_two,Real.cos_pi_div_two]
      ring
    rw [he] at hm
    have hh := aligned_lower hs ha
    dsimp only [secondaryContact,value,γ] at hm ⊢
    linarith

theorem lower_primary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ-B*Real.sin φ) :
    γ<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hA : A=(7/12:ℝ) := by
    rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,_⟩
    · rfl
    · have hAc := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤A by linarith) htr.2.2.1
      have hBs := mul_le_mul_of_nonneg_right hB hsine.le
      have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
      exfalso
      linarith [htr.2.2.2.2]
  rw [hA] at hsep
  by_cases hb : b≤7/10
  · have hP := mul_le_mul_of_nonneg_right (P_seven_chord ⟨hs.1,hb⟩) hsine.le
    have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.sin φ) hs
    have he : Real.sqrt ((-g)^2+(-p*Real.sin φ)^2)=Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      congr 1
      ring
    rw [he] at hsupp
    have hmargin := mul_le_mul_of_nonneg_left hsep (show 0≤g by norm_num [g])
    have hpos := primary_positive (lower_deviation hφ)
    have heq : MixedPrimarySupport.minus g p K (Real.pi/2-φ)=
        (φ-c+(g+p)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
          CommonQuarter.radius*Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      simp only [MixedPrimarySupport.minus,MixedPrimarySupport.N,K,
        Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
        zero_mul,one_mul,sub_zero,zero_add]
      ring
    rw [heq] at hpos
    have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
      dsimp only [value,c,e,p] at hP hpos hsupp ⊢
      linarith
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
    linarith
  · have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
    have hBc := mul_nonneg hB hsine.le
    have ha : 1≤a := by linarith [htr.2.2.1,htr.2.2.2.2]
    have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5)
      (show 6/5≤b+1/2 by linarith) 2
    have haHi : a≤537/500 := by
      have hc := hs.2.2
      norm_num [Q0] at hc
      by_contra hn
      have hsq := mul_lt_mul'' (lt_of_not_ge hn) (lt_of_not_ge hn) (by norm_num) (by norm_num)
      linarith
    have hcutEq : primaryCut a φ*Real.sin φ=
        a-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut]
      field_simp [hsine.ne']
    have hcut : B≤primaryCut a φ := by
      apply (mul_le_mul_iff_left₀ hsine).mp
      linarith
    have hweight := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := primaryContact_antitone (b := b) haHi hφ
      (show Lower (Real.pi/2) from ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩) hφ.2
    have he : primaryContact a b (Real.pi/2)=aligned a b := by
      simp only [primaryContact,primaryCut,aligned,Real.sin_pi_div_two,Real.cos_pi_div_two]
      ring
    rw [he] at hm
    have hh := aligned_lower hs ha
    dsimp only [primaryContact,value,γ] at hm ⊢
    linarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
end
end
end
