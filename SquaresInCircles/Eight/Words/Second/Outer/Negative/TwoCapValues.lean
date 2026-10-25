module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.FourthKernel
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.SourceReference
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeZeroTarget
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoInverseBounds

/-!
# Eight squares: strict reference reserves for the endpoint-angle minimum

The values below are obtained from the named physical circle cages.
They establish the initial concavity, the later increasing curvature,
and the final tangent-parabola reserve.
-/

section
/-!
## Whole-curve derivatives at the physical endpoint angle

The physical target-secondary contact supplies the height, its source speed and all derivatives
at angle `.7`. Substituting the edge labels gives the negative edge-three cost `cost`. Its third
derivative is less than `-.3` on the whole feasible arc (`third_upper`), so one fixed reference
controls its initial minimum.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD ratioDD)
open NegativeTwo.CapCurve (height k k1 k2 Domain target_mem before source_upper)

def cost (b : ℝ) : ℝ := value b (height b) (Real.pi/2-7/10)
def first (b : ℝ) : ℝ := -TLabel.d1 b+KLabel.d1 (height b)*k b
def second (b : ℝ) : ℝ :=
  -TLabel.d2 b+KLabel.d2 (height b)*(k b)^2+KLabel.d1 (height b)*k1 b
def third (b : ℝ) : ℝ :=
  -TLabel.d3 b+KLabel.d3 (height b)*(k b)^3+
    3*KLabel.d2 (height b)*k b*k1 b+KLabel.d1 (height b)*k2 b

lemma cost_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt cost (first b) b := by
  have hh := ((TLabel.outer_hasDerivAt (outer_domain hb.1)).neg).add
    ((KLabel.outer_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1))
  have hfun : cost=fun x => (Real.pi/2-7/10)+(-TLabel.outer x+KLabel.outer (height x)) := by
    funext x
    simp only [cost,value,T,K]
    ring
  rw [hfun]
  exact hh.const_add (Real.pi/2-7/10)

lemma first_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt first (second b) b := by
  have hh := ((TLabel.d1_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b
      (NegativeTwo.CapCurve.height_hasDerivAt hb.1)).mul
        (NegativeTwo.CapCurve.k_hasDerivAt hb.1))
  exact hh.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_hasDerivAt {b : ℝ} (hb : Domain b) : HasDerivAt second (third b) b := by
  have ht := NegativeTwo.CapCurve.height_hasDerivAt hb.1
  have hk := NegativeTwo.CapCurve.k_hasDerivAt hb.1
  have hk2 : HasDerivAt (fun x => (k x)^2) (2*k b*k1 b) b :=
    (hk.pow 2).congr_deriv (by norm_num)
  have hh := (((TLabel.d2_hasDerivAt (outer_domain hb.1)).neg).add
    (((KLabel.d2_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul hk2)).add
      (((KLabel.d1_hasDerivAt (outer_domain (target_mem hb))).comp b ht).mul
        (NegativeTwo.CapCurve.k1_hasDerivAt hb.1))
  exact hh.congr_deriv (by simp only [third,Function.comp_apply]; ring)

lemma source_radical_lower {b : ℝ} (hb : Domain b) : (61/40:ℝ)<U b := by
  have hu := U_positive (outer_domain hb.1)
  have hc := UW_circle (outer_domain hb.1)
  have hw : 0≤W b ∧ W b<(63/50:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hb.1.1,source_upper hb]
  have hw2 : (W b)^2<(63/50:ℝ)^2 := by nlinarith
  norm_num [Q0] at hc
  nlinarith

lemma last_term_upper {b : ℝ} (hb : Domain b) :
    KLabel.d1 (height b)*k2 b<(13/10:ℝ) := by
  have hu := U_positive (outer_domain hb.1)
  have hu0 : U b≠0 := hu.ne'
  have hU := source_radical_lower hb
  have hU5 := pow_lt_pow_left₀ hU (by norm_num : (0:ℝ)≤61/40) (by norm_num : (5:ℕ)≠0)
  have hK := K_first_bounds (target_mem hb)
  have hc := NegativeTwo.CapCurve.trig
  have hc0 : 0<NegativeTwo.CapCurve.c := by linarith [hc.1]
  have hcU : NegativeTwo.CapCurve.c<(153/200:ℝ) := by linarith [hc.2.1]
  have hw : 0<W b ∧ W b<(63/50:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hb.1.1,source_upper hb]
  have hp1 : KLabel.d1 (height b)*NegativeTwo.CapCurve.c<(116/125)*(153/200) :=
    mul_lt_mul hK.2 hcU.le hc0 (by norm_num)
  have hq : (0:ℝ)<3*Q0 := by norm_num [Q0]
  have hp2 := mul_lt_mul_of_pos_right hp1 hq
  have hp3 := mul_lt_mul hp2 hw.2.le hw.1 (by positivity)
  have he : KLabel.d1 (height b)*k2 b*(U b)^5=
      KLabel.d1 (height b)*NegativeTwo.CapCurve.c*(3*Q0)*W b := by
    rw [show k2 b=NegativeTwo.CapCurve.c*(3*Q0*W b/(U b)^5) from rfl]
    field_simp
  by_contra hh
  have hp := mul_le_mul_of_nonneg_right (not_lt.mp hh) (pow_nonneg hu.le 5)
  have hQ0 : Q0=9789/2500 := rfl
  norm_num at hU5
  linarith

theorem third_upper {b : ℝ} (hb : Domain b) : third b<(-3/10:ℝ) := by
  have hk := NegativeTwo.CapCurve.k_bounds hb.1
  have hk0 : 0<k b := by linarith [hk.1]
  have hneg1 := mul_neg_of_neg_of_pos (K_third_negative (target_mem hb)) (pow_pos hk0 3)
  have hneg2 := mul_neg_of_neg_of_pos
    (show KLabel.d2 (height b)<0 by linarith [K_second_upper (target_mem hb)])
    (mul_pos hk0 hk.2.1)
  dsimp [third]
  nlinarith [T_third_lower hb.1,last_term_upper hb]

lemma second_antitone {b : ℝ} (hb : Domain b) : AntitoneOn second (Icc 0 b) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (second_hasDerivAt (before hb ht)).continuousAt.continuousWithinAt)
    (fun t ht => second_hasDerivAt (before hb (Ioo_subset_Icc_self ht)))
    (fun t ht => by linarith [third_upper (before hb (Ioo_subset_Icc_self ht))])

end SquaresInCircles.Eight.SecondWord.NegativeThree.Cap
end
end
end

section
/-!
## Exact reserves at the named angle-cap references

The label bounds are direct substitutions into the proved physical
reference cages.  They give positive curvature through `.4`, the
near-stationary tangent reference, and a separate strict bound at the
actual diagonal-target endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height k k1 Domain target_mem)

lemma four_labels :
    TLabel.d1 (2/5)<(6761/10000:ℝ) ∧ TLabel.d2 (2/5)< -2913/5000 ∧
      (7137/10000:ℝ)<KLabel.d1 (height (2/5)) ∧
        (-339/500:ℝ)<KLabel.d2 (height (2/5)) := by
  have hs := FixedReference.target four_mem ⟨le_rfl,le_rfl⟩ four_radical
    (by norm_num) (by norm_num)
  have ht := KReference.target (target_mem four_domain) four_cage.1 four_target_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,
    KReference.valueLo,KReference.valueHi,KReference.firstLo,KReference.firstHi,
    KReference.secondLo,KReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_labels :
    T reference<(132951199/500000000:ℝ) ∧
      TLabel.d1 reference∈Icc (765874501/1000000000) (382937251/500000000) ∧
      (292887549/1000000000:ℝ)<K (height reference) ∧
      KLabel.d1 (height reference)∈Icc (789727136/1000000000) (789727137/1000000000) := by
  have hs := FixedReference.target reference_mem ⟨le_rfl,le_rfl⟩ reference_radical
    (by norm_num [reference]) (by norm_num)
  have ht := KReference.target (target_mem reference_domain) reference_cage.1
    reference_target_radical (by norm_num) (by norm_num)
  rw [show reference=(137517/500000:ℝ) from rfl] at hs ht ⊢
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,
    KReference.valueLo,KReference.valueHi,KReference.firstLo,KReference.firstHi,
    KReference.secondLo,KReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,⟨by linarith,by linarith⟩,by linarith,⟨by linarith,by linarith⟩⟩

lemma four_first : (3/50:ℝ)<first (2/5) := by
  have hp := mul_lt_mul four_labels.2.2.1 four_cage.2.1.le
    (by norm_num : (0:ℝ)<2587/2500)
    (by linarith [four_labels.2.2.1] : 0≤KLabel.d1 (height (2/5)))
  dsimp only [first]
  norm_num at hp
  linarith [four_labels.1]

lemma four_second : (6/25:ℝ)<second (2/5) := by
  have hk := NegativeTwo.CapCurve.k_bounds four_mem
  have hk0 : 0<k (2/5) := by linarith [hk.1]
  have hk2 := pow_lt_pow_left₀ four_cage.2.2.1 hk0.le (by norm_num : (2:ℕ)≠0)
  have hnegative := mul_lt_mul_of_pos_right four_labels.2.2.2 (pow_pos hk0 2)
  have hpositive := mul_lt_mul four_labels.2.2.1 four_cage.2.2.2.le
    (by norm_num : (0:ℝ)<342/625)
    (by linarith [four_labels.2.2.1] : 0≤KLabel.d1 (height (2/5)))
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [four_labels.2.1]

lemma reference_value : (4488907/5000000:ℝ)<cost reference := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,reference_labels.1,reference_labels.2.2.1]

lemma reference_first : |first reference|<(1/1000000:ℝ) := by
  have hK := reference_labels.2.2.2
  have hk := reference_cage.2
  have hlo := mul_le_mul hK.1 hk.1 (by norm_num : (0:ℝ)≤1212245417/1250000000)
    (by linarith [hK.1] : 0≤KLabel.d1 (height reference))
  have hhi := mul_le_mul hK.2 hk.2 (by linarith [hk.1] : 0≤k reference)
    (by norm_num : (0:ℝ)≤789727137/1000000000)
  dsimp [first]
  rw [abs_lt]
  norm_num at hlo hhi
  constructor <;> linarith [reference_labels.2.1.1,reference_labels.2.1.2]

lemma endpoint_source_value : T endpointUpper<(1441430267/2500000000:ℝ) := by
  have hh := FixedReference.target endpointUpper_mem ⟨le_rfl,le_rfl⟩ endpointUpper_radical
    (by norm_num [endpointUpper]) (by norm_num)
  rw [show endpointUpper=(375927951/500000000:ℝ) from rfl] at hh ⊢
  norm_num [FixedReference.valueLo,FixedReference.valueHi,
    FixedReference.firstLo,FixedReference.firstHi,FixedReference.secondLo,
    FixedReference.secondHi,Q0] at hh
  linarith

lemma endpoint_target_value : (1207117807/2000000000:ℝ)<K outerDiagonal := by
  have hd := diagonal_fine
  have hsq := pow_lt_pow_left₀ hd.1
    (by norm_num : (0:ℝ)≤89921406510940/100000000000000)
    (by norm_num : (2:ℕ)≠0)
  rw [K_diagonal]
  norm_num at hsq
  linarith

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) endpointUpper)
    (hc : height e=outerDiagonal) : (8977831/10000000:ℝ)<cost e := by
  have hed := endpoint_domain he hc
  have hm := T_monotone hed.1 endpointUpper_mem he.2
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,endpoint_source_value,endpoint_target_value]

lemma zero_value : (9/10:ℝ)<cost 0 := by
  have hb := target_mem NegativeTwo.CapCurve.zero_domain
  have hk := K_chord hb
  dsimp [cost,value]
  rw [T_zero]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1,NegativeTwo.CapCurve.zero_cage.1.1]

end SquaresInCircles.Eight.SecondWord.NegativeThree.Cap
end
end
end

section
/-!
## The complete sharp angle-cap contact bound

One tangent parabola proves the cost bound on `[0,.4]`.  Thereafter the
first derivative is concave and starts positive, so only the two true
endpoint costs can minimize the value.  The physical source interval
and its diagonal-target end are constructed by the original contact.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height Domain before target_mem)

lemma early_curvature {b : ℝ} (hb : b∈Icc 0 (2/5)) : (6/25:ℝ)≤ second b := by
  have hh := second_antitone four_domain hb (show (2/5:ℝ)∈Icc 0 (2/5) by norm_num) hb.2
  exact four_second.le.trans hh

lemma early_value {b : ℝ} (hb : b∈Icc 0 (2/5)) : (44889/50000:ℝ)<cost b := by
  have hr : reference∈Icc 0 (2/5) := by norm_num [reference]
  have ht := curvature_tangent (κ := (6/25:ℝ)) hb hr
    (fun t ht => cost_hasDerivAt (before four_domain ht))
    (fun t ht => first_hasDerivAt (before four_domain ht))
    (fun t ht => early_curvature ht)
  have hd := abs_lt.mp reference_first
  have hsq : (first reference)^2<(1/1000000000000:ℝ) := by nlinarith
  have hc := sq_nonneg ((6/25)*(b-reference)+first reference)
  nlinarith [reference_value]

theorem cost_lower {b : ℝ} (hb : Domain b) : (44889/50000:ℝ)<cost b := by
  rcases le_total b (2/5) with h | h
  · exact early_value ⟨hb.1.1,h⟩
  · obtain ⟨e,he,hc⟩ := true_endpoint
    have hed := endpoint_domain he hc
    have hbe := source_bounded_by_end hb he hc
    have hdom (t : ℝ) (ht : t∈Icc (2/5) e) : Domain t :=
      before hed ⟨by linarith [ht.1],ht.2⟩
    have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (show b∈Icc (2/5) e from ⟨h,hbe⟩)
      (fun t ht => cost_hasDerivAt (hdom t ht))
      (fun t ht => first_hasDerivAt (hdom t ht))
      (fun t ht => second_hasDerivAt (hdom t ht))
      (fun t ht => by linarith [third_upper (hdom t ht)])
      (show 0<first (2/5) by linarith [four_first])
    exact (lt_min (early_value (by norm_num)) (by linarith [endpoint_value he hc])).trans_le hm

theorem original_contact {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : NegativeTwo.TargetContact.B b (7/10)=B) :
    (44889/50000:ℝ)<value b B (Real.pi/2-7/10) := by
  have hd : Domain b := ⟨hb,by simpa only [height,hc] using hB.2⟩
  simpa only [cost,height,hc] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeThree.Cap
end
end
end

section
/-!
## Whole-domain polynomials for fixed-target contact concavity

The early-circle half uses two exact polynomials in its shifted primary
coordinate.  Their single expansions have positive remainders throughout
the whole interval.  On the late-circle half, two concave polynomials
give the required rational derivative bounds from their endpoints.
There is no interval mesh or asserted coefficient-table premise.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactPolynomial

open CommonQuarter CorePairGeometry Arithmetic
open Inverse (q N K factorD)

def early : Set ℝ := Icc (17/10) (383/200)
def late : Set ℝ := Icc (1399/1000) (171/100)

def R (u : ℝ) : ℝ :=
  Q0*q u*(q u-1/4)-u*(Q0-u^2)*(3*q u-1/2)

def A (u : ℝ) : ℝ :=
  (Q0-u^2)*(N u)^2*(q u-4/25)-(4/25)*(Inverse.K u)^2

lemma R_expansion (y : ℝ) :
    R (17/10+y)=1777364861/3906250000+(12376707/1562500)*y+
      y^2*(194367/25000-(66383/2500)*y-6*y^2) := by
  norm_num [R,q,Inverse.q,Q0]
  ring

lemma R_positive {u : ℝ} (hu : u∈early) : 0<R u := by
  let y : ℝ := u-17/10
  have hy : y∈Icc 0 (43/200) := by
    dsimp [early] at hu
    dsimp [y]
    constructor <;> linarith [hu.1,hu.2]
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hbracket : 0<(194367/25000:ℝ)-(66383/2500)*y-6*y^2 := by
    nlinarith [hy.2]
  have hprod := mul_nonneg (sq_nonneg y) hbracket.le
  have he := R_expansion y
  have hh : 17/10+y=u := by dsimp [y]; ring
  rw [hh] at he
  nlinarith [hy.1]

def lower (y : ℝ) : ℝ :=
  347/100+(523/25)*y+y^2*(-2114/25-(40261/100)*y+
    (1295/2)*y^2-(2251/25)*y^3-(5057/100)*y^4)

def remainder (y : ℝ) : ℝ :=
  212203130934677909/61035156250000000000+
    (2285349186678467/488281250000000000)*y+
    (235719982588451/97656250000000000)*y^2+
    (31285343561/3906250000000)*y^3+
    (20299879/3906250000)*y^4+(3947/781250)*y^5+(21/2500)*y^6+8*y^7

lemma A_expansion (y : ℝ) : A (17/10+y)=lower y+remainder y := by
  simp only [A,lower,remainder,q,N,Inverse.K,Inverse.q,Inverse.N,Q0]
  ring

lemma remainder_positive {y : ℝ} (hy : 0≤y) : 0<remainder y := by
  dsimp [remainder]
  positivity

lemma lower_bracket {y : ℝ} (hy : y∈Icc 0 (43/200)) :
    -(143:ℝ)< -2114/25-(40261/100)*y+(1295/2)*y^2-
      (2251/25)*y^3-(5057/100)*y^4 := by
  have hdecrease := mul_nonneg (show 0≤(43/200:ℝ)-y by linarith [hy.2])
    (show 0≤(40261/100:ℝ)-(1295/2)*(y+43/200) by linarith [hy.2])
  have hy3 := pow_le_pow_left₀ hy.1 hy.2 3
  have hy4 := pow_le_pow_left₀ hy.1 hy.2 4
  nlinarith

lemma lower_positive {y : ℝ} (hy : y∈Icc 0 (43/200)) : 1<lower y := by
  have hbracket : 0≤ -2114/25-(40261/100)*y+(1295/2)*y^2-
      (2251/25)*y^3-(5057/100)*y^4+143 := by
    linarith [lower_bracket hy]
  have hb := mul_nonneg (sq_nonneg y) hbracket
  have hquad := mul_nonneg hy.1 (show 0≤(43/200:ℝ)-y by linarith [hy.2])
  dsimp [lower]
  nlinarith [hy.2]

lemma A_positive {u : ℝ} (hu : u∈early) : 1<A u := by
  let y : ℝ := u-17/10
  have hy : y∈Icc 0 (43/200) := by
    dsimp [early] at hu
    dsimp [y]
    constructor <;> linarith [hu.1,hu.2]
  have he := A_expansion y
  have hh : 17/10+y=u := by dsimp [y]; ring
  rw [hh] at he
  linarith [lower_positive hy,remainder_positive hy.1]

lemma N_positive {u : ℝ} (hu : u∈early) : 0<N u := by
  have hp := mul_nonneg (show 0≤u-17/10 from sub_nonneg.mpr hu.1)
    (show 0≤4*Q0-2*(u+17/10) by norm_num [Q0]; linarith [hu.2])
  norm_num [Q0] at hp
  norm_num [N,Inverse.N,Q0]
  nlinarith

lemma K_positive {u : ℝ} (hu : u∈early) : 0<Inverse.K u := by
  obtain ⟨y,hy⟩ : ∃ y : ℝ, y=u-17/10 := ⟨_,rfl⟩
  have hy0 : 0≤y := by rw [hy]; linarith [hu.1]
  have he : Inverse.K u=Inverse.K (17/10)+(804/125)*y+(153/10)*y^2+3*y^3 := by
    have hu' : u=17/10+y := by rw [hy]; ring
    rw [hu']
    simp only [Inverse.K,Q0]
    ring
  have h0 : 0<Inverse.K (17/10) := by norm_num [Inverse.K,Q0]
  have hy2 := pow_nonneg hy0 2
  have hy3 := pow_nonneg hy0 3
  rw [he]
  linarith

lemma late_full {u : ℝ} (hu : u∈late) : u∈OppositeTwo.Inverse.interval :=
  ⟨hu.1,by linarith [hu.2]⟩

def lateUpper (u : ℝ) : ℝ := (11/100)*OppositeTwo.Inverse.mass u-Inverse.K u
def lateUpperD (u : ℝ) : ℝ :=
  -(22/25)*u^3+3*((11/100)*(Q0+1)-3)*u^2+5*Q0
def lateUpperDD (u : ℝ) : ℝ :=
  -(66/25)*u^2+6*((11/100)*(Q0+1)-3)*u

lemma lateUpper_hasDerivAt (u : ℝ) : HasDerivAt lateUpper (lateUpperD u) u := by
  have hK : HasDerivAt Inverse.K (3*(3*u^2)-5*Q0) u := by
    have h := (((hasDerivAt_pow 3 u).const_mul (3:ℝ)).sub
      ((hasDerivAt_id' u).const_mul (5*Q0))).add_const (Q0*(Q0+1))
    exact h.congr_deriv (by norm_num)
  have hd := ((OppositeTwo.Inverse.mass_hasDerivAt u).const_mul (11/100:ℝ)).sub hK
  exact hd.congr_deriv (by simp only [OppositeTwo.Inverse.massD,lateUpperD]; ring)

lemma lateUpperD_hasDerivAt (u : ℝ) : HasDerivAt lateUpperD (lateUpperDD u) u := by
  have hd := (((hasDerivAt_pow 3 u).const_mul (-(22/25:ℝ))).add
    ((hasDerivAt_pow 2 u).const_mul (3*((11/100)*(Q0+1)-3)))).add_const (5*Q0)
  exact hd.congr_deriv (by norm_num [lateUpperDD]; ring)

lemma lateUpper_positive {u : ℝ} (hu : u∈late) : 0<lateUpper u := by
  exact positive_of_second_nonpos hu
    (fun t _ => lateUpper_hasDerivAt t) (fun t _ => lateUpperD_hasDerivAt t)
    (fun t ht => by
      have hp : 0≤t := by linarith [ht.1]
      norm_num [lateUpperDD,Q0]
      nlinarith [sq_nonneg t])
    (by norm_num [lateUpper,OppositeTwo.Inverse.mass,Inverse.K,
      OppositeTwo.Inverse.q,Inverse.q,Q0])
    (by norm_num [lateUpper,OppositeTwo.Inverse.mass,Inverse.K,
      OppositeTwo.Inverse.q,Inverse.q,Q0])

lemma late_K0 {u : ℝ} (hu : u∈late) :
    -(1/500:ℝ)<Inverse.K u/OppositeTwo.Inverse.mass u ∧
      Inverse.K u/OppositeTwo.Inverse.mass u<11/100 := by
  have hm := OppositeTwo.Inverse.mass_lower (late_full hu)
  refine ⟨(OppositeTwo.Inverse.K0_bounds (late_full hu)).1,?_⟩
  apply (div_lt_iff₀ (by linarith : 0<OppositeTwo.Inverse.mass u)).2
  have hh := lateUpper_positive hu
  dsimp only [lateUpper] at hh
  linarith

def derivativeNumerator (u : ℝ) : ℝ := N u+(18/125)*u^2*(q u)^2
def derivativeNumeratorD (u : ℝ) : ℝ :=
  9789/625+(577925689/195312500)*u-(663606/78125)*u^2+(288/125)*u^3
def derivativeNumeratorDD (u : ℝ) : ℝ :=
  577925689/195312500-(1327212/78125)*u+(864/125)*u^2

lemma derivativeNumerator_hasDerivAt (u : ℝ) :
    HasDerivAt derivativeNumerator (derivativeNumeratorD u) u := by
  have hfun : derivativeNumerator=fun x => -120297021/6250000+(9789/625)*x+
      (577925689/390625000)*x^2-(221202/78125)*x^3+(72/125)*x^4 := by
    funext x
    simp only [derivativeNumerator,N,Inverse.N,q,Inverse.q,Q0]
    ring
  rw [hfun]
  have hd := (((((hasDerivAt_id' u).const_mul (9789/625:ℝ)).const_add (-120297021/6250000:ℝ)).add
    ((hasDerivAt_pow 2 u).const_mul (577925689/390625000:ℝ))).sub
      ((hasDerivAt_pow 3 u).const_mul (221202/78125:ℝ))).add
        ((hasDerivAt_pow 4 u).const_mul (72/125:ℝ))
  exact hd.congr_deriv (by norm_num [derivativeNumeratorD]; ring)

lemma derivativeNumeratorD_hasDerivAt (u : ℝ) :
    HasDerivAt derivativeNumeratorD (derivativeNumeratorDD u) u := by
  have hd := ((((hasDerivAt_id' u).const_mul (577925689/195312500:ℝ)).const_add (9789/625:ℝ)).sub
    ((hasDerivAt_pow 2 u).const_mul (663606/78125:ℝ))).add
      ((hasDerivAt_pow 3 u).const_mul (288/125:ℝ))
  exact hd.congr_deriv (by norm_num [derivativeNumeratorDD]; ring)

lemma derivativeNumerator_positive {u : ℝ} (hu : u∈late) :
    0<derivativeNumerator u :=
  positive_of_second_nonpos hu
    (fun t _ => derivativeNumerator_hasDerivAt t)
    (fun t _ => derivativeNumeratorD_hasDerivAt t)
    (fun t ht => by
      have hp := mul_nonneg (show 0≤t by linarith [ht.1])
        (show 0≤171/100-t by linarith [ht.2])
      dsimp [derivativeNumeratorDD]
      nlinarith [ht.1])
    (by norm_num [derivativeNumerator,N,Inverse.N,q,Inverse.q,Q0])
    (by norm_num [derivativeNumerator,N,Inverse.N,q,Inverse.q,Q0])

lemma late_factorD {u : ℝ} (hu : u∈late) : -(18/125:ℝ)<factorD u := by
  have hd := OppositeTwo.Inverse.range_data (late_full hu)
  have hq : 0<q u := by linarith [hd.2]
  apply (lt_div_iff₀ (mul_pos (sq_pos_of_pos hd.1) (sq_pos_of_pos hq))).2
  have hh := derivativeNumerator_positive hu
  dsimp [derivativeNumerator] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactPolynomial
end
end
end

section
/-!
## Strict concavity of the actual fixed-target inverse contact

The target is kept fixed on its original circle.  The two geometric
source halves use the exact polynomials proved in the preceding module,
the source circle, and the inverse-contact norm identity.  Together they
prove strict concavity on the complete closed source interval, including
both signs of the shifted target coordinate.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactCurvature

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open Inverse (q N K brace factorD)

lemma circle_ratio {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (U b)^2+(ratio b)^2*(U b)^2=Q0 := by
  have hu := U_positive (outer_domain hb)
  have hr : ratio b*U b=W b := by
    change (W b/U b)*U b=W b
    field_simp [hu.ne']
  have hr2 : (ratio b)^2*(U b)^2=(W b)^2 := by
    calc
      _=(ratio b*U b)^2 := by ring
      _=(W b)^2 := by rw [hr]
  rw [hr2]
  exact UW_circle (outer_domain hb)

lemma late_coordinate {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b) :
    U b∈ContactPolynomial.late := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hw : 1≤W b := by dsimp [W]; linarith
  refine ⟨hu.1.le,?_⟩
  norm_num [Q0] at hc
  nlinarith

lemma early_coordinate {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2) :
    U b∈ContactPolynomial.early := by
  have hu := UW_bounds hb
  have hc := UW_circle (outer_domain hb)
  have hw : W b≤1 := by dsimp [W]; linarith
  refine ⟨?_,hu.2.1.le⟩
  norm_num [Q0] at hc
  nlinarith [hu.2.2.1]

lemma late_speed_data {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    (3739/2500:ℝ)≤q (U b) ∧ (1557/1250:ℝ)≤(ContactInverse.speed z b)^2 ∧
      (223/200:ℝ)<ContactInverse.speed z b := by
  have hd := ContactInverse.data hb hz
  have hu := late_coordinate hb hhalf
  have hq : (3739/2500:ℝ)≤q (U b) := by
    norm_num [q,Inverse.q,Q0]
    linarith [hu.2]
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hv2 : (1557/1250:ℝ)≤(ContactInverse.speed z b)^2 := by
    linarith [hd.2.2.2.2.2]
  exact ⟨hq,hv2,by nlinarith [hd.2.2.2.2.1]⟩

lemma late_brace {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    |brace (U b) (ratio b) (ContactInverse.speed z b)|<(7/50:ℝ) := by
  have hd := ContactInverse.data hb hz
  have hh := late_speed_data hb hhalf hz
  have hq : 0<q (U b) := by linarith [hh.1]
  have hv := hd.2.2.2.2.1
  have hr := outer_ratio_bounds hb
  have hr2 : (ratio b)^2≤1 := by nlinarith [hr.1,hr.2.1]
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hnum := mul_le_mul hr2 hz2 (sq_nonneg z) (by norm_num : (0:ℝ)≤1)
  have hden := mul_le_mul hh.1 hh.2.1 (by norm_num : (0:ℝ)≤1557/1250) hq.le
  have hcor : (ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2)<69/500 := by
    apply (div_lt_iff₀ (mul_pos hq (sq_pos_of_pos hv))).2
    linarith
  have hcor0 : 0≤(ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos hq (sq_pos_of_pos hv)).le
  have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
    (circle_ratio hb) hd.2.2.2.2.2
  have hK := ContactPolynomial.late_K0 (late_coordinate hb hhalf)
  simp only [OppositeTwo.Inverse.mass,OppositeTwo.Inverse.q] at hK
  rw [abs_lt]
  constructor <;> linarith

lemma late_inverse_upper {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : 1/2≤b)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)<187/1000 := by
  have hd := ContactInverse.data hb hz
  have hh := late_speed_data hb hhalf hz
  have hr := outer_ratio_bounds hb
  have hr0 : 0<ratio b := by linarith [hr.1]
  have hf := mul_lt_mul_of_pos_left
    (ContactPolynomial.late_factorD (late_coordinate hb hhalf)) hr0
  have hfirst : -ratio b*factorD (U b)<18/125 := by nlinarith [hr.2.1]
  have hzabs : |z|≤(1/2:ℝ) := abs_le.mpr ⟨hz.1,by linarith [hz.2]⟩
  have hbabs := late_brace hb hhalf hz
  have hprod : |z*brace (U b) (ratio b) (ContactInverse.speed z b)|<7/100 := by
    rw [abs_mul]
    have hle := mul_le_mul_of_nonneg_right hzabs
      (abs_nonneg (brace (U b) (ratio b) (ContactInverse.speed z b)))
    linarith
  have hq : 0<q (U b) := by linarith [hh.1]
  have hden := mul_lt_mul' hh.1 hh.2.2 (by norm_num : (0:ℝ)≤223/200) hq
  have hmiddle : z/(q (U b)*ContactInverse.speed z b)*
      brace (U b) (ratio b) (ContactInverse.speed z b)<43/1000 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (mul_pos hq hd.2.2.2.2.1)).2
    have hp := (le_abs_self (z*brace (U b) (ratio b) (ContactInverse.speed z b))).trans_lt hprod
    linarith
  dsimp only [PJCritical.inverseTarget,PJCritical.heightFactorD]
  linarith

lemma source_half_second : (11/50:ℝ)<PLabel.d2 (1/2) := by
  have hb : (1/2:ℝ)∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem (by constructor <;> norm_num)
  have hh := PLabel.second_chart_reference (outer_domain hb)
    (l := (1707512811079/1000000000000:ℝ))
    (u := (42687820277/25000000000:ℝ))
    (dlo := (11/50:ℝ)) (dhi := (23/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PLabel,W,Q0]) (by norm_num [PLabel,W,Q0])
  exact hh.1

lemma R_identity (u : ℝ) : ContactPolynomial.R u=
    Inverse.K u*(q u-1/4)-(1/4)*u*(Q0-u^2) := by
  simp only [ContactPolynomial.R,Inverse.K,q,Inverse.q]
  ring

lemma early_brace_positive {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    0<brace (U b) (ratio b) (ContactInverse.speed z b) := by
  have hd := ContactInverse.data hb hz
  have hu := early_coordinate hb hhalf
  have hq : 0<q (U b) := by linarith [Inverse.actual_q_positive hb]
  have hv := hd.2.2.2.2.1
  have hc := UW_circle (outer_domain hb)
  have hcircle : Q0-(U b)^2=(W b)^2 := by linarith
  have hr2 : (ratio b)^2*(U b)^2=(W b)^2 := by
    linarith [circle_ratio hb]
  have hK := ContactPolynomial.K_positive hu
  have hR := ContactPolynomial.R_positive hu
  have hz2 : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hproduct := mul_nonneg (show 0≤(1/4:ℝ)-z^2 by linarith)
    (add_pos hK (mul_pos hd.1 (pow_pos hd.2.1 2))).le
  have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
    (circle_ratio hb) hd.2.2.2.2.2
  have hmass : brace (U b) (ratio b) (ContactInverse.speed z b)*
      ((U b)^3*q (U b)*(ContactInverse.speed z b)^2)=
      Inverse.K (U b)*(q (U b)-z^2)-U b*(W b)^2*z^2 := by
    have hU0 : U b≠0 := hd.1.ne'
    have e1 : Inverse.K (U b)/((U b)^3*q (U b))*((U b)^3*q (U b)*(ContactInverse.speed z b)^2)=
        Inverse.K (U b)*(ContactInverse.speed z b)^2 := by
      field_simp
    have e2 : (ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2)*
        ((U b)^3*q (U b)*(ContactInverse.speed z b)^2)=(ratio b)^2*z^2*(U b)^3 := by
      field_simp
    rw [he,sub_mul,e1,e2]
    linear_combination Inverse.K (U b)*hd.2.2.2.2.2-(U b*z^2)*hr2
  have hRid := R_identity (U b)
  rw [hcircle] at hRid
  have hmasspos : 0<(U b)^3*q (U b)*(ContactInverse.speed z b)^2 :=
    mul_pos (mul_pos (pow_pos hd.1 3) hq) (pow_pos hv 2)
  by_contra hbad
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hbad) hmasspos.le
  linarith

lemma early_inverse_negative {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hhalf : b≤1/2)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)<0 := by
  have hd := ContactInverse.data hb hz
  have hu := early_coordinate hb hhalf
  have hq : 0<q (U b) := by linarith [Inverse.actual_q_positive hb]
  have hv := hd.2.2.2.2.1
  have hN := ContactPolynomial.N_positive hu
  have hK := ContactPolynomial.K_positive hu
  have hr : 0<ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hbrace := early_brace_positive hb hhalf hz
  have hfactor : 0<factorD (U b) := by
    exact div_pos hN (mul_pos (sq_pos_of_pos hd.1) (sq_pos_of_pos hq))
  by_cases hz0 : 0≤z
  · have hz2 : z^2≤(4/25:ℝ) := by nlinarith [hz.2]
    have hspeed : 0≤(ContactInverse.speed z b)^2-(q (U b)-4/25) := by
      linarith [hd.2.2.2.2.2]
    have hc := UW_circle (outer_domain hb)
    have hcircle : Q0-(U b)^2=(W b)^2 := by linarith
    have hreserve := ContactPolynomial.A_positive hu
    have hnonneg := mul_nonneg
      (mul_nonneg (sq_nonneg (W b)) (sq_nonneg (N (U b)))) hspeed
    have hsquares : (W b*N (U b)*ContactInverse.speed z b)^2-
        ((2/5)*Inverse.K (U b))^2=ContactPolynomial.A (U b)+
          (W b)^2*(N (U b))^2*((ContactInverse.speed z b)^2-(q (U b)-4/25)) := by
      simp only [ContactPolynomial.A]
      rw [hcircle]
      ring
    have hleft : 0<W b*N (U b)*ContactInverse.speed z b := mul_pos (mul_pos hd.2.1 hN) hv
    have hright : 0≤(2/5:ℝ)*Inverse.K (U b) := by linarith
    have hgap : (2/5)*Inverse.K (U b)<W b*N (U b)*ContactInverse.speed z b := by
      by_contra hcon
      have hsq := pow_le_pow_left₀ hleft.le (le_of_not_gt hcon) 2
      linarith
    have htarget := mul_le_mul_of_nonneg_right hz.2 hK.le
    have hnum : -W b*N (U b)*ContactInverse.speed z b+z*Inverse.K (U b)<0 := by
      linarith
    have he := Inverse.brace_identity hd.1.ne' hq.ne' hv.ne'
      (circle_ratio hb) hd.2.2.2.2.2
    have hcor : 0≤(ratio b)^2*z^2/(q (U b)*(ContactInverse.speed z b)^2) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos hq (sq_pos_of_pos hv)).le
    have hupper : brace (U b) (ratio b) (ContactInverse.speed z b)≤
        Inverse.K (U b)/((U b)^3*q (U b)) := by linarith
    have hweight : 0≤z/(q (U b)*ContactInverse.speed z b) :=
      div_nonneg hz0 (mul_pos hq hv).le
    have hle := mul_le_mul_of_nonneg_left hupper hweight
    have hsum : -ratio b*factorD (U b)+
        z/(q (U b)*ContactInverse.speed z b)*(Inverse.K (U b)/((U b)^3*q (U b)))=
        (-W b*N (U b)*ContactInverse.speed z b+z*Inverse.K (U b))/
          ((U b)^3*(q (U b))^2*ContactInverse.speed z b) := by
      have hratio : ratio b=W b/U b := rfl
      rw [hratio]
      simp only [Inverse.factorD]
      field_simp
    have hdiv : (-W b*N (U b)*ContactInverse.speed z b+z*Inverse.K (U b))/
        ((U b)^3*(q (U b))^2*ContactInverse.speed z b)<0 :=
      div_neg_of_neg_of_pos hnum (mul_pos (mul_pos (pow_pos hd.1 3) (pow_pos hq 2)) hv)
    dsimp only [PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith
  · have hweight : z/(q (U b)*ContactInverse.speed z b)≤0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz0) (mul_pos hq hv).le
    have hmiddle := mul_nonpos_of_nonpos_of_nonneg hweight hbrace.le
    have hfirst := mul_pos hr hfactor
    dsimp only [PJCritical.inverseTarget,PJCritical.heightFactorD]
    linarith

theorem inverse_minus_source_second {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)-PLabel.d2 b<0 := by
  rcases le_total b (1/2) with hhalf|hhalf
  · linarith [early_inverse_negative hb hhalf hz,P_second_positive hb]
  · have hh := P_second_monotone
      (show (1/2:ℝ)∈Icc 0 outerDiagonal from
        Asymmetric.rational_outer_mem (by constructor <;> norm_num)) hb hhalf
    linarith [late_inverse_upper hb hhalf hz,source_half_second]

def fixedCost (z b : ℝ) : ℝ := Real.pi/2-ContactInverse.angle z b-P b+T (z+1/2)
def fixedFirst (z b : ℝ) : ℝ := -ContactInverse.first z b-PLabel.d1 b
def fixedSecond (z b : ℝ) : ℝ :=
  PJCritical.inverseTarget (U b) (ratio b) z (ContactInverse.speed z b)-PLabel.d2 b

lemma fixedCost_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (fixedCost z) (fixedFirst z b) b := by
  have hd := (((ContactInverse.angle_hasDerivAt hb hz).const_sub (Real.pi/2)).sub
    (PLabel.outer_hasDerivAt (outer_domain hb))).add_const (T (z+1/2))
  exact hd.congr_deriv (by simp only [fixedFirst])

lemma fixedFirst_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (fixedFirst z) (fixedSecond z b) b := by
  have hd := (ContactInverse.first_hasDerivAt hb hz).neg.sub
    (PLabel.d1_hasDerivAt (outer_domain hb))
  exact hd.congr_deriv (by simp only [fixedSecond,ContactInverse.second]; ring)

theorem fixedCost_concave {z : ℝ} (hz : z∈Icc (-(1/2)) (2/5)) :
    ConcaveOn ℝ (Icc 0 outerDiagonal) (fixedCost z) :=
  concave_of_deriv2
    (fun _ hb => fixedCost_hasDerivAt hb hz)
    (fun _ hb => fixedFirst_hasDerivAt hb hz)
    (fun _ hb => (inverse_minus_source_second hb hz).le)

end SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactCurvature
end
end
end

section
/-!
## Boundary reduction for the lower target-secondary owner

Every original weak separator first gives a contact on the same circle, with no larger cost
(`original_lower_boundary`). At a fixed target coordinate, intermediate-value contacts give both
ends of the feasible source interval. Strict contact concavity then selects one of the four
boundary types (`contact_boundary`). The axial and aligned types are discharged here
(`axial_contact_lower`, `aligned_contact_lower`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

structure BoundaryContact (B : ℝ) where
  b : ℝ
  x : ℝ
  source : b∈Icc 0 outerDiagonal
  angle : x∈Icc 0 (7/10)
  contact : TargetContact.B b x=B
  boundary : b=0 ∨ b=outerDiagonal ∨ x=0 ∨ x=7/10

lemma target_shift_mem {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    B-1/2∈Icc (-(1/2)) (2/5) :=
  ⟨by linarith [hB.1],by linarith [hB.2,outer_endpoint_bounds.2.2.2]⟩

lemma fixed_contact_value {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ContactCurvature.fixedCost (B-1/2) b=value b B (Real.pi/2-x) := by
  have hd : TargetContact.Domain b x := ⟨hb,hx,by rw [hc]; exact hB⟩
  have he := ContactInverse.original_angle hd
  rw [hc] at he
  dsimp [ContactCurvature.fixedCost,value]
  rw [he,show B-1/2+1/2=B by ring]

lemma left_boundary_contact {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, w.b≤b := by
  by_cases hleft : B≤TargetContact.B 0 (7/10)
  · have hstart : TargetContact.B 0 0≤B := by
      rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_zero]
      linarith [hB.1,outer_endpoint_bounds.1]
    have hcont : Continuous (TargetContact.B 0) :=
      continuous_iff_continuousAt.2 fun t => (TargetContact.B_angle_hasDerivAt 0 t).continuousAt
    obtain ⟨t,ht,hcontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn ⟨hstart,hleft⟩
    exact ⟨⟨0,t,outer_zero_mem,ht,hcontact,Or.inl rfl⟩,hb.1⟩
  · have hcap := TargetContact.B_angle_monotone hb hx
      (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
    rw [hc] at hcap
    have hcont : Continuous (fun t => TargetContact.B t (7/10)) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨l,hl,hcontact⟩ := intermediate_value_Icc hb.1 hcont.continuousOn
      (show B∈Icc (TargetContact.B 0 (7/10)) (TargetContact.B b (7/10)) from
        ⟨by linarith,hcap⟩)
    exact ⟨⟨l,7/10,⟨hl.1,hl.2.trans hb.2⟩,by norm_num,hcontact,
      Or.inr (Or.inr (Or.inr rfl))⟩,hl.2⟩

lemma right_boundary_contact {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (_hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, b≤w.b := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  by_cases hright : TargetContact.B outerDiagonal 0≤B
  · have hend := TargetContact.B_source_monotone hx hb hd hb.2
    dsimp only at hend
    rw [hc] at hend
    have hcont : Continuous (TargetContact.B outerDiagonal) :=
      continuous_iff_continuousAt.2 fun t =>
        (TargetContact.B_angle_hasDerivAt outerDiagonal t).continuousAt
    obtain ⟨t,ht,hcontact⟩ := intermediate_value_Icc hx.1 hcont.continuousOn
      (show B∈Icc (TargetContact.B outerDiagonal 0) (TargetContact.B outerDiagonal x) from
        ⟨hright,hend⟩)
    exact ⟨⟨outerDiagonal,t,hd,⟨ht.1,ht.2.trans hx.2⟩,hcontact,
      Or.inr (Or.inl rfl)⟩,hb.2⟩
  · have hstart := TargetContact.B_angle_monotone hb (by norm_num) hx hx.1
    rw [hc] at hstart
    have hcont : Continuous (fun t => TargetContact.B t 0) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨r,hr,hcontact⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show B∈Icc (TargetContact.B b 0) (TargetContact.B outerDiagonal 0) from
        ⟨hstart,by linarith⟩)
    exact ⟨⟨r,0,⟨hb.1.trans hr.1,hr.2⟩,by norm_num,hcontact,
      Or.inr (Or.inr (Or.inl rfl))⟩,hr.1⟩

theorem contact_boundary {b B x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hB : B∈Icc 0 outerDiagonal)
    (hc : TargetContact.B b x=B) :
    ∃ w : BoundaryContact B, value w.b B (Real.pi/2-w.x)≤value b B (Real.pi/2-x) := by
  obtain ⟨l,hl⟩ := left_boundary_contact hb hx hB hc
  obtain ⟨r,hr⟩ := right_boundary_contact hb hx hB hc
  have hmin := (ContactCurvature.fixedCost_concave (target_shift_mem hB)).min_le_of_mem_Icc
    l.source r.source ⟨hl,hr⟩
  rw [fixed_contact_value l.source l.angle hB l.contact,
    fixed_contact_value r.source r.angle hB r.contact,
    fixed_contact_value hb hx hB hc] at hmin
  rcases le_total (value l.b B (Real.pi/2-l.x)) (value r.b B (Real.pi/2-r.x)) with h|h
  · exact ⟨l,by simpa only [min_eq_left h] using hmin⟩
  · exact ⟨r,by simpa only [min_eq_right h] using hmin⟩

lemma original_lower_contact {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ b' B', b'∈Icc 0 outerDiagonal ∧ B'∈Icc 0 outerDiagonal ∧
      TargetContact.B b' x=B' ∧ value b' B' (Real.pi/2-x)≤value b B (Real.pi/2-x) := by
  have hb := source_mem hs
  have hB := source_mem ht
  have hcut := lower_target_cut hs hx hm
  by_cases hpos : 0≤TargetContact.B b x
  · have hc : TargetContact.B b x∈Icc 0 outerDiagonal := ⟨hpos,hcut.trans hB.2⟩
    have hT := T_monotone hc hB hcut
    refine ⟨b,TargetContact.B b x,hb,hc,rfl,?_⟩
    dsimp [value]
    linarith
  · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
    have hdiag := TargetContact.B_angle_monotone hd (by norm_num) hx hx.1
    rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal] at hdiag
    have hcont : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨b',hb',he⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (TargetContact.B b x) (TargetContact.B outerDiagonal x) by
        constructor <;> linarith [outer_endpoint_bounds.2.2.2])
    have hbnew : b'∈Icc 0 outerDiagonal := ⟨hb.1.trans hb'.1,hb'.2⟩
    have hP := P_monotone hb hbnew hb'.1
    have hT := T_monotone outer_zero_mem hB hB.1
    refine ⟨b',0,hbnew,outer_zero_mem,he,?_⟩
    dsimp [value]
    linarith

theorem original_lower_boundary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ B', B'∈Icc 0 outerDiagonal ∧ ∃ w : BoundaryContact B',
      value w.b B' (Real.pi/2-w.x)≤value b B (Real.pi/2-x) := by
  obtain ⟨b',B',hb',hB',hc,hstep⟩ := original_lower_contact hs ht hx hm
  obtain ⟨w,hw⟩ := contact_boundary hb' hx hB' hc
  exact ⟨B',hB',w,hw.trans hstep⟩

lemma axial_reference_target : (37/500:ℝ)<TargetContact.B 0 (13/20) := by
  have hs := sin_lower_seven (show (0:ℝ)≤13/20 by norm_num)
  have hc := cos_le_cos8 (show (0:ℝ)≤13/20 by norm_num)
  have hcos0 : 0≤Real.cos (13/20) := by
    linarith [(positive_trig (show (13/20:ℝ)∈Icc 0 (7/10) by norm_num)).1]
  have hmul := mul_le_mul
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1]) hc hcos0
    (by norm_num : (0:ℝ)≤183/200)
  norm_num [cos8] at hs hc hmul
  dsimp [TargetContact.B]
  rw [ShortOuterOne.SameContact.arc_zero]
  nlinarith

theorem axial_contact_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B 0 x=B) :
    (9/10:ℝ)<value 0 B (Real.pi/2-x) := by
  by_cases hearly : x≤13/20
  · have hT := T_lower hB
    dsimp [value]
    rw [P_zero]
    linarith [pi_hand_enclosure.1]
  · have hmono := TargetContact.B_angle_monotone outer_zero_mem
      (show (13/20:ℝ)∈Icc 0 (7/10) by norm_num) hx (by linarith)
    rw [hc] at hmono
    have hT := T_increment_lower outer_zero_mem hB hB.1
    rw [T_zero] at hT
    dsimp [value]
    rw [P_zero]
    linarith [axial_reference_target,pi_hand_enclosure.1,hx.2]

theorem aligned_contact_lower {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b 0=B) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2) := by
  rw [TargetContact.B_zero] at hc
  exact original_aligned (ShortOuterOne.SameContact.arc_state hb)
    (ShortOuterOne.SameContact.arc_state hB) (by linarith)

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_labels : (21/200:ℝ)<PLabel.d2 0 ∧
    TLabel.d1 (height 0)<9173/10000 ∧ TLabel.d2 (height 0)< -113/100 := by
  have hs := SourceReference.source outer_zero_mem zero_radical (by norm_num)
  have ht := FixedReference.target (target_mem zero_domain) zero_cage.1 zero_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith⟩

lemma two_labels : (289/2000:ℝ)<PLabel.d2 (1/5) ∧ PLabel.d3 (1/5)<533/2500 ∧
    (7451/10000:ℝ)<TLabel.d1 (height (1/5)) ∧ TLabel.d1 (height (1/5))<1863/2500 ∧
    (-7981/10000:ℝ)<TLabel.d2 (height (1/5)) ∧ TLabel.d2 (height (1/5))< -399/500 ∧
    (509/250:ℝ)<TLabel.d3 (height (1/5)) := by
  have hs := SourceReference.source two_mem two_radical (by norm_num)
  have ht := FixedReference.target (target_mem two_domain) two_cage.1 two_target_radical
    (by norm_num) (by norm_num)
  have hp3 := SourceReference.source_third_upper two_mem
    (ul := (185083764820148/100000000000000:ℝ)) (upper := (533/2500:ℝ))
    (by norm_num) two_radical.1 (by norm_num) (by norm_num [Q0])
  have hthree : (3/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hUthree := shifted_chart_reference (outer_domain hthree)
    (l := (9049/5000:ℝ)) (u := (18099/10000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have ht3 := SourceReference.target_third_lower hthree hUthree.2.le
    (lower := (509/250:ℝ)) (by norm_num) (by norm_num [Q0])
  have hm := T_third_monotone hthree (target_mem two_domain)
    (by linarith [two_cage.1.1])
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,hp3,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma six_labels : P (3/5)<6443/12500 ∧ (87629/100000:ℝ)<PLabel.d1 (3/5) ∧
    PLabel.d2 (3/5)<6337/25000 ∧ (6918/12500:ℝ)<T (height (3/5)) ∧
    (627189/1000000:ℝ)<TLabel.d1 (height (3/5)) ∧
    TLabel.d1 (height (3/5))<784/1250 ∧
    (18027/50000:ℝ)<TLabel.d2 (height (3/5)) := by
  have hs := SourceReference.source six_mem six_radical (by norm_num)
  have ht := FixedReference.target (target_mem six_domain) six_cage.1 six_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma reference_labels : P (14473/20000)<7823141206/12500000000 ∧
    PLabel.d1 (14473/20000)∈Icc (91065969/100000000) (91065971/100000000) ∧
    (326420021/500000000:ℝ)<T (height (14473/20000)) ∧
    TLabel.d1 (height (14473/20000))∈Icc (7308367/10000000) (9135459/12500000) := by
  have hs := SourceReference.source reference_mem reference_radical (by norm_num)
  have ht := FixedReference.target (target_mem reference_domain) reference_cage_fine.1
    reference_target_radical (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,⟨by linarith,by linarith⟩,by linarith,⟨by linarith,by linarith⟩⟩

lemma zero_second : second 0<(-51/100:ℝ) := by
  have hk := k_bounds outer_zero_mem
  have hk0 : 0<k 0 := by linarith [hk.1]
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8439/10000) zero_cage.2.1.le 2
  have hnegative := mul_lt_mul_of_pos_right zero_labels.2.2 (pow_pos hk0 2)
  have hpositive := mul_lt_mul zero_labels.2.1 zero_cage.2.2.le hk.2.1
    (by norm_num : (0:ℝ)≤9173/10000)
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [zero_labels.1]

lemma two_second : second (1/5)<(-12/25:ℝ) := by
  have hk := k_bounds two_mem
  have hk0 : 0<k (1/5) := by linarith [hk.1]
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4667/5000) two_cage.2.1.le 2
  have hnegative := mul_lt_mul_of_pos_right two_labels.2.2.2.2.2.1 (pow_pos hk0 2)
  have hpositive := mul_lt_mul two_labels.2.2.2.1 two_cage.2.2.2.1.le hk.2.1
    (by norm_num : (0:ℝ)≤1863/2500)
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [two_labels.1]

lemma two_third : (3/5:ℝ)<third (1/5) := by
  have hk := k_bounds two_mem
  have hk0 : 0<k (1/5) := by linarith [hk.1]
  have hk3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4667/5000) two_cage.2.1.le 3
  have hlead := mul_lt_mul two_labels.2.2.2.2.2.2 hk3
    (by norm_num : (0:ℝ)<(4667/5000)^3)
    (by linarith [two_labels.2.2.2.2.2.2] : 0≤TLabel.d3 (height (1/5)))
  have hkk1 := mul_lt_mul two_cage.2.2.1 two_cage.2.2.2.1.le hk.2.1
    (by norm_num : (0:ℝ)≤1867/2000)
  have hprod := mul_pos (show 0<TLabel.d2 (height (1/5))+7981/10000 by
    linarith [two_labels.2.2.2.2.1]) (mul_pos hk0 hk.2.1)
  have hlast := mul_lt_mul two_labels.2.2.1 two_cage.2.2.2.2.le
    (by norm_num : (0:ℝ)<579/2000)
    (by linarith [two_labels.2.2.1] : 0≤TLabel.d1 (height (1/5)))
  dsimp only [third]
  norm_num at hlead hkk1 hlast
  nlinarith [two_labels.2.1]

lemma zero_value : (9/10:ℝ)<cost 0 :=
  axial_contact_lower (target_mem zero_domain) (by norm_num) rfl

lemma two_value : (9/10:ℝ)<cost (1/5) := by
  have hs := SourceReference.source two_mem two_radical (by norm_num)
  have ht := FixedReference.target (target_mem two_domain) two_cage.1 two_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1]

lemma six_value : (453/500:ℝ)<cost (3/5) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,six_labels.1,six_labels.2.2.2.1]

lemma six_first : first (3/5)<0 := by
  have hk := k_bounds six_mem
  have hh := mul_lt_mul six_labels.2.2.2.2.2.1 six_cage.2.2.1.le
    (by linarith [hk.1] : 0<k (3/5)) (by norm_num : (0:ℝ)≤784/1250)
  dsimp only [first]
  norm_num at hh
  linarith [six_labels.2.1]

lemma six_second : (13/20:ℝ)<second (3/5) := by
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤577851/500000) six_cage.2.1.le 2
  have hlead := mul_lt_mul six_labels.2.2.2.2.2.2 hk2
    (by norm_num : (0:ℝ)<(577851/500000)^2)
    (by linarith [six_labels.2.2.2.2.2.2] : 0≤TLabel.d2 (height (3/5)))
  have hlast := mul_lt_mul six_labels.2.2.2.2.1 six_cage.2.2.2.le
    (by norm_num : (0:ℝ)<672937/1000000)
    (by linarith [six_labels.2.2.2.2.1] : 0≤TLabel.d1 (height (3/5)))
  dsimp only [second]
  norm_num at hlead hlast
  linarith [six_labels.2.2.1]

lemma reference_value : (89778507/100000000:ℝ)<cost (14473/20000) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,reference_labels.1,reference_labels.2.2.1]

lemma reference_first : |first (14473/20000)|<(1/1000000:ℝ) := by
  have ht := reference_labels.2.2.2
  have hk := reference_cage_fine.2
  have hlo := mul_le_mul ht.1 hk.1 (by norm_num : (0:ℝ)≤124605027/100000000)
    (by linarith [ht.1] : 0≤TLabel.d1 (height (14473/20000)))
  have hhi := mul_le_mul ht.2 hk.2 (by linarith [hk.1] : 0≤k (14473/20000))
    (by norm_num : (0:ℝ)≤9135459/12500000)
  rw [abs_lt]
  dsimp [first]
  norm_num at hlo hhi
  constructor <;> linarith [reference_labels.2.1.1,reference_labels.2.1.2]

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end
