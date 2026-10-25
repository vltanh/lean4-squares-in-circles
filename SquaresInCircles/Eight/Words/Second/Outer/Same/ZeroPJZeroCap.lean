module

public import SquaresInCircles.Eight.Words.Second.Outer.JBounds
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKReference
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJBoundaryReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJCriticalBounds

/-!
# Eight squares: the target-zero and upper-angle P/J boundaries

The target-zero boundary uses a single circle estimate (`zero_boundary_lower`), and the
upper-angle boundary uses the exact positive curvature identity (`cap_curvature`) and its one
reference point (`cap_boundary_lower`).
-/

section
/-!
## A single endpoint-forcing direction for the L/K contact

If the angular derivative can fail to be
positive, the original source lies above .755.  Its exact projection
ratio then exceeds the target label slope on the whole target arc.
Every nonpositive angular derivative therefore has a strictly positive
target derivative.  The split at .2 compares two analytic bounds on
the same circle; no box or sampled contact is a hypothesis.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma first_left : LLabel.d1 (293/1000)<(817/1000:ℝ) := by
  have hh := LLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (293/1000:ℝ)∈Icc 0 (899/1000))))
    (l := (18129398776/10000000000:ℝ)) (u := (18129398777/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (817/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.2

lemma first_right : LLabel.d1 (151/200)<(817/1000:ℝ) := by
  have hh := LLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (151/200:ℝ)∈Icc 0 (899/1000))))
    (l := (15298937871/10000000000:ℝ)) (u := (15298937872/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (817/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.2

lemma second_right : (167/100:ℝ)<LLabel.d2 (151/200) := by
  have hh := LLabel.second_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (151/200:ℝ)∈Icc 0 (899/1000))))
    (l := (15298937871/10000000000:ℝ)) (u := (15298937872/10000000000:ℝ))
    (dlo := (167/100:ℝ)) (dhi := (2:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.1

lemma target_fifth_first : KLabel.d1 (1/5)<(869/1000:ℝ) := by
  have hh := KLabel.first_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))))
    (l := (18508376482/10000000000:ℝ)) (u := (18508376483/10000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (869/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma first_middle {y : ℝ} (hy : y∈Icc (293/1000:ℝ) (151/200)) :
    LLabel.d1 y<(817/1000:ℝ) := by
  have hdom : Icc (293/1000:ℝ) (151/200)⊆Icc 0 outerDiagonal := by
    intro z hz
    exact ⟨by linarith [hz.1],by linarith [hz.2,fine_outer_endpoint_bounds.2]⟩
  have hc : ConcaveOn ℝ (Icc (293/1000:ℝ) (151/200)) (fun y => -LLabel.d1 y) :=
    concave_of_deriv2
      (fun z hz => (LLabel.d1_hasDerivAt (outer_domain (hdom hz))).neg)
      (fun z hz => (LLabel.d2_hasDerivAt (outer_domain (hdom hz))).neg)
      (fun z hz => neg_nonpos.mpr (L_third_positive (hdom hz)).le)
  have hh := concave_gt_of_endpoints hc hy
    (show -(817/1000:ℝ)< -LLabel.d1 (293/1000) by linarith [first_left])
    (show -(817/1000:ℝ)< -LLabel.d1 (151/200) by linarith [first_right])
  linarith

lemma angular_nonpos_large {B x : ℝ} (hd : Domain B x)
    (hangle : angleFirst LLabel B x≤0) : (151/200:ℝ)<b B x := by
  by_contra! hsmall
  have hp := first_middle ⟨(b_lower hd.1 hd.2.1).le,hsmall⟩
  have hv := v_upper hd.1 hd.2.1
  have hprod := mul_lt_mul hp hv.le (v_positive hd.1 hd.2.1)
    (by norm_num : (0:ℝ)≤817/1000)
  dsimp [angleFirst] at hangle
  norm_num at hprod
  linarith

lemma factor_lower {u : ℝ} (hu : 0<u) (hq : 0<NegativeTwo.Inverse.q u) :
    (21/25:ℝ)<NegativeTwo.Inverse.factor u := by
  apply (lt_div_iff₀ (mul_pos hu hq)).2
  have he : Q0-u-(21/25)*u*NegativeTwo.Inverse.q u=
      (42/25)*(u-320569/210000)^2+20016239/26250000000 := by
    norm_num [Q0,NegativeTwo.Inverse.q]
    ring
  nlinarith [sq_nonneg (u-320569/210000)]

lemma projection_early {B x : ℝ} (hd : Domain B x) (hB : B≤1/5)
    (hb : (151/200:ℝ)<b B x) : (116/125:ℝ)<k B x/v B x := by
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hv := v_positive hd.1 hd.2.1
  have hU : (37/20:ℝ)<U B := by
    have hc := UW_circle (outer_domain hd.1)
    have hw : (W B)^2≤(7/10:ℝ)^2 :=
      pow_le_pow_left₀ (by dsimp [W]; linarith [hd.1.1]) (by dsimp [W]; linarith) 2
    norm_num [Q0] at hc
    exact lt_of_pow_lt_pow_left₀ 2 hu.le (by linarith)
  have hUhi := (UW_bounds hd.1).2.1
  have hqhi : NegativeTwo.Inverse.q (U B)<(3039/2500:ℝ) := by
    norm_num [NegativeTwo.Inverse.q,Q0]
    linarith
  have hden : U B*NegativeTwo.Inverse.q (U B)≤(37/20)*(3039/2500) := by
    have hh := mul_nonneg (show 0≤U B-37/20 by linarith)
      (show 0≤2*U B+37/10-(Q0+1) by norm_num [Q0]; linarith)
    norm_num [NegativeTwo.Inverse.q,Q0] at hh ⊢
    linarith
  have hfirst : (889/1000:ℝ)<NegativeTwo.Inverse.factor (U B) := by
    apply (lt_div_iff₀ (mul_pos hu hq)).2
    norm_num [Q0] at hden ⊢
    linarith
  have hvhi : v B x<(1103/1000:ℝ) := by
    have hn := norm_identity hd.1 x
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith [sq_nonneg (b B x-1/2)])
  have hden2 := mul_lt_mul
    (mul_lt_mul hUhi hqhi.le hq (by norm_num : (0:ℝ)≤383/200)) hvhi.le hv
    (by norm_num : (0:ℝ)≤(383/200)*(3039/2500))
  have hnum : (1/2)*(51/200)<W B*(b B x-1/2) := by
    have hh := mul_nonneg (show 0≤W B-1/2 by dsimp [W]; linarith [hd.1.1])
      (show 0≤b B x-1/2 by linarith)
    linarith
  have hsecond : (39/1000:ℝ)<W B*(b B x-1/2)/
      (U B*NegativeTwo.Inverse.q (U B)*v B x) := by
    apply (lt_div_iff₀ (mul_pos (mul_pos hu hq) hv)).2
    linarith
  rw [projection_identity hd.1 hd.2.1]
  linarith

lemma projection_late {B x : ℝ} (hd : Domain B x) (hB : 1/5≤B)
    (hb : (151/200:ℝ)<b B x) : (869/1000:ℝ)<k B x/v B x := by
  have hu := U_positive (outer_domain hd.1)
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hd.1]
  have hv := v_positive hd.1 hd.2.1
  have hUhi := (UW_bounds hd.1).2.1
  have hqhi : NegativeTwo.Inverse.q (U B)<(1059/500:ℝ) := by
    have hu := (UW_bounds hd.1).1
    norm_num [NegativeTwo.Inverse.q,Q0]
    linarith
  have hvhi := v_upper hd.1 hd.2.1
  have hden := mul_lt_mul
    (mul_lt_mul hUhi hqhi.le hq (by norm_num : (0:ℝ)≤383/200)) hvhi.le hv
    (by norm_num : (0:ℝ)≤(383/200)*(1059/500))
  have hnum : (7/10)*(51/200)<W B*(b B x-1/2) := by
    have hh := mul_nonneg (show 0≤W B-7/10 by dsimp [W]; linarith)
      (show 0≤b B x-1/2 by linarith)
    linarith
  have hsecond : (29/1000:ℝ)<W B*(b B x-1/2)/
      (U B*NegativeTwo.Inverse.q (U B)*v B x) := by
    apply (lt_div_iff₀ (mul_pos (mul_pos hu hq) hv)).2
    linarith
  rw [projection_identity hd.1 hd.2.1]
  linarith [factor_lower hu hq]

theorem angular_nonpos_target_pos {B x : ℝ} (hd : Domain B x)
    (hangle : angleFirst LLabel B x≤0) : 0<targetFirst LLabel KLabel B x := by
  have hb := angular_nonpos_large hd hangle
  have hv := v_positive hd.1 hd.2.1
  have hk := k_positive hd.1 hd.2.1
  have hpaid : k B x/v B x≤LLabel.d1 (b B x)*k B x := by
    apply (div_le_iff₀ hv).2
    have hh := mul_nonneg hk.le (show 0≤LLabel.d1 (b B x)*v B x-1 by
      dsimp [angleFirst] at hangle; linarith)
    nlinarith
  have hgap : KLabel.d1 B<k B x/v B x := by
    rcases le_total B (1/5) with he | hl
    · exact (K_first_bounds hd.1).2.trans (projection_early hd he hb)
    · have hf := K_first_antitone (Asymmetric.rational_outer_mem
        (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))) hd.1 hl
      exact (hf.trans_lt target_fifth_first).trans (projection_late hd hl hb)
  dsimp [targetFirst]
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.LK
end
end
end

section
/-!
## The uniform negative P/J Hessian direction

One estimate on the whole domain: the second derivative of the inverse contact is below `-.05`
on the critical coordinate range (`inverse_target_upper`). Together with the E and
mixed-derivative bounds, the Hessian is negative on the fixed direction `(1,-.7)`
(`hessian_direction_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)
open NegativeTwo.Inverse (q N factorD brace)

def qLower : ℝ := 3029/2500
def qUpper : ℝ := 3289/2500
def factorLower : ℝ := N (9/5)/((9/5)*qUpper)^2
def braceUpper : ℝ := Q0/(9/5)^3-3*(189/500)^2/qUpper

lemma inverse_target_upper {u r z w : ℝ}
    (hu : u∈Icc (9/5:ℝ) (463/250)) (hr : (189/500:ℝ)<r)
    (hz : z∈Icc (0:ℝ) (2/5)) (hw : 0<w) (hn : z^2+w^2=q u) :
    PJCritical.inverseTarget u r z w< -(1/20:ℝ) := by
  have hu0 : 0<u := by linarith [hu.1]
  have hq : q u∈Icc qLower qUpper := by
    dsimp [q,NegativeTwo.Inverse.q,qLower,qUpper]
    norm_num [Q0]
    constructor <;> linarith [hu.1,hu.2]
  have hq0 : 0<q u := by linarith [hq.1,show (0:ℝ)<qLower by norm_num [qLower]]
  have hN : N (9/5)≤N u := by
    have hp := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤4*Q0-2*(u+9/5) by norm_num [Q0]; linarith [hu.2])
    dsimp [N,NegativeTwo.Inverse.N]
    linarith
  have hmass : u*q u≤(9/5)*qUpper := by
    have hp := mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0≤2*u+18/5-(Q0+1) by norm_num [Q0]; linarith [hu.1])
    norm_num [q,NegativeTwo.Inverse.q,qUpper,Q0] at hp ⊢
    linarith
  have hf0 : 0<factorLower := by norm_num [factorLower,N,NegativeTwo.Inverse.N,qUpper,Q0]
  have hf : factorLower≤factorD u := by
    apply (le_div_iff₀ (mul_pos (pow_pos hu0 2) (pow_pos hq0 2))).2
    have hh := pow_le_pow_left₀ (mul_pos hu0 hq0).le hmass 2
    have hm := mul_le_mul_of_nonneg_left hh hf0.le
    have he : factorLower*((9/5)*qUpper)^2=N (9/5) := by
      have hq1 : qUpper≠0 := by norm_num [qUpper]
      unfold factorLower
      field_simp
    rw [he] at hm
    linarith
  have hr0 : 0<r := by linarith
  have hr2 : (189/500:ℝ)^2≤r^2 :=
    pow_le_pow_left₀ (by norm_num) hr.le 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9/5) hu.1 3
  have hfirst : Q0/u^3≤Q0/(9/5)^3 :=
    div_le_div_of_nonneg_left (by norm_num [Q0]) (by norm_num) hu3
  have hsecond : (189/500:ℝ)^2/qUpper≤r^2/q u :=
    div_le_div₀ (sq_nonneg r) hr2 hq0 hq.2
  have hw2 : w^2≤qUpper := by linarith [sq_nonneg z,hq.2]
  have hthird : (189/500:ℝ)^2/qUpper≤r^2/w^2 :=
    div_le_div₀ (sq_nonneg r) hr2 (pow_pos hw 2) hw2
  have hb : brace u r w≤braceUpper := by
    dsimp [brace,NegativeTwo.Inverse.brace,braceUpper]
    have e1 : 2*r^2/q u=2*(r^2/q u) := by ring
    have e2 : 3*(189/500:ℝ)^2/qUpper=3*((189/500)^2/qUpper) := by ring
    rw [e1,e2]
    linarith
  have hb0 : 0≤braceUpper := by norm_num [braceUpper,qUpper,Q0]
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hwl : (41/40:ℝ)<w := by
    have hh := hq.1
    norm_num [qLower] at hh
    exact lt_of_pow_lt_pow_left₀ 2 hw.le (by linarith)
  have hden := mul_le_mul hq.1 hwl.le
    (by norm_num : (0:ℝ)≤41/40) hq0.le
  have hweight : z/(q u*w)≤(2/5)/(qLower*(41/40)) :=
    div_le_div₀ (by norm_num) hz.2 (by norm_num [qLower]) hden
  have hmiddle := (mul_le_mul_of_nonneg_left hb
    (div_nonneg hz.1 (mul_pos hq0 hw).le)).trans
      (mul_le_mul_of_nonneg_right hweight hb0)
  have hprod := mul_le_mul hr.le hf hf0.le hr0.le
  have href : -(189/500)*factorLower+
      ((2/5)/(qLower*(41/40)))*braceUpper< -(1/20:ℝ) := by
    norm_num [factorLower,braceUpper,N,NegativeTwo.Inverse.N,qLower,qUpper,Q0]
  dsimp only [PJCritical.inverseTarget,PJCritical.heightFactorD]
  linarith

lemma stationary_actual {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) :
    b B x∈sourceInterval ∧ criticalU (b B x)=U B ∧
      criticalV (b B x)=W B ∧ criticalRatio (b B x)=ratio B ∧
      B∈Ioo (1/5:ℝ) (8/25) := by
  have hs : b B x∈sourceInterval := ⟨(stationary_source hd hstat).le,hd.2.2.2⟩
  have he := stationary_coordinate hd hstat
  have hc := critical_data hs
  have hcircle := UW_circle (outer_domain hd.1)
  have hW : 0<W B := by dsimp [W]; linarith [hd.1.1]
  have hV : criticalV (b B x)=W B := by
    rw [he] at hc
    nlinarith [hc.2.2.1,hc.2.2.2.1]
  have hr : criticalRatio (b B x)=ratio B := by
    dsimp [criticalRatio,ratio,U,W]
    rw [show criticalV (b B x)=B+1/2 from hV,
      show criticalU (b B x)=ShortOuterOne.SameContact.arc B+1/2 from he]
  have hB : B∈Ioo (1/5:ℝ) (8/25) := by
    have hlo := hc.2.2.2.2.1
    have hhi := hc.2.2.2.2.2.1
    rw [hV] at hlo hhi
    dsimp [W] at hlo hhi
    constructor <;> linarith
  exact ⟨hs,he,hV,hr,hB⟩

theorem hessian_direction_negative {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) :
    E (b B x)-(7/5)*ratio B*(p (b B x))^3+
      (49/100)*(PJCritical.inverseTarget (U B) (ratio B)
        (b B x-1/2) (v B x)-JLabel.d2 B)< -(1/200:ℝ) := by
  obtain ⟨hs,he,hV,hr,hB⟩ := stationary_actual hd hstat
  have hc := critical_data hs
  have hu := criticalU_bounds hs
  rw [he] at hu
  have hu' : U B∈Icc (9/5:ℝ) (463/250) := ⟨by linarith,by linarith⟩
  have hr' : (189/500:ℝ)<ratio B := by
    have hh := hc.2.2.2.2.2.2
    rwa [hr] at hh
  have hz : b B x-1/2∈Icc (0:ℝ) (2/5) := by
    constructor <;> linarith [hs.1,hd.2.2.2,outer_endpoint_bounds.2.2.2]
  have hinverse := inverse_target_upper hu' hr' hz (v_positive hd.1 hd.2.1)
    (norm_identity hd.1 x)
  have hJ := J_second_antitone hd.1
    (Asymmetric.rational_outer_mem (by norm_num : (8/25:ℝ)∈Icc 0 (899/1000))) hB.2.le
  have hcross := critical_mixed_lower hs
  rw [hr] at hcross
  have hE := (E_bounds hs).2
  nlinarith [J_eight_twentyfifths_second]

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
/-!
## The actual inverse-contact curve for the P/J Hessian argument

The angle is the explicit physical inverse
of the same-sign contact.  Differentiation along (1,-.7) realizes the
negative Hessian direction on an actual curve of original contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open NegativeTwo.Inverse (q factor factorD)

def inverseAngle (s B : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle (s-1/2) B
def inverseValue (s B : ℝ) : ℝ := inverseAngle s B+PLabel.outer s-JLabel.outer B
def inverseDirection (s B : ℝ) : ℝ :=
  -1/NegativeTwo.ContactInverse.speed (s-1/2) B-
    (7/10)*(factor (U B)+(s-1/2)*ratio B/
      (q (U B)*NegativeTwo.ContactInverse.speed (s-1/2) B))
def inverseDirectionSecond (s B : ℝ) : ℝ :=
  -((s-1/2)+(7/5)*ratio B)/(NegativeTwo.ContactInverse.speed (s-1/2) B)^3+
    (49/100)*PJCritical.inverseTarget (U B) (ratio B) (s-1/2)
      (NegativeTwo.ContactInverse.speed (s-1/2) B)
def lineValue (s B t : ℝ) : ℝ := inverseValue (s+t) (B-(7/10)*t)
def lineFirst (s B t : ℝ) : ℝ :=
  inverseDirection (s+t) (B-(7/10)*t)+PLabel.d1 (s+t)+(7/10)*JLabel.d1 (B-(7/10)*t)
def lineSecond (s B t : ℝ) : ℝ :=
  inverseDirectionSecond (s+t) (B-(7/10)*t)+PLabel.d2 (s+t)-
    (49/100)*JLabel.d2 (B-(7/10)*t)

lemma inverse_data {s B : ℝ} (hs : s∈Icc 0 outerDiagonal)
    (_hB : B∈Icc 0 outerDiagonal) :
    s-1/2∈Icc (-(1/2):ℝ) (2/5) := by
  constructor <;> linarith [hs.1,hs.2,outer_endpoint_bounds.2.2.2]

lemma inverse_contact {s B : ℝ} (hs : s∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) : b B (inverseAngle s B)=s := by
  have hh := NegativeTwo.ContactInverse.contact hB (inverse_data hs hB)
  dsimp [inverseAngle,b]
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  dsimp [NegativeTwo.TargetContact.B] at hh
  linarith [hh.1]

lemma inverse_original {B x : ℝ} (hd : Domain B x) :
    inverseAngle (b B x) B=x := by
  have hz := inverse_data hd.2.2 hd.1
  have hd' := NegativeTwo.ContactInverse.data hd.1 hz
  have hr : 0<NegativeTwo.ContactInverse.radius B := by linarith [hd'.2.2.1]
  have ht := NegativeTwo.ContactInverse.base_trig hd.1
  have ha := NegativeTwo.ContactInverse.base_bounds hd.1
  have hy : -(Real.pi/2)≤Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B ∧
      Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B≤Real.pi/2 := by
    constructor <;> linarith [hd.2.1.1,hd.2.1.2,ha.1,ha.2,Real.pi_gt_three]
  have he : (b B x-1/2)/NegativeTwo.ContactInverse.radius B=
      Real.sin (Real.pi/2-x-NegativeTwo.ContactInverse.baseAngle B) := by
    rw [Real.sin_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub,ht.1,ht.2]
    dsimp [b,U,W]
    field_simp [hr.ne']
    ring
  dsimp [inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [he,Real.arcsin_sin hy.1 hy.2]
  ring

lemma inverse_speed_original {B x : ℝ} (hd : Domain B x) :
    NegativeTwo.ContactInverse.speed (b B x-1/2) B=v B x := by
  have h := NegativeTwo.ContactInverse.data hd.1 (inverse_data hd.2.2 hd.1)
  have hn := norm_identity hd.1 x
  have hv := v_positive hd.1 hd.2.1
  nlinarith [h.2.2.2.2.1,h.2.2.2.2.2]

lemma inverse_line_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => inverseAngle (s+y) (B-(7/10)*y))
      (inverseDirection (s+t) (B-(7/10)*t)) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hr : 0<NegativeTwo.ContactInverse.radius (B-(7/10)*t) := by linarith [hd.2.2.1]
  have hw := hd.2.2.2.2.1
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hsource : HasDerivAt (fun y : ℝ => s+y-1/2) 1 t :=
    (((hasDerivAt_id' t).const_add s).sub_const (1/2))
  have hrad := (NegativeTwo.ContactInverse.radius_hasDerivAt hB).comp t htarget
  have harg := hsource.fun_div hrad hr.ne'
  have ha := NegativeTwo.ContactInverse.argument_bounds hB hz
  have hasin := (Real.hasDerivAt_arcsin
    (by linarith : (s+t-1/2)/NegativeTwo.ContactInverse.radius (B-(7/10)*t)≠-1)
    (by linarith : (s+t-1/2)/NegativeTwo.ContactInverse.radius (B-(7/10)*t)≠1)).comp t harg
  have hbase := (NegativeTwo.ContactInverse.base_hasDerivAt hB).comp t htarget
  have hder := (hbase.fun_add hasin).const_sub (Real.pi/2)
  refine hder.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [NegativeTwo.ContactInverse.inverse_root hB hz]
  dsimp only [inverseDirection]
  rw [←hd.2.2.2.1]
  generalize NegativeTwo.ContactInverse.radius (B-(7/10)*t)=r at hr ⊢
  generalize NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)=v at hw ⊢
  have hr0 := hr.ne'
  have hw0 := hw.ne'
  field_simp
  ring

lemma inverse_direction_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (fun y => inverseDirection (s+y) (B-(7/10)*y))
      (inverseDirectionSecond (s+t) (B-(7/10)*t)) t := by
  have hz := inverse_data hs hB
  have hd := NegativeTwo.ContactInverse.data hB hz
  have hu := hd.1
  have hw := hd.2.2.2.2.1
  have hq : 0<q (U (B-(7/10)*t)) := by linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hsource : HasDerivAt (fun y : ℝ => s+y-1/2) 1 t :=
    (((hasDerivAt_id' t).const_add s).sub_const (1/2))
  have hU0 := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
      (1/2)).comp t htarget
  have hU : HasDerivAt (fun y => U (B-(7/10)*y)) (-ratio (B-(7/10)*t)*(-(7/10))) t := hU0
  have hQ := (NegativeTwo.Inverse.q_hasDerivAt (U (B-(7/10)*t))).comp t hU
  have hR := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).comp t htarget
  have hF := (NegativeTwo.Inverse.factor_hasDerivAt hu.ne' hq.ne').comp t hU
  have hrad : q (U (B-(7/10)*t))-(s+t-1/2)^2≠0 := by
    nlinarith [hd.2.2.2.2.2,sq_pos_of_pos hw]
  have hspeed := (hQ.fun_sub (hsource.fun_pow 2)).sqrt hrad
  have hden := hQ.fun_mul hspeed
  have hweight := (hsource.fun_mul hR).fun_div hden (mul_ne_zero hq.ne' hw.ne')
  have hrecip := (hasDerivAt_const t (-(1:ℝ))).fun_div hspeed hw.ne'
  have hder := hrecip.fun_sub ((hF.fun_add hweight).const_mul (7/10))
  refine hder.congr_deriv ?_
  have hsp : Real.sqrt (q (U (B-(7/10)*t))-(s+t-1/2)^2)=
      NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t) := rfl
  have hrD : ratioD (B-(7/10)*t)=Q0/(U (B-(7/10)*t))^3 := rfl
  simp only [Function.comp_apply,inverseDirectionSecond,PJCritical.inverseTarget,
    PJCritical.heightFactorD,NegativeTwo.Inverse.brace,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  rw [hsp,hrD]
  have hn := hd.2.2.2.2.2
  generalize NegativeTwo.ContactInverse.speed (s+t-1/2) (B-(7/10)*t)=v at hw hn ⊢
  generalize q (U (B-(7/10)*t))=Q at hq hn ⊢
  generalize factorD (U (B-(7/10)*t))=F
  generalize U (B-(7/10)*t)=u at hu ⊢
  generalize ratio (B-(7/10)*t)=ρ
  generalize s+t-1/2=z at hn ⊢
  have hu0 := hu.ne'
  have hq0 := hq.ne'
  have hw0 := hw.ne'
  field_simp
  linear_combination (-35000*Q*ρ*u^3)*hn

lemma lineValue_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (lineValue s B) (lineFirst s B t) t := by
  have hsource : HasDerivAt (fun y : ℝ => s+y) 1 t := (hasDerivAt_id' t).const_add s
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hP0 := (PLabel.outer_hasDerivAt (outer_domain hs)).comp t hsource
  have hP : HasDerivAt (fun y => PLabel.outer (s+y)) (PLabel.d1 (s+t)*1) t := hP0
  have hJ0 := (JLabel.outer_hasDerivAt (outer_domain hB)).comp t htarget
  have hJ : HasDerivAt (fun y => JLabel.outer (B-(7/10)*y))
      (JLabel.d1 (B-(7/10)*t)*(-(7/10))) t := hJ0
  exact (((inverse_line_hasDerivAt hs hB).fun_add hP).fun_sub hJ).congr_deriv
    (by dsimp only [lineFirst]; ring)

lemma lineFirst_hasDerivAt {s B t : ℝ}
    (hs : s+t∈Icc 0 outerDiagonal) (hB : B-(7/10)*t∈Icc 0 outerDiagonal) :
    HasDerivAt (lineFirst s B) (lineSecond s B t) t := by
  have hsource : HasDerivAt (fun y : ℝ => s+y) 1 t := (hasDerivAt_id' t).const_add s
  have htarget : HasDerivAt (fun y : ℝ => B-(7/10)*y) (-(7/10)) t :=
    (((hasDerivAt_id' t).const_mul (7/10)).const_sub B).congr_deriv (by ring)
  have hP0 := (PLabel.d1_hasDerivAt (outer_domain hs)).comp t hsource
  have hP : HasDerivAt (fun y => PLabel.d1 (s+y)) (PLabel.d2 (s+t)*1) t := hP0
  have hJ0 := (JLabel.d1_hasDerivAt (outer_domain hB)).comp t htarget
  have hJ : HasDerivAt (fun y => JLabel.d1 (B-(7/10)*y))
      (JLabel.d2 (B-(7/10)*t)*(-(7/10))) t := hJ0
  exact (((inverse_direction_hasDerivAt hs hB).fun_add hP).fun_add
    (hJ.const_mul (7/10))).congr_deriv (by dsimp only [lineSecond]; ring)

lemma stationary_line_negative {B x : ℝ} (hd : Domain B x)
    (hstat : angleFirst PLabel B x=0) : lineSecond (b B x) B 0< -(1/200:ℝ) := by
  have hneg := hessian_direction_negative hd hstat
  have hv := v_positive hd.1 hd.2.1
  have hp := p_positive hd.2.2
  have hprod : p (b B x)*v B x=1 := by dsimp [p,angleFirst] at *; linarith
  have hcube : 1/(v B x)^3=(p (b B x))^3 := by
    field_simp
    rw [← mul_pow,mul_comm,hprod]
    norm_num
  have heq : lineSecond (b B x) B 0=E (b B x)-(7/5)*ratio B*(p (b B x))^3+
      (49/100)*(PJCritical.inverseTarget (U B) (ratio B) (b B x-1/2) (v B x)-JLabel.d2 B) := by
    simp only [lineSecond,inverseDirectionSecond,add_zero,mul_zero,sub_zero,
      inverse_speed_original hd,E]
    rw [div_eq_mul_one_div _ ((v B x)^3),hcube]
    ring
  linarith

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma zero_angle_positive {x : ℝ} (hd : Domain 0 x) : 0<angleFirst PLabel 0 x := by
  let z := b 0 x-1/2
  let q₀ := NegativeTwo.Inverse.q (U 0)
  let R := Real.sqrt q₀
  have hv := v_positive hd.1 hd.2.1
  have hp := (P_first_bounds hd.2.2).1
  have hq0 : 0<q₀ := by linarith [NegativeTwo.Inverse.actual_q_positive outer_zero_mem]
  have hq : q₀<(1087/1000:ℝ) := by
    dsimp [q₀,NegativeTwo.Inverse.q,U]
    rw [ShortOuterOne.SameContact.arc_zero]
    norm_num [Q0]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hR : 0<R := Real.sqrt_pos.mpr hq0
  have hR2 : R^2=q₀ := Real.sq_sqrt hq0.le
  have hRu : R<(1043/1000:ℝ) := by nlinarith
  have hn : z^2+(v 0 x)^2=q₀ := norm_identity outer_zero_mem x
  have hP : PLabel.d1 (b 0 x)<443/500+(223/1000)*z := by
    have hh := OppositeTwo.P_first_affine hd.2.2
    dsimp [z]
    linarith
  have hvR : v 0 x≤R := by nlinarith [sq_nonneg z]
  have hprod : PLabel.d1 (b 0 x)*v 0 x<1 := by
    rcases le_total z 0 with hz | hz
    · have hsmall : PLabel.d1 (b 0 x)<443/500 := by linarith
      have hh := mul_lt_mul'' hsmall (hvR.trans_lt hRu) (by linarith) hv.le
      norm_num at hh
      linarith
    · have htangent : v 0 x≤R-z^2/(2*R) := by
        have h2R : 0<2*R := by linarith
        have hh : z^2/(2*R)≤R-v 0 x := by
          rw [div_le_iff₀ h2R]
          nlinarith [sq_nonneg (R-v 0 x)]
        linarith
      have hcoef : 0<443/500+(223/1000)*z := by linarith
      have h1 := mul_lt_mul_of_pos_right hP hv
      have h2 := mul_le_mul_of_nonneg_left htangent hcoef.le
      have hcomplete : (443/500+(223/1000)*z)*(R-z^2/(2*R))≤
          (443/500)*R+(223/1000)^2*R^3/(2*(443/500)) := by
        have hkey : (443/500)*R+(223/1000)^2*R^3/(2*(443/500))-
            (443/500+(223/1000)*z)*(R-z^2/(2*R))=
            ((443/500)*z-(223/1000)*R^2)^2/(2*(443/500)*R)+(223/1000)*z^3/(2*R) := by
          field_simp
          ring
        have hnn : 0≤((443/500)*z-(223/1000)*R^2)^2/(2*(443/500)*R)+(223/1000)*z^3/(2*R) :=
          add_nonneg (by positivity)
            (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz 3)) (by positivity))
        linarith
      have hcube : R^3<(1087/1000)*(1043/1000:ℝ) := by
        have hh := mul_lt_mul'' hq hRu hq0.le hR.le
        have he : R^3=q₀*R := by rw [←hR2]; ring
        rw [he]
        exact hh
      have hend : (443/500)*(1043/1000)+
          (223/1000)^2*((1087/1000)*(1043/1000))/(2*(443/500))<(1:ℝ) := by norm_num
      nlinarith
  dsimp [angleFirst]
  linarith

theorem zero_boundary_lower {x : ℝ} (hd : Domain 0 x) :
    (89777/100000:ℝ)<value PLabel JLabel 0 x := by
  have hstart : Diagonal.start<x := by
    by_contra! hn
    have hh := b_angle_antitone outer_zero_mem hd.2.1
      (by norm_num [Diagonal.start] : Diagonal.start∈Icc 0 (7/10)) hn
    linarith [Reference.zero_start,hd.2.2.2]
  have hc : Continuous (b 0) := by
    have hb : b 0=fun t => 1/2+(0+1/2)*Real.cos t-(arc 0-1/2)*Real.sin t := rfl
    rw [hb]
    fun_prop
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc hstart.le hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-b 0 Diagonal.start) (-b 0 x) by
      constructor <;> linarith [Reference.zero_start,hd.2.2.2])
  simp only [Pi.neg_apply] at he
  have hcontact : b 0 y=outerDiagonal := by linarith
  have hyi : y∈Icc 0 (7/10) :=
    ⟨by linarith [hy.1,show (0:ℝ)<Diagonal.start by norm_num [Diagonal.start]],hy.2.trans hd.2.1.2⟩
  have hdom : ∀t∈Icc y x,Domain 0 t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyi.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    have hb := b_angle_antitone outer_zero_mem hyi hti ht.1
    rw [hcontact] at hb
    exact ⟨outer_zero_mem,hti,⟨by linarith [b_lower outer_zero_mem hti],hb⟩⟩
  have hm : MonotoneOn (value PLabel JLabel 0) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (value_angle_hasDerivAt PLabel JLabel (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => value_angle_hasDerivAt PLabel JLabel (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (zero_angle_positive (hdom t (Ioo_subset_Icc_self ht))).le)
  have hh := hm ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2
  dsimp [value] at hh ⊢
  rw [hcontact] at hh
  linarith [Reference.zero_start_cost,hy.1]

def capSecond (B : ℝ) : ℝ :=
  PLabel.d2 (b B (7/10))*(k B (7/10))^2+
    PLabel.d1 (b B (7/10))*ratioD B*Real.sin (7/10)-JLabel.d2 B

lemma capFirst_hasDerivAt {B : ℝ} (hd : Domain B (7/10)) :
    HasDerivAt (fun t => targetFirst PLabel JLabel t (7/10)) (capSecond B) B := by
  have hk : HasDerivAt (fun t => k t (7/10)) (ratioD B*Real.sin (7/10)) B :=
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).mul_const
      (Real.sin (7/10))).const_add (Real.cos (7/10))
  have h := (((PLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp B
    (b_target_hasDerivAt hd.1 (7/10))).mul hk).sub
      (JLabel.d1_hasDerivAt (outer_domain hd.1))
  convert h using 1
  · funext t
    rfl
  · dsimp [capSecond]
    ring

lemma cap_curvature {B : ℝ} (hd : Domain B (7/10)) : (329/1000:ℝ)<capSecond B := by
  have hP2 := P_second_positive hd.2.2
  have hp := (P_first_bounds hd.2.2).1
  have hD := (outer_ratio_bounds hd.1).2.2.1
  have hs := (positive_trig hd.2.1).2.2.1
  have h1 := mul_nonneg hP2.le (sq_nonneg (k B (7/10)))
  have h2 := mul_nonneg (mul_nonneg (by linarith : 0≤PLabel.d1 (b B (7/10))) hD.le) hs
  have hJ := J_second_upper hd.1
  dsimp [capSecond]
  linarith

theorem cap_boundary_lower {B : ℝ} (hd : Domain B (7/10)) :
    (89777/100000:ℝ)<value PLabel JLabel B (7/10) := by
  let r := Reference.capReference
  let l := min B r
  let u := max B r
  have hr := Reference.cap_reference
  have hB : B∈Icc l u := ⟨min_le_left _ _,le_max_left _ _⟩
  have hR : r∈Icc l u := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom : ∀t∈Icc l u,Domain t (7/10) := by
    intro t ht
    have hti : t∈Icc 0 outerDiagonal :=
      ⟨(le_min hd.1.1 hr.1.1.1).trans ht.1,ht.2.trans (max_le hd.1.2 hr.1.1.2)⟩
    have hcut : b t (7/10)≤outerDiagonal := by
      rcases le_total B r with he | he
      · have htr : t≤r := by simpa [u,max_eq_right he] using ht.2
        exact (b_target_monotone hd.2.1 hti hr.1.1 htr).trans hr.1.2.2.2
      · have htB : t≤B := by simpa [u,max_eq_left he] using ht.2
        exact (b_target_monotone hd.2.1 hti hd.1 htB).trans hd.2.2.2
    exact ⟨hti,hd.2.1,⟨by linarith [b_lower hti hd.2.1],hcut⟩⟩
  have hh := curvature_tangent
    (f := fun t => value PLabel JLabel t (7/10))
    (d := fun t => targetFirst PLabel JLabel t (7/10)) (dd := capSecond)
    (κ := (329/1000:ℝ)) hB hR
    (fun t ht => value_target_hasDerivAt PLabel JLabel (hdom t ht))
    (fun t ht => capFirst_hasDerivAt (hdom t ht))
    (fun t ht => (cap_curvature (hdom t ht)).le)
  have hs := abs_lt.mp hr.2.2
  have hsquare := sq_nonneg ((329/1000)*(B-r)+targetFirst PLabel JLabel r (7/10))
  have hsmall : (targetFirst PLabel JLabel r (7/10))^2<(1/100000:ℝ)^2 := by nlinarith
  nlinarith [hr.2.1]

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
end
end
end
