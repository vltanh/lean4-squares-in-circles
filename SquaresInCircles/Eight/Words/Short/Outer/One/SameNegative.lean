module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameDiagonal
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositive

/-!
# Eight squares: the complete negative halves of the same-sign primary owners

The original circle identity gives a positive angular derivative at
every physical active contact. Decreasing the angle reaches alignment
or the complete source-diagonal curve. Target slack decreases until
that original contact is attained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Negative
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

def contact (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x
def speed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x+(B-1/2)*Real.sin x
def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ contact B x∈Icc outerDiagonal outerAxial
def cost (r : Row) (B x : ℝ) : ℝ :=
  Real.pi/2-x+c r+source r (contact B x)+target r B
def first (r : Row) (B x : ℝ) : ℝ := -1+sourceD r (contact B x)*speed B x

lemma contact_hasDerivAt (B x : ℝ) : HasDerivAt (contact B) (speed B x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (arc B+1/2)) using 1
  · funext y; simp only [contact,Pi.add_apply]
  · simp only [speed]; ring

lemma speed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<speed B x := by
  have hA := (outer_bounds (SameContact.arc_state hB)).1
  have ht := positive_trig hx
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤arc B+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (by linarith [outer_endpoint_bounds.2.2.1] : 0≤arc B+1/2)
  have hs := mul_le_mul_of_nonneg_right (show -(1/2:ℝ)≤B-1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [speed]
  nlinarith [ht.2.2.2.1]

lemma contact_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (contact B) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x _ => (contact_hasDerivAt B x).continuousAt.continuousWithinAt)
  (fun x _ => contact_hasDerivAt B x)
  (fun x hx => (speed_positive hB (Ioo_subset_Icc_self hx)).le)

lemma contact_zero (B : ℝ) : contact B 0=1-B := by norm_num [contact]; ring

lemma speed_circle {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (speed B x)^2=Q0-2*B-(contact B x-1/2)^2 := by
  have hc := SameContact.arc_circle (SameContact.outer_domain hB)
  dsimp [speed,contact]
  linear_combination hc+((arc B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma first_positive (r : Row) {B x : ℝ} (hd : Domain B x) : 0<first r B x := by
  have hspeed := speed_positive hd.1 hd.2.1
  have hcircle := speed_circle (x := x) hd.1
  have hB : B<(9/10:ℝ) := hd.1.2.trans_lt outer_endpoint_bounds.2.2.2
  have ha : 0≤contact B x-1/2 ∧ contact B x-1/2<(183/200:ℝ) :=
    ⟨by linarith [hd.2.2.1,outer_endpoint_bounds.2.2.1],
      by linarith [hd.2.2.2,outer_endpoint_bounds.2.1]⟩
  have hsquare := pow_le_pow_left₀ ha.1 ha.2.le 2
  have hreserve : (1:ℝ)<(94766/100000)*speed B x := by
    norm_num [Q0] at hcircle
    nlinarith
  have hL := mul_le_mul_of_nonneg_right (sourceD_lower r hd.2.2) hspeed.le
  dsimp [first]
  linarith

lemma cost_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (first r B x) x := by
  convert ((((hasDerivAt_id x).neg).const_add (Real.pi/2+c r)).add
    ((source_hasDerivAt r hd.2.2).comp x (contact_hasDerivAt B x))).add_const
      (target r B) using 1
  · funext y; simp only [cost,Pi.add_apply,Pi.neg_apply,id_eq,Function.comp_apply]; ring
  · simp only [first]

lemma physical_between {B x y z : ℝ} (hd : Domain B x)
    (hy : y∈Icc 0 x) (hcontact : outerDiagonal≤contact B y) (hz : z∈Icc y x) : Domain B z := by
  have hy' : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hz' : z∈Icc 0 (7/10) := ⟨hy.1.trans hz.1,hz.2.trans hd.2.1.2⟩
  exact ⟨hd.1,hz',hcontact.trans (contact_monotone hd.1 hy' hz' hz.1),
    (contact_monotone hd.1 hz' hd.2.1 hz.2).trans hd.2.2.2⟩

lemma cost_monotone_between (r : Row) {B x y : ℝ} (hd : Domain B x)
    (hy : y∈Icc 0 x) (hcontact : outerDiagonal≤contact B y) :
    MonotoneOn (cost r B) (Icc y x) := monoOn_of_hasDeriv_nonneg
  (fun z hz => (cost_hasDerivAt r (physical_between hd hy hcontact hz)).continuousAt.continuousWithinAt)
  (fun z hz => cost_hasDerivAt r (physical_between hd hy hcontact (Ioo_subset_Icc_self hz)))
  (fun z hz => (first_positive r (physical_between hd hy hcontact (Ioo_subset_Icc_self hz))).le)

lemma initial_cost (r : Row) (B : ℝ) : cost r B 0=aligned r B := by
  rw [cost,contact_zero]
  simp [aligned]

lemma diagonal_cost (r : Row) {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (he : contact B x=outerDiagonal) :
    (8981/10000:ℝ)<cost r B x := by
  have hh := Diagonal.original_contact r (SameContact.arc_state hB) hx
    (by simpa [contact] using he)
  dsimp [cost,source,target]
  rw [he,SameContact.arc_diagonal]
  nlinarith only [hh]

theorem active_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  by_cases hzero : outerDiagonal≤contact B 0
  · have hB : B∈Icc 0 b0 := ⟨hd.1.1,by rw [contact_zero] at hzero; dsimp [b0]; linarith⟩
    have hh := aligned_lower r hB
    have hm := cost_monotone_between r hd (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩) hzero
      (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩)
      (show x∈Icc 0 x from ⟨hd.2.1.1,le_rfl⟩) hd.2.1.1
    rw [initial_cost] at hm
    exact hh.trans_le hm
  · have hc : Continuous (contact B) := by
      have he : contact B = fun x => 1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x := rfl
      rw [he]; fun_prop
    obtain ⟨y,hy,he⟩ := intermediate_value_Icc hd.2.1.1 hc.continuousOn
      (show outerDiagonal∈Icc (contact B 0) (contact B x) from ⟨by linarith,hd.2.2.1⟩)
    have hy' : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
    have hh := diagonal_cost r hd.1 hy' he
    have hm := cost_monotone_between r hd hy he.ge
      (show y∈Icc y x from ⟨le_rfl,hy.2⟩)
      (show x∈Icc y x from ⟨hy.2,le_rfl⟩) hy.2
    exact hh.trans_le hm

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x+B*Real.cos x) :
    (8981/10000:ℝ)<Real.pi/2-x+c r+p r*a-q r*b-P r*A+t r*B := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hcontact : contact B x≤a := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c r+source r a+target r B=
      Real.pi/2-x+c r+p r*a-q r*b-P r*A+t r*B := by
    have hh := Positive.physical_state_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : outerDiagonal≤contact B x
  · have hdom : Domain B x := ⟨hB,hx,hactive,hcontact.trans ha.2⟩
    have hmono := source_monotone r hdom.2.2 ha hcontact
    have hh := active_lower r hdom
    dsimp [cost] at hh
    linarith
  · have hsource := source_monotone r hd ha ha.1
    have haxial := contact_monotone hzero (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    rw [contact_zero] at haxial
    have hc : Continuous (fun D : ℝ => -contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,hDe⟩ := intermediate_value_Icc hB.1 hc.continuousOn
      (show -outerDiagonal∈Icc (-contact 0 x) (-contact B x) from
        ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith⟩)
    have he : contact D x=outerDiagonal := by linarith
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hD.1,hD.2.trans hB.2⟩
    have htarget := target_monotone r hDouter hB hD.2
    have hh := diagonal_cost r hDouter hx he
    dsimp [cost] at hh
    rw [he] at hh
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Negative
