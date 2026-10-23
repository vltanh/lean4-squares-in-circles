module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreePrimaryMotion
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# The whole upper-primary target-ratio arc

One scaled second-derivative bound proves concavity on `[.2,d]`.
Only the two ends of that complete arc are evaluated.  The actual
circle identity supplies both the third-derivative numerator and the
power bounds, with no subdivision of the continuous target interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.CapRatio
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def c : ℝ := Real.cos (7/10)
def s : ℝ := Real.sin (7/10)
def V (B : ℝ) : ℝ := (U B-1)*c+W B*s
def m (B : ℝ) : ℝ := s-ratio B*c
def F (B : ℝ) : ℝ := c+ratio B*s-LLabel.d1 B*V B
def first (B : ℝ) : ℝ := ratioD B*s-LLabel.d2 B*V B-LLabel.d1 B*m B
def second (B : ℝ) : ℝ :=
  ratioDD B*s-LLabel.d3 B*V B-2*LLabel.d2 B*m B+LLabel.d1 B*ratioD B*c

lemma trig : (76484/100000:ℝ)<c ∧ c<15297/20000 ∧
    (64421/100000:ℝ)<s ∧ s<32211/50000 := by
  have hh := ShortOuterOne.FiveSame.cap_fine
  dsimp [c,s]
  exact ⟨by linarith [hh.2.2.1],by linarith [hh.2.2.2],
    by linarith [hh.1],by linarith [hh.2.1]⟩

lemma domain {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) :
    B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩

lemma fifth_U : (185083/100000:ℝ)<U (1/5) ∧ U (1/5)<92542/50000 :=
  shifted_chart_reference (outer_domain fifth_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma fifth_ratio : (1891/5000:ℝ)<ratio (1/5) ∧ ratio (1/5)<37821/100000 := by
  have hu := U_positive (outer_domain fifth_mem)
  change (1891/5000:ℝ)<(1/5+1/2)/U (1/5) ∧
    (1/5+1/2)/U (1/5)<37821/100000
  constructor
  · apply (lt_div_iff₀ hu).2
    nlinarith [fifth_U.2]
  · apply (div_lt_iff₀ hu).2
    nlinarith [fifth_U.1]

lemma fifth_first : LLabel.d1 (1/5)<(21009/25000:ℝ) := by
  have hh := LLabel.first_chart_reference (outer_domain fifth_mem)
    (l := (185083764/10^8:ℝ)) (u := (185083765/10^8:ℝ))
    (dlo := (4/5:ℝ)) (dhi := (21009/25000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.2

lemma V_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt V (m B) B := by
  convert (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
    (-(1/2))).mul_const c).add (((hasDerivAt_id B).add_const (1/2)).mul_const s)
      using 1 <;> dsimp [V,m,U,W] <;> ring

lemma m_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt m (-ratioD B*c) B := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const c).const_sub s
    using 1 <;> dsimp [m] <;> ring

lemma F_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt F (first B) B := by
  convert (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const s).const_add c).sub
    ((LLabel.d1_hasDerivAt (outer_domain hB)).mul (V_hasDerivAt hB)) using 1 <;>
    dsimp [F,first] <;> ring

lemma first_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt first (second B) B := by
  convert (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).mul_const s).sub
    ((LLabel.d2_hasDerivAt (outer_domain hB)).mul (V_hasDerivAt hB))).sub
      ((LLabel.d1_hasDerivAt (outer_domain hB)).mul (m_hasDerivAt hB)) using 1 <;>
    dsimp [first,second] <;> ring

lemma V_fifth : (11/10:ℝ)<V (1/5) ∧ V (1/5)<110173/100000 := by
  have hlo := mul_lt_mul (show (85083/100000:ℝ)<U (1/5)-1 by linarith [fifth_U.1])
    trig.1 (by norm_num) (by linarith [fifth_U.1] : 0≤U (1/5)-1)
  have hhi := mul_lt_mul (show U (1/5)-1<(42542/50000:ℝ) by linarith [fifth_U.2])
    trig.2.1 (by linarith [trig.1] : 0<c) (by norm_num)
  dsimp [V,W]
  constructor <;> nlinarith [trig.2.2.1,trig.2.2.2]

lemma V_diagonal : (11/10:ℝ)<V outerDiagonal ∧ V outerDiagonal<4827/4000 := by
  have hd : (89921/100000:ℝ)<outerDiagonal ∧ outerDiagonal<179843/200000 := by
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have hlo1 := mul_lt_mul (show (39921/100000:ℝ)<outerDiagonal-1/2 by linarith)
    trig.1 (by norm_num) (by linarith [hd.1] : 0≤outerDiagonal-1/2)
  have hlo2 := mul_lt_mul (show (139921/100000:ℝ)<outerDiagonal+1/2 by linarith)
    trig.2.2.1 (by norm_num) (by linarith [hd.1] : 0≤outerDiagonal+1/2)
  have hhi1 := mul_lt_mul (show outerDiagonal-1/2<(79843/200000:ℝ) by linarith)
    trig.2.1 (by linarith [trig.1] : 0<c) (by norm_num)
  have hhi2 := mul_lt_mul (show outerDiagonal+1/2<(279843/200000:ℝ) by linarith)
    trig.2.2.2 (by linarith [trig.2.2.1] : 0<s) (by norm_num)
  dsimp [V,U,W]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  constructor <;> nlinarith

lemma V_lower {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) : (11/10:ℝ)<V B := by
  have hc : ConcaveOn ℝ (Icc (1/5) outerDiagonal) V := concave_of_deriv2
    (fun t ht => V_hasDerivAt (domain ht))
    (fun t ht => m_hasDerivAt (domain ht))
    (fun t ht => by
      have hp := (outer_ratio_bounds (domain ht)).2.2.1
      exact neg_nonpos.mpr (mul_nonneg hp.le (by linarith [trig.1])))
  exact concave_gt_of_endpoints hc hB V_fifth.1 V_diagonal.1

lemma m_bounds {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) :
    -(9/25:ℝ)<m B ∧ m B<9/25 := by
  have hr := outer_ratio_bounds (domain hB)
  have hlo := ShortOuterOne.SameContact.ratio_monotone
    (outer_domain fifth_mem) (outer_domain (domain hB)) hB.1
  have hprodlo := mul_le_mul
    (show (1891/5000:ℝ)≤ratio B by linarith [fifth_ratio.1]) trig.1.le
    (by norm_num) (by linarith [hr.1] : 0≤ratio B)
  have hprodhi := mul_le_mul hr.2.1 trig.2.1.le
    (by linarith [trig.1] : 0≤c) (by norm_num)
  dsimp [m]
  constructor <;> linarith [trig.2.2.1,trig.2.2.2]

lemma L_second_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    -(33/10:ℝ)<LLabel.d2 B ∧ LLabel.d2 B<33/10 := by
  have hr := outer_ratio_bounds hB
  have hlo : -(33/10:ℝ)<LLabel.d2 B := by
    have hprod := mul_nonneg hB.1 hr.2.2.1.le
    norm_num [RoleLabel.d2,LLabel]
    nlinarith [hr.1]
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hmono := L_second_monotone hB hd hB.2
  have hU : U outerDiagonal=outerDiagonal+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_diagonal]
  have hp : 0<outerDiagonal+1/2 := by linarith [fine_outer_endpoint_bounds.2]
  have hcircle := UW_circle (outer_domain hd)
  rw [hU] at hcircle
  have hD : ratioD outerDiagonal=2/(outerDiagonal+1/2) := by
    dsimp [ratioD]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    dsimp [W] at hcircle
    field_simp [hp.ne']
    nlinarith [hcircle]
  have he : LLabel.d2 outerDiagonal*(outerDiagonal+1/2)=
      (19847/25000)*(outerDiagonal+1/2)+(94721/25000)*outerDiagonal := by
    dsimp [RoleLabel.d2,LLabel]
    rw [ratio_diagonal,hD]
    field_simp [hp.ne']
    ring
  have hhi : LLabel.d2 outerDiagonal<33/10 := by
    apply (mul_lt_mul_right hp).mp
    rw [he]
    linarith [outer_endpoint_bounds.2.2.2]
  exact ⟨hlo,hmono.trans_lt hhi⟩

lemma second_negative {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) : second B<0 := by
  have hb := domain hB
  have hu := U_positive (outer_domain hb)
  have hcircle := UW_circle (outer_domain hb)
  have hUlo := (UW_bounds hb).1
  have hUhi : U B<(1851/1000:ℝ) := by
    have hh := ShortOuterOne.SameContact.arc_antitone
      (outer_domain fifth_mem) (outer_domain hb) hB.1
    have huf := fifth_U
    dsimp [U] at huf ⊢
    linarith [huf.2]
  have hW : (7/10:ℝ)≤W B ∧ W B<7/5 := by
    dsimp [W]
    constructor <;> linarith [hB.1,hB.2,outer_endpoint_bounds.2.2.2]
  have hU2 : (U B)^2<(1713/500:ℝ) := by norm_num [Q0] at hcircle; nlinarith
  have hU5 := pow_lt_pow_left₀ hu.le hUhi (by norm_num : (5:ℕ)≠0)
  have hV := V_lower hB
  have hM := m_bounds hB
  have hL := L_second_bounds hb
  have hLp := L_first_bounds hb
  have hQ : 0<Q0 := by norm_num [Q0]
  have hnum := LLabel.third_numerator (outer_domain hb)
  have hthird : LLabel.d3 B*(U B)^5=
      3*Q0*(94721/50000)*(Q0-W B/2) := by
    norm_num [LLabel] at hnum
    nlinarith
  have hscaled : second B*(U B)^5=
      3*Q0*W B*s-3*Q0*(94721/50000)*(Q0-W B/2)*V B-
        2*LLabel.d2 B*m B*(U B)^5+LLabel.d1 B*Q0*(U B)^2*c := by
    calc
      second B*(U B)^5=ratioDD B*s*(U B)^5-(LLabel.d3 B*(U B)^5)*V B-
          2*LLabel.d2 B*m B*(U B)^5+LLabel.d1 B*ratioD B*c*(U B)^5 := by
        dsimp [second]
        ring
      _=3*Q0*W B*s-3*Q0*(94721/50000)*(Q0-W B/2)*V B-
          2*LLabel.d2 B*m B*(U B)^5+LLabel.d1 B*Q0*(U B)^2*c := by
        rw [hthird]
        dsimp [ratioD,ratioDD,U,W]
        field_simp [show arc B+1/2≠0 from hu.ne']
        ring
  have hterm1 : 3*Q0*W B*s<3*Q0*(7/5)*(129/200) := by
    have hh := mul_lt_mul hW.2
      (show s<(129/200:ℝ) by linarith [trig.2.2.2])
      (by linarith [trig.2.2.1] : 0<s) (by norm_num)
    exact mul_lt_mul_of_pos_left hh (by norm_num [Q0])
  have hterm2 : 3*Q0*(94721/50000)*(Q0-7/10)*(11/10)<
      3*Q0*(94721/50000)*(Q0-W B/2)*V B := by
    have hh := mul_lt_mul (show Q0-7/10<Q0-W B/2 by linarith) hV
      (by norm_num : (0:ℝ)<11/10) (by norm_num [Q0]; linarith [hW.2] : 0≤Q0-W B/2)
    exact mul_lt_mul_of_pos_left hh (by norm_num [Q0])
  have hmixed : -(33/10:ℝ)*(9/25)<LLabel.d2 B*m B := by
    by_cases hs : 0≤LLabel.d2 B
    · have hh := mul_le_mul_of_nonneg_left hM.1.le hs
      nlinarith [hL.2]
    · have hh := mul_le_mul_of_nonpos_left hM.2.le (le_of_not_ge hs)
      nlinarith [hL.1]
  have hterm3 : -2*LLabel.d2 B*m B*(U B)^5<
      2*(33/10)*(9/25)*(1851/1000)^5 := by
    have hh := mul_lt_mul_of_pos_right (show -2*LLabel.d2 B*m B<2*(33/10)*(9/25) by linarith)
      (pow_pos hu 5)
    nlinarith [hU5]
  have hterm4 : LLabel.d1 B*Q0*(U B)^2*c<
      (147/125)*Q0*(1713/500)*(153/200) := by
    have hp := mul_lt_mul hLp.2 hU2 (sq_pos_of_pos hu) (by norm_num)
    have hc := mul_lt_mul hp (show c<(153/200:ℝ) by linarith [trig.2.1])
      (by linarith [trig.1] : 0<c) (by norm_num)
    have hh := mul_lt_mul_of_pos_left hc hQ
    nlinarith
  have hnegative : second B*(U B)^5<0 := by
    norm_num [Q0] at hterm1 hterm2 hterm3 hterm4 hscaled
    linarith
  nlinarith [pow_pos hu 5]

lemma fifth_positive : (41/500:ℝ)<F (1/5) := by
  have hnum := mul_lt_mul fifth_ratio.1 trig.2.2.1 (by norm_num)
    (by linarith [fifth_ratio.1] : 0≤ratio (1/5))
  have hsub := mul_lt_mul fifth_first V_fifth.2
    (by linarith [V_fifth.1] : 0<V (1/5)) (by norm_num)
  dsimp [F]
  nlinarith [trig.1]

lemma diagonal_positive : (17/2500:ℝ)<F outerDiagonal := by
  have hLp : LLabel.d1 outerDiagonal<(581/500:ℝ) := by
    rw [L_first_diagonal]
    linarith [diagonal_fine.1]
  have hsub := mul_lt_mul hLp V_diagonal.2
    (by linarith [V_diagonal.1] : 0<V outerDiagonal) (by norm_num)
  dsimp [F]
  rw [ratio_diagonal]
  nlinarith [trig.1,trig.2.2.1]

theorem positive {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) : 0<F B := by
  have hc : ConcaveOn ℝ (Icc (1/5) outerDiagonal) F := concave_of_deriv2
    (fun t ht => F_hasDerivAt (domain ht))
    (fun t ht => first_hasDerivAt (domain ht))
    (fun t ht => (second_negative ht).le)
  exact concave_gt_of_endpoints hc hB (by linarith [fifth_positive])
    (by linarith [diagonal_positive])

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.CapRatio
