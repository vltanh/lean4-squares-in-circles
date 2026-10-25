module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeReferenceAlgebra
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperSourcePrimary

/-!
# Eight squares: the complete initial target-diagonal curvature interval

The diagonal inverse uses the original fixed radius and literal target
diagonal.  The inverse-polynomial height bound and a positive bracket
give curvature greater than `.9` on the whole interval `[0,.1]`.
-/

section
/-!
## Two primary-height slope bounds for the opposite edge-three contact

The transformed source label has positive third derivative on the entire
primary circle chart.  Its first derivative is therefore convex, and two
rational-height references bound it on the complete initial primary arcs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma primary_eleven_mem : (11/10:ℝ)∈Icc outerDiagonal outerAxial := by
  constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma primary_six_fifths_mem : (6/5:ℝ)∈Icc outerDiagonal outerAxial := by
  constructor <;> linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma primary_eleven_first : TPrimaryLabel.d1 (11/10)<(17/20:ℝ) := by
  have hh := TPrimaryLabel.first_chart_reference (primary_domain primary_eleven_mem)
    (l := (116430236/10^8:ℝ)) (u := (116430237/10^8:ℝ))
    (dlo := (4/5:ℝ)) (dhi := (17/20:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_six_fifths_first : TPrimaryLabel.d1 (6/5)<(1051/1000:ℝ) := by
  have hh := TPrimaryLabel.first_chart_reference (primary_domain primary_six_fifths_mem)
    (l := (101271911/10^8:ℝ)) (u := (101271912/10^8:ℝ))
    (dlo := (1:ℝ)) (dhi := (1051/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_first_upper_from_endpoints {a u m : ℝ}
    (hu : u∈Icc outerDiagonal outerAxial) (ha : a∈Icc outerDiagonal u)
    (hl : TPrimaryLabel.d1 outerDiagonal< m) (hr : TPrimaryLabel.d1 u< m) :
    TPrimaryLabel.d1 a< m := by
  have hdom {t : ℝ} (ht : t∈Icc outerDiagonal u) :
      t∈Icc outerDiagonal outerAxial := ⟨ht.1,ht.2.trans hu.2⟩
  have hc : ConcaveOn ℝ (Icc outerDiagonal u) (fun t => -TPrimaryLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (TPrimaryLabel.d1_hasDerivAt (primary_domain (hdom ht))).neg)
      (fun t ht => (TPrimaryLabel.d2_hasDerivAt (primary_domain (hdom ht))).neg)
      (fun t ht => by linarith [NegativeThree.primary_third_positive (hdom ht)])
  have hh := concave_gt_of_endpoints hc ha
    (show -m< -TPrimaryLabel.d1 outerDiagonal by linarith)
    (show -m< -TPrimaryLabel.d1 u by linarith)
  linarith

lemma primary_first_eleven {a : ℝ} (ha : a∈Icc outerDiagonal (11/10)) :
    TPrimaryLabel.d1 a<(17/20:ℝ) :=
  primary_first_upper_from_endpoints primary_eleven_mem ha
    (by linarith [NegativeThree.primary_diagonal_first]) primary_eleven_first

lemma primary_first_six_fifths {a : ℝ} (ha : a∈Icc outerDiagonal (6/5)) :
    TPrimaryLabel.d1 a<(1051/1000:ℝ) :=
  primary_first_upper_from_endpoints primary_six_fifths_mem ha
    (by linarith [NegativeThree.primary_diagonal_first]) primary_six_fifths_first

lemma fifth_mem : (1/5:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma fifth_primary_lower : (135083/100000:ℝ)<arc (1/5) := by
  have hh := shifted_chart_reference (outer_domain fifth_mem)
    (l := (185083/100000:ℝ)) (u := (185084/100000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## The whole upper-primary target-ratio arc

One scaled second-derivative bound proves concavity on `[.2,d]`.
Only the two ends of that complete arc are evaluated.  The actual
circle identity supplies both the third-derivative numerator and the
power bounds, with no subdivision of the continuous target interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.CapRatio
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
  have hd := (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
    (-(1/2))).mul_const c).fun_add (((hasDerivAt_id' (x := B)).add_const (1/2)).mul_const s)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [m]
    ring
  · simp only [V,U,W]
    ring

lemma m_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt m (-ratioD B*c) B := by
  exact ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const c).const_sub s
    |>.congr_deriv (by ring)

lemma F_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt F (first B) B := by
  have hd := (((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const s).const_add
    c).fun_sub ((LLabel.d1_hasDerivAt (outer_domain hB)).fun_mul (V_hasDerivAt hB))
  exact hd.congr_deriv (by simp only [first]; ring)

lemma first_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt first (second B) B := by
  have hd := (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).mul_const s).fun_sub
    ((LLabel.d2_hasDerivAt (outer_domain hB)).fun_mul (V_hasDerivAt hB))).fun_sub
      ((LLabel.d1_hasDerivAt (outer_domain hB)).fun_mul (m_hasDerivAt hB))
  exact hd.congr_deriv (by simp only [second]; ring)

lemma V_fifth : (11/10:ℝ)<V (1/5) ∧ V (1/5)<110173/100000 := by
  have hlo := mul_lt_mul (show (85083/100000:ℝ)<U (1/5)-1 by linarith [fifth_U.1])
    trig.1.le (by norm_num) (by linarith [fifth_U.1] : 0≤U (1/5)-1)
  have hhi := mul_lt_mul (show U (1/5)-1<(42542/50000:ℝ) by linarith [fifth_U.2])
    trig.2.1.le (by linarith [trig.1] : 0<c) (by norm_num)
  have ht := trig
  dsimp [V,W]
  constructor
  · linarith only [hlo,ht.2.2.1]
  · linarith only [hhi,ht.2.2.2]

lemma V_diagonal : (11/10:ℝ)<V outerDiagonal ∧ V outerDiagonal<4827/4000 := by
  have hd : (89921/100000:ℝ)<outerDiagonal ∧ outerDiagonal<179843/200000 := by
    constructor <;> linarith only [diagonal_fine.1,diagonal_fine.2]
  have ht := trig
  have hlo1 := mul_lt_mul (show (39921/100000:ℝ)<outerDiagonal-1/2 by linarith only [hd.1])
    ht.1.le (by norm_num) (by linarith only [hd.1] : 0≤outerDiagonal-1/2)
  have hlo2 := mul_lt_mul (show (139921/100000:ℝ)<outerDiagonal+1/2 by linarith only [hd.1])
    ht.2.2.1.le (by norm_num) (by linarith only [hd.1] : 0≤outerDiagonal+1/2)
  have hhi1 := mul_lt_mul (show outerDiagonal-1/2<(79843/200000:ℝ) by linarith only [hd.2])
    ht.2.1.le (by linarith only [ht.1] : 0<c) (by norm_num)
  have hhi2 := mul_lt_mul (show outerDiagonal+1/2<(279843/200000:ℝ) by linarith only [hd.2])
    ht.2.2.2.le (by linarith only [ht.2.2.1] : 0<s) (by norm_num)
  dsimp [V,U,W]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  constructor
  · linarith only [hlo1,hlo2]
  · linarith only [hhi1,hhi2]

lemma V_lower {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) : (11/10:ℝ)<V B := by
  have hc : ConcaveOn ℝ (Icc (1/5) outerDiagonal) V := concave_of_deriv2
    (fun t ht => V_hasDerivAt (domain ht))
    (fun t ht => m_hasDerivAt (domain ht))
    (fun t ht => by
      have hp := (outer_ratio_bounds (domain ht)).2.2.1
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (by linarith [trig.1]))
  exact concave_gt_of_endpoints hc hB V_fifth.1 V_diagonal.1

lemma m_bounds {B : ℝ} (hB : B∈Icc (1/5) outerDiagonal) :
    -(9/25:ℝ)< m B ∧ m B<9/25 := by
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
    simp only [RoleLabel.d2,LLabel]
    linarith only [hprod,hr.1]
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hmono := L_second_monotone hB hd hB.2
  have hU : U outerDiagonal=outerDiagonal+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_diagonal]
  have hp : 0<outerDiagonal+1/2 := by linarith [fine_outer_endpoint_bounds.2]
  have hcircle := UW_circle (outer_domain hd)
  rw [hU] at hcircle
  have hD : ratioD outerDiagonal=2/(outerDiagonal+1/2) := by
    simp only [ratioD]
    rw [ShortOuterOne.SameContact.arc_diagonal]
    simp only [W] at hcircle
    rw [← hcircle]
    generalize outerDiagonal+1/2=t at hp ⊢
    field_simp
    ring
  have hinv : (outerDiagonal+1/2)*(2/(outerDiagonal+1/2))=2 := by
    generalize outerDiagonal+1/2=t at hp ⊢
    field_simp
  have he : LLabel.d2 outerDiagonal*(outerDiagonal+1/2)=
      (19847/25000)*(outerDiagonal+1/2)+(94721/25000)*outerDiagonal := by
    simp only [RoleLabel.d2,LLabel]
    rw [ratio_diagonal,hD]
    linear_combination (189442/100000*outerDiagonal)*hinv
  have hhi : LLabel.d2 outerDiagonal<33/10 := by
    apply (mul_lt_mul_iff_left₀ hp).mp
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
    have huf := fifth_U.2
    dsimp [U] at huf ⊢
    linarith only [huf,hh]
  have hW : (7/10:ℝ)≤W B ∧ W B<7/5 := by
    have hd := outer_endpoint_bounds.2.2.2
    dsimp [W]
    exact ⟨by linarith only [hB.1],by linarith only [hB.2,hd]⟩
  have hQ0 : Q0=9789/2500 := rfl
  have hW2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/10) hW.1 2
  have hU2 : (U B)^2<(1713/500:ℝ) := by linarith only [hcircle,hW2,hQ0]
  have hU5 := pow_lt_pow_left₀ hUhi hu.le (by norm_num : (5:ℕ)≠0)
  have hV := V_lower hB
  have hM := m_bounds hB
  have hL := L_second_bounds hb
  have hLp := L_first_bounds hb
  have hQ : 0<Q0 := by rw [hQ0]; norm_num
  have hnum := LLabel.third_numerator (outer_domain hb)
  have hthird : LLabel.d3 B*(U B)^5=
      3*Q0*(94721/50000)*(Q0-W B/2) := by
    rw [hnum]
    simp only [LLabel]
    ring
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
        have hu' : arc B+1/2≠0 := hu.ne'
        simp only [ratioD,ratioDD,U,W]
        generalize arc B+1/2=u at hu' ⊢
        field_simp
  have hterm1 : 3*Q0*W B*s<3*Q0*(7/5)*(129/200) := by
    have ht := trig
    have hh := mul_lt_mul hW.2
      (show s≤(129/200:ℝ) by linarith only [ht.2.2.2])
      (by linarith only [ht.2.2.1] : 0<s) (by norm_num)
    have h2 := mul_lt_mul_of_pos_left hh (show (0:ℝ)<3*Q0 by linarith only [hQ])
    linarith only [h2]
  have hterm2 : 3*Q0*(94721/50000)*(Q0-7/10)*(11/10)<
      3*Q0*(94721/50000)*(Q0-W B/2)*V B := by
    have hh := mul_lt_mul (show Q0-7/10<Q0-W B/2 by linarith only [hW.2]) hV.le
      (by norm_num : (0:ℝ)<11/10) (by rw [hQ0]; linarith only [hW.2] : 0≤Q0-W B/2)
    have h2 := mul_lt_mul_of_pos_left hh (show (0:ℝ)<3*Q0*(94721/50000) by linarith only [hQ])
    linarith only [h2]
  have hmixed : -(33/10:ℝ)*(9/25)<LLabel.d2 B*m B := by
    by_cases hs : 0≤LLabel.d2 B
    · have hh := mul_le_mul_of_nonneg_left hM.1.le hs
      linarith only [hh,hL.2]
    · have hh := mul_le_mul_of_nonpos_left hM.2.le (le_of_not_ge hs)
      linarith only [hh,hL.1]
  have hterm3 : -2*LLabel.d2 B*m B*(U B)^5<
      2*(33/10)*(9/25)*(1851/1000)^5 := by
    have hh := mul_lt_mul_of_pos_right (show -2*LLabel.d2 B*m B<2*(33/10)*(9/25) by linarith only [hmixed])
      (pow_pos hu 5)
    linarith only [hh,hU5]
  have hterm4 : LLabel.d1 B*Q0*(U B)^2*c<
      (147/125)*Q0*(1713/500)*(153/200) := by
    have hp := mul_lt_mul hLp.2 hU2.le (sq_pos_of_pos hu) (by norm_num)
    have ht := trig
    have hc := mul_lt_mul hp (show c≤(153/200:ℝ) by linarith only [ht.2.1])
      (by linarith only [ht.1] : 0<c) (by norm_num)
    have hh := mul_lt_mul_of_pos_left hc hQ
    linarith only [hh]
  have hnegative : second B*(U B)^5<0 := by
    rw [hQ0] at hterm1 hterm2 hterm4 hscaled
    linarith only [hterm1,hterm2,hterm3,hterm4,hscaled]
  by_contra hc
  have hh := mul_nonneg (not_lt.mp hc) (pow_pos hu 5).le
  linarith only [hh,hnegative]

lemma fifth_positive : (41/500:ℝ)<F (1/5) := by
  have hnum := mul_lt_mul fifth_ratio.1 trig.2.2.1.le (by norm_num)
    (by linarith [fifth_ratio.1] : 0≤ratio (1/5))
  have hsub := mul_lt_mul fifth_first V_fifth.2.le
    (by linarith [V_fifth.1] : 0<V (1/5)) (by norm_num)
  dsimp [F]
  nlinarith [trig.1]

lemma diagonal_positive : (17/2500:ℝ)<F outerDiagonal := by
  have hLp : LLabel.d1 outerDiagonal<(581/500:ℝ) := by
    rw [L_first_diagonal]
    linarith [diagonal_fine.1]
  have hsub := mul_lt_mul hLp V_diagonal.2.le
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

end SquaresInCircles.Eight.SecondWord.OppositeThree.CapRatio
end
end
end

section
/-!
## The original primary contact motions for opposite edge three

Both speed identities retain the actual target circle.  The lower contact
has a source-label speed product above one everywhere; the upper product
is below one whenever the target secondary coordinate is at most `.2`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def lowerPrimarySpeed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x-(B+1/2)*Real.sin x

def upperPrimarySpeed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x+(B+1/2)*Real.sin x

lemma lowerPrimary_hasDerivAt (B x : ℝ) :
    HasDerivAt (lowerPrimary B) (lowerPrimarySpeed B x) x := by
  have hd := (((Real.hasDerivAt_sin x).const_mul (arc B+1/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (B+1/2))).const_add (1/2)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [lowerPrimarySpeed]
    ring
  · simp only [lowerPrimary]
    ring

lemma upperPrimary_hasDerivAt (B x : ℝ) :
    HasDerivAt (upperPrimary B) (-upperPrimarySpeed B x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (B+1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (arc B-1/2))).const_add (1/2)
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [upperPrimarySpeed]
    ring
  · simp only [upperPrimary]
    ring

lemma lowerPrimarySpeed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<lowerPrimarySpeed B x := by
  have hs := ShortOuterOne.SameContact.arc_state hB
  have ht := positive_trig hx
  have hsc : Real.sin x<Real.cos x := by linarith [ht.1,ht.2.2.2.1]
  have hp := mul_pos (show 0<B+1/2 by linarith [hB.1]) (sub_pos.mpr hsc)
  have hn := mul_nonneg (sub_nonneg.mpr hs.2.1) (by linarith [ht.1] : 0≤Real.cos x)
  dsimp [lowerPrimarySpeed]
  nlinarith

lemma upperPrimarySpeed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<upperPrimarySpeed B x := by
  have hs := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hB)
  have ht := positive_trig hx
  have hp := mul_pos (show 0<arc B-1/2 by linarith [hs.1,fine_outer_endpoint_bounds.2])
    (show 0<Real.cos x by linarith [ht.1])
  have hn := mul_nonneg (show 0≤B+1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [upperPrimarySpeed]
  linarith

lemma lowerPrimary_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (lowerPrimary B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (lowerPrimary_hasDerivAt B t).continuousAt.continuousWithinAt)
    (fun t _ => lowerPrimary_hasDerivAt B t)
    (fun _ ht => (lowerPrimarySpeed_positive hB (Ioo_subset_Icc_self ht)).le)

lemma upperPrimary_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (upperPrimary B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (upperPrimary_hasDerivAt B t).continuousAt.continuousWithinAt)
    (fun t _ => upperPrimary_hasDerivAt B t)
    (fun t ht => by linarith [upperPrimarySpeed_positive hB (Ioo_subset_Icc_self ht)])

lemma lowerPrimary_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (lowerPrimary B x-1/2)^2+(lowerPrimarySpeed B x)^2=Q0 := by
  have hc := (ShortOuterOne.SameContact.arc_state hB).2.2
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [lowerPrimary,lowerPrimarySpeed]
  linear_combination hc+((arc B+1/2)^2+(B+1/2)^2)*ht

lemma upperPrimary_norm {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    (upperPrimary B x-1/2)^2+(upperPrimarySpeed B x)^2=Q0-2*arc B := by
  have hc := (ShortOuterOne.SameContact.arc_state hB).2.2
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [upperPrimary,upperPrimarySpeed]
  linear_combination hc+((arc B-1/2)^2+(B+1/2)^2)*ht

lemma lower_primary_speed_paid {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10))
    (ha : lowerPrimary B x∈Icc outerDiagonal outerAxial) :
    1<TPrimaryLabel.d1 (lowerPrimary B x)*lowerPrimarySpeed B x := by
  have hv := lowerPrimarySpeed_positive hB hx
  have hn := lowerPrimary_norm hB x
  have hm := NegativeThree.primary_first_lower ha
  have hz : 0<lowerPrimary B x-1/2 ∧ lowerPrimary B x-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hs : (7/4:ℝ)<lowerPrimarySpeed B x := by
    norm_num [Q0] at hn
    nlinarith
  have hh := mul_lt_mul hm hs.le (by norm_num : (0:ℝ)<7/4)
    (by linarith [hm] : 0≤TPrimaryLabel.d1 (lowerPrimary B x))
  nlinarith

lemma upper_primary_speed_paid {B x : ℝ} (hB : B∈Icc 0 (1/5))
    (hx : x∈Icc 0 (7/10))
    (ha : upperPrimary B x∈Icc outerDiagonal (6/5)) :
    TPrimaryLabel.d1 (upperPrimary B x)*upperPrimarySpeed B x<1 := by
  have hBfull : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans fifth_mem.2⟩
  have hv := upperPrimarySpeed_positive hBfull hx
  have hn := upperPrimary_norm hBfull x
  have hA := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hBfull) (outer_domain fifth_mem) hB.2
  have hAlo : (135083/100000:ℝ)<arc B := fifth_primary_lower.trans_le hA
  have haFull : upperPrimary B x∈Icc outerDiagonal outerAxial :=
    ⟨ha.1,ha.2.trans primary_six_fifths_mem.2⟩
  have hmlo : 0<TPrimaryLabel.d1 (upperPrimary B x) := by
    linarith [NegativeThree.primary_first_lower haFull]
  by_cases hsmall : upperPrimary B x≤11/10
  · have hM := primary_first_eleven ⟨ha.1,hsmall⟩
    have hz : (399/1000:ℝ)<upperPrimary B x-1/2 := by
      linarith [ha.1,fine_outer_endpoint_bounds.2]
    have hs : upperPrimarySpeed B x<(103/100:ℝ) := by
      norm_num [Q0] at hn
      nlinarith
    have hh := mul_lt_mul hM hs.le hv (by norm_num : (0:ℝ)≤17/20)
    norm_num at hh
    linarith
  · have hM := primary_first_six_fifths ha
    have hz : (3/5:ℝ)≤upperPrimary B x-1/2 := by linarith
    have hs : upperPrimarySpeed B x<(37/40:ℝ) := by
      norm_num [Q0] at hn
      nlinarith
    have hh := mul_lt_mul hM hs.le hv (by norm_num : (0:ℝ)≤1051/1000)
    norm_num at hh
    linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## The physical upper-primary inverse motion

The inverse rotation is the same explicit circle function as for edge
two.  Here the literal edge-three target label is paid by the whole-arc
cap-ratio inequality.  The proof identifies every inverse point with
its original primary contact before applying that inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperInverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

abbrev X := OppositeTwo.PrimaryInverse.X
abbrev F := OppositeTwo.PrimaryInverse.F
abbrev shifts := OppositeTwo.PrimaryInverse.shifts
abbrev speed := OppositeTwo.PrimaryInverse.speed
abbrev radius := OppositeTwo.PrimaryInverse.radius
def quotient (B x : ℝ) : ℝ :=
  (Real.cos x+ratio B*Real.sin x)/upperPrimarySpeed B x

lemma primary_shift {a b : ℝ} (hs : OuterState a b) : a-1/2∈shifts := by
  have ha := NegativeTwo.primary_mem hs
  constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]

lemma quotient_hasDerivAt {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (quotient B) (-ratio B/(upperPrimarySpeed B x)^2) x := by
  have hv := upperPrimarySpeed_positive hB hx
  have hu : arc B+1/2≠0 := (U_positive (outer_domain hB)).ne'
  have hspeed : HasDerivAt (upperPrimarySpeed B)
      (-(arc B-1/2)*Real.sin x+(B+1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (B+1/2))).congr_deriv (by ring)
  have hd := ((Real.hasDerivAt_cos x).fun_add
    ((Real.hasDerivAt_sin x).const_mul (ratio B))).fun_div hspeed hv.ne'
  refine hd.congr_deriv ?_
  congr 1
  have hr : ratio B*(arc B+1/2)=B+1/2 := div_mul_cancel₀ (B+1/2) hu
  have ht := Real.sin_sq_add_cos_sq x
  simp only [upperPrimarySpeed]
  linear_combination (ratio B*(arc B-1/2)-(B+1/2))*ht+hr

lemma quotient_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (quotient B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t ht => (quotient_hasDerivAt hB ht).continuousAt.continuousWithinAt)
    (fun t ht => quotient_hasDerivAt hB (Ioo_subset_Icc_self ht))
    (fun t ht => by
      exact div_nonpos_of_nonpos_of_nonneg
        (by linarith [(outer_ratio_bounds hB).1]) (sq_nonneg _))

lemma quotient_paid {B x : ℝ} (hB : B∈Icc (1/5) outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : LLabel.d1 B<quotient B x := by
  have hb := CapRatio.domain hB
  have hcap := CapRatio.positive hB
  have hv := upperPrimarySpeed_positive hb (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hV : CapRatio.V B=upperPrimarySpeed B (7/10) := by
    dsimp [CapRatio.V,CapRatio.c,CapRatio.s,upperPrimarySpeed,U,W]
    ring
  have hp : LLabel.d1 B<quotient B (7/10) := by
    apply (lt_div_iff₀ hv).2
    dsimp [CapRatio.F,CapRatio.c,CapRatio.s] at hcap
    rw [hV] at hcap
    linarith
  exact hp.trans_le (quotient_antitone hb hx (by norm_num) hx.2)

lemma X_monotone {z : ℝ} (hz : z∈shifts) :
    MonotoneOn (X z) (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t ht => (OppositeTwo.PrimaryInverse.X_source_hasDerivAt ht hz).continuousAt.continuousWithinAt)
    (fun t ht => OppositeTwo.PrimaryInverse.X_source_hasDerivAt (Ioo_subset_Icc_self ht) hz)
  intro t ht
  have hb := Ioo_subset_Icc_self ht
  have hd := OppositeTwo.PrimaryInverse.data hb hz
  have hu := U_positive (outer_domain hb)
  have hq := NegativeTwo.Inverse.actual_q_positive hb
  have hfactor := NegativeTwo.Inverse.factor_lower hu (by linarith : 0<NegativeTwo.Inverse.q (U t))
  have hratio := outer_ratio_bounds hb
  have hn : 0≤z*ratio t/(NegativeTwo.Inverse.q (U t)*speed z t) := by
    apply div_nonneg (mul_nonneg hz.1 (by linarith [hratio.1]))
    exact mul_nonneg (by linarith) hd.2.2.1.le
  dsimp [F,OppositeTwo.PrimaryInverse.F]
  linarith

lemma X_nonnegative {B z : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z≤W B) : 0≤X z B := by
  have hr := (OppositeTwo.PrimaryInverse.data hB
    (show (0:ℝ)∈shifts by norm_num [shifts,OppositeTwo.PrimaryInverse.shifts])).1
  have hquot := div_le_div_of_nonneg_right hz (show 0≤radius B by linarith)
  have hh := Real.arcsin_le_arcsin hquot
  have ha := OppositeTwo.PrimaryInverse.aligned hB (z := W B) rfl
  dsimp [X,OppositeTwo.PrimaryInverse.X,OppositeTwo.PrimaryInverse.inverseAngle,
    NegativeTwo.ContactInverse.angle] at ha ⊢
  linarith

lemma X_contact {B z : ℝ} (hB : B∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    upperPrimary B (X z B)=z+1/2 := by
  have hd := OppositeTwo.PrimaryInverse.data hB hz
  have hr : 0<radius B := by linarith [hd.1]
  have ha := OppositeTwo.PrimaryInverse.argument_bounds hB hz
  have htr := NegativeTwo.ContactInverse.base_trig hB
  have hs := Real.sin_arcsin ha.1.le ha.2.le
  dsimp [upperPrimary,X,OppositeTwo.PrimaryInverse.X,
    OppositeTwo.PrimaryInverse.inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,Real.sin_add,Real.cos_add,
    htr.1,htr.2,hs]
  dsimp [U,W]
  field_simp [hr.ne']
  have hc := UW_circle (outer_domain hB)
  have hq := hd.2.1
  dsimp [OppositeTwo.Inverse.q,NegativeTwo.Inverse.q,U,W] at hc hq
  have hc' := congrArg (fun v : ℝ => z*v) hc
  have hq' := congrArg (fun v : ℝ => z*v) hq
  nlinarith [hc',hq']

lemma physical_speed {B z x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈shifts) (hx : x∈Icc 0 (7/10))
    (hc : upperPrimary B x=z+1/2) : speed z B=upperPrimarySpeed B x := by
  have hd := OppositeTwo.PrimaryInverse.data hB hz
  have hp := upperPrimarySpeed_positive hB hx
  have hn := upperPrimary_norm hB x
  rw [hc] at hn
  have hq := hd.2.2.2
  dsimp [OppositeTwo.Inverse.q,NegativeTwo.Inverse.q,U] at hq
  nlinarith [hd.2.2.1]

lemma physical_F {B z x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hz : z∈shifts) (hx : x∈Icc 0 (7/10))
    (hc : upperPrimary B x=z+1/2) : F z B=quotient B x := by
  have he := physical_speed hB hz hx hc
  have hu := U_positive (outer_domain hB)
  have hv := upperPrimarySpeed_positive hB hx
  have hq : 0<NegativeTwo.Inverse.q (U B) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hB]
  have hzform : z=W B*Real.cos x-(U B-1)*Real.sin x := by
    dsimp [upperPrimary,U,W] at hc ⊢
    linarith
  have hvform : upperPrimarySpeed B x=(U B-1)*Real.cos x+W B*Real.sin x := by
    dsimp [upperPrimarySpeed,U,W]
    ring
  change (Q0-U B)/(U B*NegativeTwo.Inverse.q (U B))+
      z*(W B/U B)/(NegativeTwo.Inverse.q (U B)*speed z B)=
        (Real.cos x+(W B/U B)*Real.sin x)/upperPrimarySpeed B x
  rw [he,hzform]
  field_simp [hu.ne',hq.ne',hv.ne']
  rw [hvform]
  dsimp [NegativeTwo.Inverse.q]
  linear_combination Real.cos x*(UW_circle (outer_domain hB))

lemma inverse_paid {B z : ℝ} (hB : B∈Icc (1/5) outerDiagonal)
    (hz : z∈shifts) (hx : X z B∈Icc 0 (7/10)) : LLabel.d1 B<F z B := by
  rw [physical_F (CapRatio.domain hB) hz hx (X_contact (CapRatio.domain hB) hz)]
  exact quotient_paid hB hx

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperInverse
end
end
end

section
/-!
## The full late source motion for the other upper-primary owner

On `[.1,.4]` the difference `V' - T'` is concave and positive at both
ends, so the existing physical primary ratio pays `T'` as well.  On
the remaining arc the global inverse-factor floor already suffices.
These two derivative regimes give one monotone source motion from
every source coordinate at least `.1`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma tenth_mem : (1/10:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma two_fifths_mem : (2/5:ℝ)∈Icc 0 outerDiagonal := by
  constructor <;> linarith [fine_outer_endpoint_bounds.2]

lemma tenth_slopes : TLabel.d1 (1/10)<(118/125:ℝ) ∧
    (51/50:ℝ)<VLabel.d1 (1/10) := by
  have ht := TLabel.first_chart_reference (outer_domain tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (9/10:ℝ)) (dhi := (118/125:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  have hv := VLabel.first_chart_reference (outer_domain tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (51/50:ℝ)) (dhi := (11/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact ⟨ht.2,hv.1⟩

lemma two_fifths_slopes : TLabel.d1 (2/5)<(677/1000:ℝ) ∧
    (209/250:ℝ)<VLabel.d1 (2/5) := by
  have ht := TLabel.first_chart_reference (outer_domain two_fifths_mem)
    (l := (176227126/10^8:ℝ)) (u := (176227127/10^8:ℝ))
    (dlo := (3/5:ℝ)) (dhi := (677/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  have hv := VLabel.first_chart_reference (outer_domain two_fifths_mem)
    (l := (176227126/10^8:ℝ)) (u := (176227127/10^8:ℝ))
    (dlo := (209/250:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact ⟨ht.2,hv.1⟩

lemma source_comparison {b : ℝ} (hb : b∈Icc (1/10) (2/5)) :
    TLabel.d1 b<VLabel.d1 b := by
  have hdom {t : ℝ} (ht : t∈Icc (1/10) (2/5)) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2.trans two_fifths_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (1/10) (2/5)) (fun t => VLabel.d1 t-TLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub
        (TLabel.d1_hasDerivAt (outer_domain (hdom ht))))
      (fun t ht => (VLabel.d2_hasDerivAt (outer_domain (hdom ht))).sub
        (TLabel.d2_hasDerivAt (outer_domain (hdom ht))))
      (fun t ht => by linarith [V_third_negative (hdom ht),T_third_lower (hdom ht)])
  have hh := concave_gt_of_endpoints hc hb
    (show 0<VLabel.d1 (1/10)-TLabel.d1 (1/10) by linarith [tenth_slopes.1,tenth_slopes.2])
    (show 0<VLabel.d1 (2/5)-TLabel.d1 (2/5) by
      linarith [two_fifths_slopes.1,two_fifths_slopes.2])
  linarith

lemma source_first_late {b : ℝ} (hb : b∈Icc (2/5) outerDiagonal) :
    TLabel.d1 b<(387/500:ℝ) := by
  have hdom {t : ℝ} (ht : t∈Icc (2/5) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc (2/5) outerDiagonal) (fun t => -TLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (TLabel.d1_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => (TLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => by linarith [T_third_lower (hdom ht)])
  have hh := concave_gt_of_endpoints hc hb
    (show -(387/500:ℝ)< -TLabel.d1 (2/5) by linarith [two_fifths_slopes.1])
    (show -(387/500:ℝ)< -TLabel.d1 outerDiagonal by
      rw [T_first_diagonal]
      linarith [fine_outer_endpoint_bounds.2])
  linarith

theorem source_ratio_paid {b z : ℝ} (hb : b∈Icc (1/10) outerDiagonal)
    (hz : z∈UpperInverse.shifts) (hdiag : outerDiagonal-1/2≤z) :
    TLabel.d1 b<UpperInverse.F z b := by
  have hbf : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  by_cases hearly : b≤2/5
  · have hT := source_comparison ⟨hb.1,hearly⟩
    exact hT.trans (OppositeTwo.PrimaryInverse.F_paid hbf hz hdiag)
  · have hT := source_first_late ⟨by linarith,hb.2⟩
    have hu := U_positive (outer_domain hbf)
    have hq : 0<NegativeTwo.Inverse.q (U b) := by
      linarith [NegativeTwo.Inverse.actual_q_positive hbf]
    have hf := NegativeTwo.Inverse.factor_lower hu hq
    have hd := OppositeTwo.PrimaryInverse.data hbf hz
    have hn : 0≤z*ratio b/(NegativeTwo.Inverse.q (U b)*UpperInverse.speed z b) :=
      div_nonneg (mul_nonneg hz.1 (by linarith [(outer_ratio_bounds hbf).1]))
        (mul_nonneg hq.le hd.2.2.1.le)
    dsimp [UpperInverse.F,OppositeTwo.PrimaryInverse.F]
    linarith

lemma source_cost_monotone {z : ℝ} (hz : z∈UpperInverse.shifts)
    (hdiag : outerDiagonal-1/2≤z) :
    MonotoneOn (fun b => UpperInverse.X z b-T b) (Icc (1/10) outerDiagonal) := by
  have hdom {t : ℝ} (ht : t∈Icc (1/10) outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨by linarith [ht.1],ht.2⟩
  have hd {t : ℝ} (ht : t∈Icc (1/10) outerDiagonal) :
      HasDerivAt (fun b => UpperInverse.X z b-T b) (UpperInverse.F z t-TLabel.d1 t) t := by
    convert (OppositeTwo.PrimaryInverse.X_source_hasDerivAt (hdom ht) hz).sub
      (TLabel.outer_hasDerivAt (outer_domain (hdom ht))) using 1
    rfl
  exact monoOn_of_hasDeriv_nonneg
    (fun t ht => (hd ht).continuousAt.continuousWithinAt)
    (fun t ht => hd (Ioo_subset_Icc_self ht))
    (fun t ht => by linarith [source_ratio_paid (Ioo_subset_Icc_self ht) hz hdiag])

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperTarget
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

abbrev z := OppositeTwo.TargetRatio.z
abbrev speed := OppositeTwo.TargetRatio.speed
def value (b : ℝ) : ℝ :=
  Real.pi/2+UpperInverse.X z b-T b-L outerDiagonal
def first (b : ℝ) : ℝ := OppositeTwo.TargetRatio.F b-TLabel.d1 b
def second (b : ℝ) : ℝ := OppositeTwo.TargetRatio.first b-TLabel.d2 b

lemma z_mem : z∈UpperInverse.shifts := by
  have hh := OppositeTwo.TargetRatio.z_bounds
  constructor <;> linarith [hh.1,hh.2]

lemma inverse_first (b : ℝ) : UpperInverse.F z b=OppositeTwo.TargetRatio.F b := by
  rw [OppositeTwo.TargetRatio.F_formula]
  rfl

lemma value_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt value (first b) b := by
  have hd := (((OppositeTwo.PrimaryInverse.X_source_hasDerivAt hb z_mem).const_add
    (Real.pi/2)).fun_sub (TLabel.outer_hasDerivAt (outer_domain hb))).sub_const (L outerDiagonal)
  refine hd.congr_deriv ?_
  simp only [first]
  rw [← inverse_first]

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b := by
  convert (OppositeTwo.TargetRatio.F_hasDerivAt hb).sub
    (TLabel.d1_hasDerivAt (outer_domain hb)) using 1 <;> rfl

lemma early_domain {b : ℝ} (hb : b∈Icc 0 (1/10)) : b∈Icc 0 outerDiagonal :=
  ⟨hb.1,hb.2.trans UpperTarget.tenth_mem.2⟩

lemma tenth_U : (94281/50000:ℝ)<U (1/10) ∧ U (1/10)<47141/25000 :=
  shifted_chart_reference (outer_domain UpperTarget.tenth_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma early_ratio {b : ℝ} (hb : b∈Icc 0 (1/10)) : ratio b<(319/1000:ℝ) := by
  have hB := early_domain hb
  have hu := U_positive (outer_domain hB)
  have hmono := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hB) (outer_domain UpperTarget.tenth_mem) hb.2
  have hU : (94281/50000:ℝ)<U b := by
    have hh := tenth_U.1
    dsimp [U] at hh ⊢
    linarith
  change (b+1/2)/U b<(319/1000:ℝ)
  apply (div_lt_iff₀ hu).2
  nlinarith [hb.2]

lemma ratioD_floor {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hp := pow_le_pow_left₀ hu.le (UW_bounds hb).2.1.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at *
  nlinarith

lemma early_brace {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    0<NegativeTwo.Inverse.brace (U b) (ratio b) (speed b) := by
  have hB := early_domain hb
  have hr := outer_ratio_bounds hB
  have hrhi := early_ratio hb
  have hr2 : (ratio b)^2<(319/1000:ℝ)^2 := by nlinarith [hr.1]
  have hq := NegativeTwo.Inverse.actual_q_positive hB
  have hq0 : 0<NegativeTwo.Inverse.q (U b) := by linarith
  have hv := OppositeTwo.TargetRatio.speed_lower hB
  have hv2 : (481/500:ℝ)^2<(speed b)^2 := by nlinarith
  have hfirst : 2*(ratio b)^2/NegativeTwo.Inverse.q (U b)<47/250 := by
    apply (div_lt_iff₀ hq0).2
    nlinarith
  have hsecond : (ratio b)^2/(speed b)^2<11/100 := by
    apply (div_lt_iff₀ (sq_pos_of_pos (show 0<speed b by linarith))).2
    nlinarith
  have hD := ratioD_floor hB
  change 0<ratioD b-2*(ratio b)^2/NegativeTwo.Inverse.q (U b)-
    (ratio b)^2/(speed b)^2
  linarith

lemma tenth_second : TLabel.d2 (1/10)<(-(1169/1000):ℝ) := by
  have hh := TLabel.second_chart_reference (outer_domain UpperTarget.tenth_mem)
    (l := (188562986/10^8:ℝ)) (u := (188562987/10^8:ℝ))
    (dlo := (-2:ℝ)) (dhi := (-(1169/1000):ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma early_curvature {b : ℝ} (hb : b∈Icc 0 (1/10)) : (9/10:ℝ)<second b := by
  have hB := early_domain hb
  have hheight := OppositeTwo.Inverse.actual_height_derivative hB
  have hweight := (OppositeTwo.TargetRatio.weight_bounds hB).1
  have hbrace := early_brace hb
  have hproduct := mul_pos hweight hbrace
  have hT := (T_second_monotone hB UpperTarget.tenth_mem hb.2).trans_lt tenth_second
  change (9/10:ℝ)< -ratio b*PJCritical.heightFactorD (U b)+
    z/(NegativeTwo.Inverse.q (U b)*speed b)*
      NegativeTwo.Inverse.brace (U b) (ratio b) (speed b)-TLabel.d2 b
  linarith

lemma late_monotone : MonotoneOn value (Icc (1/10) outerDiagonal) := by
  have hM := UpperTarget.source_cost_monotone z_mem (by rfl)
  intro b hb B hB h
  have hh := hM hb hB h
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree.UpperDiagonal
end
end
end
