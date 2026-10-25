module

public import SquaresInCircles.Eight.Words.Second.Mixed.LHeightGrowth
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.ZeroCurve

/-!
# Eight squares: complete lower bounds for the shared L primary zero-source curve

A single quadratic tangent controls the middle minimum. Concavity of
the first derivative covers the rest of that middle arc. The complete
late arc is concave and has both endpoint costs above .8978.
-/

section
/-!
## Two affine lower bounds for the L height label

A chord controls the whole concave height range below 1.6. Above 1.6
the global first-derivative lower bound gives one affine minorant.
These two explicit lines suffice for the complete positive-core corner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LHeightAffine
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

lemma references : -(800617/1000000:ℝ)<LHeight.eval (171/125) ∧
    -(277727/500000:ℝ)<LHeight.eval (8/5) := by
  have h0 := root_cage (u := (171/125:ℝ))
    (l := (1429746830736/1000000000000:ℝ)) (r := (1429746830737/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have h1 := root_cage (u := (8/5:ℝ))
    (l := (1164302366226/1000000000000:ℝ)) (r := (1164302366227/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  constructor <;> dsimp [HeightLabel.eval,LHeight] <;> nlinarith [h0.2,h1.2]

theorem low {u : ℝ} (hu : u∈Icc (171/125:ℝ) (8/5)) :
    (132/125)*u-89809/40000<LHeight.eval u := by
  have hdom {y : ℝ} (hy : y∈Icc (171/125:ℝ) (8/5)) : y∈LHeightBounds.heights :=
    ⟨hy.1,by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (171/125:ℝ) (8/5))
      (fun y => LHeight.eval y-(132/125)*y+89809/40000) :=
    concave_of_deriv2 (f' := fun y => LHeight.d1 y-132/125)
      (fun y hy => (((LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom hy))).sub
        ((hasDerivAt_id y).const_mul (132/125))).add_const (89809/40000)).congr_deriv (by ring))
      (fun y hy => (LHeight.d1_hasDerivAt (LHeightBounds.domain (hdom hy))).sub_const (132/125))
      (fun y hy => (LHeightBounds.second_negative_below (hdom hy) hy.2).le)
  have hh := concave_gt_of_endpoints hc hu
    (show (0:ℝ)<LHeight.eval (171/125)-(132/125)*(171/125)+89809/40000 by linarith [references.1])
    (show (0:ℝ)<LHeight.eval (8/5)-(132/125)*(8/5)+89809/40000 by linarith [references.2])
  linarith

theorem high {u : ℝ} (hu : u∈Icc (8/5:ℝ) (383/200)) :
    (19/20)*u-1037727/500000<LHeight.eval u := by
  have hdom {y : ℝ} (hy : y∈Icc (8/5:ℝ) (383/200)) : y∈LHeightBounds.heights :=
    ⟨by linarith [hy.1],hy.2⟩
  have hm : MonotoneOn (fun y => LHeight.eval y-(19/20)*y) (Icc (8/5:ℝ) (383/200)) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => ((LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom hy))).sub
        ((hasDerivAt_id y).const_mul (19/20))).continuousAt.continuousWithinAt)
      (fun y hy => (LHeight.eval_hasDerivAt (LHeightBounds.domain (hdom (Ioo_subset_Icc_self hy)))).sub
        ((hasDerivAt_id y).const_mul (19/20)))
      (fun y hy => by linarith [LHeightBounds.first_lower (hdom (Ioo_subset_Icc_self hy))])
  have hh := hm (by norm_num) hu hu.1
  linarith [references.2]

end SquaresInCircles.Eight.SecondWord.LHeightAffine
end
end
end

section
/-!
## The shared L-label primary zero-source curve

The same exact harmonic height serves both core signs. On the complete
middle arc its cost has negative third derivative. On the entire late
arc its second derivative is negative directly from the height label;
no quotient-of-radial-derivatives estimate is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

abbrev m := PrimaryZero.m
abbrev w := PrimaryZero.v
abbrev U := PrimaryZero.U
abbrev V := PrimaryZero.V
abbrev b := PrimaryZero.b

def angles : Set ℝ := Icc (33/25) (Real.pi/2)
def middle : Set ℝ := Icc (33/25) (37/25)
def late : Set ℝ := Icc (73/50) (Real.pi/2)
def e : ℝ := 11021/50000-(8623/25000)*(7/12)
def K (φ : ℝ) : ℝ := φ-e+LHeight.eval (U φ)
def KD (φ : ℝ) : ℝ := 1-LHeight.d1 (U φ)*w φ
def KDD (φ : ℝ) : ℝ := LHeight.d2 (U φ)*(w φ)^2-LHeight.d1 (U φ)*m φ
def KDDD (φ : ℝ) : ℝ := w φ*(-LHeight.d3 (U φ)*(w φ)^2+
  3*LHeight.d2 (U φ)*m φ+LHeight.d1 (U φ))

lemma initial_trig :
    (96871509/100000000:ℝ)≤Real.sin (33/25) ∧ Real.sin (33/25)≤96871511/100000000 ∧
    (4963509/20000000:ℝ)≤Real.cos (33/25) ∧ Real.cos (33/25)≤12408773/50000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (33/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (33/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (33/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (33/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma middle_terminal_trig :
    (1244851/1250000:ℝ)≤Real.sin (37/25) ∧ Real.sin (37/25)≤49794043/50000000 ∧
    (4533581/50000000:ℝ)≤Real.cos (37/25) ∧ Real.cos (37/25)≤9067163/100000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (37/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (37/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (37/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (37/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma middle_subset : middle⊆angles := fun φ hφ =>
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
lemma late_subset : late⊆angles := fun φ hφ => ⟨by linarith [hφ.1],hφ.2⟩

lemma sine_monotone : MonotoneOn Real.sin angles := by
  intro x hx y hy hxy
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos]) hy.2 hxy

lemma cosine_antitone : AntitoneOn Real.cos angles := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_cos x
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2,Real.pi_pos])
    linarith

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    (24/25:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<1/4 := by
  have hleft : (33/25:ℝ)∈angles := ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩
  have hright : Real.pi/2∈angles := ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩
  have hs := sine_monotone hleft hφ hφ.1
  have hc := cosine_antitone hleft hφ hφ.1
  have hc0 := cosine_antitone hφ hright hφ.2
  norm_num at hc0
  exact ⟨by linarith [initial_trig.1],Real.sin_le_one φ,hc0,by linarith [initial_trig.2.2.2]⟩

lemma w_positive {φ : ℝ} (hφ : φ∈angles) : 0<w φ := by
  have ht := trig hφ
  dsimp [w,PrimaryZero.v]
  linarith [ht.1,ht.2.2.2]

lemma U_antitone : AntitoneOn U angles :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => (PrimaryZero.U_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => PrimaryZero.U_hasDerivAt φ)
    (fun _ hφ => neg_nonpos.mpr (w_positive (Ioo_subset_Icc_self hφ)).le)

lemma U_bounds {φ : ℝ} (hφ : φ∈angles) : (3/2:ℝ)≤U φ ∧ U φ<(44/25:ℝ) := by
  have hl := U_antitone hφ
    (show Real.pi/2∈angles from ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩) hφ.2
  have hu := U_antitone
    (show (33/25:ℝ)∈angles from ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩) hφ hφ.1
  have hinit : U (33/25)<(44/25:ℝ) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [initial_trig.2.1,initial_trig.2.2.2]
  norm_num [U,PrimaryZero.U,PrimaryZero.m] at hl
  exact ⟨hl,hu.trans_lt hinit⟩

lemma height_domain {φ : ℝ} (hφ : φ∈angles) : U φ∈LHeightBounds.heights :=
  ⟨by linarith [(U_bounds hφ).1],by linarith [(U_bounds hφ).2]⟩

lemma middle_height {φ : ℝ} (hφ : φ∈middle) : U φ∈LHeightBounds.zero := by
  have hh := U_antitone (middle_subset hφ)
    (middle_subset (show (37/25:ℝ)∈middle by norm_num [middle])) hφ.2
  have hb : (159/100:ℝ)<U (37/25) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [middle_terminal_trig.1,middle_terminal_trig.2.2.1]
  exact ⟨by linarith,(U_bounds (middle_subset hφ)).2.le⟩

lemma late_height {φ : ℝ} (hφ : φ∈late) : U φ∈Icc (3/2) (81/50) := by
  have hh := U_antitone
    (show (73/50:ℝ)∈angles from ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩)
    (late_subset hφ) hφ.1
  have hc := HighOrderTaylor.cos_le_C12 (x := (73/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc
  have hU : U (73/50)<(81/50:ℝ) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [Real.sin_le_one (73/50:ℝ)]
  exact ⟨(U_bounds (late_subset hφ)).1,hh.trans hU.le⟩

lemma harmonic_circle (φ : ℝ) : (m φ)^2+(w φ)^2=(205/144:ℝ) := PrimaryZero.mv_circle φ

lemma K_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt K (KD φ) φ := by
  exact (((hasDerivAt_id φ).sub_const e).fun_add
    ((LHeight.eval_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
      (PrimaryZero.U_hasDerivAt φ))).congr_deriv (by simp only [KD,w]; ring)

lemma KD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KD (KDD φ) φ := by
  exact ((((LHeight.d1_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
    (PrimaryZero.U_hasDerivAt φ)).fun_mul (PrimaryZero.v_hasDerivAt φ)).const_sub 1).congr_deriv
    (by simp only [KDD,m,w,Function.comp_apply]; ring)

lemma KDD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KDD (KDDD φ) φ := by
  exact ((((LHeight.d2_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
    (PrimaryZero.U_hasDerivAt φ)).fun_mul ((PrimaryZero.v_hasDerivAt φ).fun_pow 2)).fun_sub
      (((LHeight.d1_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
        (PrimaryZero.U_hasDerivAt φ)).fun_mul (PrimaryZero.m_hasDerivAt φ))).congr_deriv
    (by simp only [KDDD,m,w,Nat.cast_ofNat,Function.comp_apply]; ring)

lemma KDDD_negative {φ : ℝ} (hφ : φ∈middle) : KDDD φ<0 := by
  have hu := middle_height hφ
  have hm : m φ=U φ-1 := by dsimp [m,U,PrimaryZero.U]; ring
  have hm0 : 0≤ m φ := by rw [hm]; linarith [hu.1]
  have hmU : m φ≤(19/25:ℝ) := by rw [hm]; linarith [hu.2]
  have hs := pow_le_pow_left₀ hm0 hmU 2
  have hc := harmonic_circle φ
  have hw : (1/2:ℝ)<(w φ)^2 := by nlinarith
  have hwm : 3*m φ<5*(w φ)^2 := by nlinarith
  have hd := LHeightBounds.third_dominates hu
  have hf := LHeightBounds.first_lower (LHeightBounds.zero_subset hu)
  have hfirst := mul_pos (show 0<LHeight.d1 (U φ) by linarith)
    (show 0<2*(w φ)^2-1 by linarith)
  have hp := mul_lt_mul_of_pos_right hd (show 0<(w φ)^2 by linarith)
  have hlast : -LHeight.d3 (U φ)*(w φ)^2+3*LHeight.d2 (U φ)*m φ+LHeight.d1 (U φ)<0 := by
    by_cases h2 : 0≤LHeight.d2 (U φ)
    · rw [max_eq_left h2] at hp
      have hsecond := mul_nonneg h2 (show 0≤5*(w φ)^2-3*m φ by linarith)
      nlinarith
    · rw [max_eq_right (not_le.mp h2).le] at hp
      have hsecond := mul_nonpos_of_nonpos_of_nonneg (not_le.mp h2).le hm0
      nlinarith
  exact mul_neg_of_pos_of_neg (w_positive (middle_subset hφ)) hlast

lemma KDD_antitone : AntitoneOn KDD middle :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hφ => (KDD_hasDerivAt (middle_subset hφ)).continuousAt.continuousWithinAt)
    (fun _ hφ => KDD_hasDerivAt (middle_subset (Ioo_subset_Icc_self hφ)))
    (fun _ hφ => (KDDD_negative (Ioo_subset_Icc_self hφ)).le)

lemma KDD_negative_late {φ : ℝ} (hφ : φ∈late) : KDD φ<0 := by
  have hu := late_height hφ
  have hdd := LHeightBounds.second_upper_late hu
  have hd := LHeightBounds.first_lower (height_domain (late_subset hφ))
  have hm : (1/2:ℝ)≤ m φ := by dsimp [m,U,PrimaryZero.U] at hu; linarith [hu.1]
  have hc := harmonic_circle φ
  have hs : (w φ)^2≤(205/144:ℝ) := by nlinarith [sq_nonneg (m φ)]
  have hp := mul_le_mul_of_nonneg_right hdd.le (sq_nonneg (w φ))
  have hq := mul_le_mul hd.le hm (by norm_num : (0:ℝ)≤1/2)
    (show 0≤LHeight.d1 (U φ) by linarith)
  dsimp [KDD]
  nlinarith

lemma V_positive {φ : ℝ} (hφ : φ∈angles) : 0<V φ :=
  root_pos (LHeightBounds.domain (height_domain hφ))

lemma physical {φ : ℝ} (hφ : φ∈angles) : OuterState (U φ-1/2) (b φ) := by
  have hu := U_bounds hφ
  have hp := V_positive hφ
  have hc : (V φ)^2=Q0-(U φ)^2 := root_sq (LHeightBounds.domain (height_domain hφ))
  have hsqL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 2
  have hsqU := pow_le_pow_left₀ (by linarith [hu.1] : 0≤U φ) hu.2.le 2
  have hb : 0≤b φ := by dsimp [b,PrimaryZero.b]; norm_num [Q0] at hc; nlinarith
  refine ⟨hb,?_,?_⟩
  · dsimp [b,PrimaryZero.b]
    norm_num [Q0] at hc
    nlinarith
  · dsimp [b,PrimaryZero.b]
    nlinarith only [hc]

lemma cost_eq {A B φ : ℝ} (ht : OuterState A B) (hU : A+1/2=U φ) :
    K φ=φ-e-L B := by
  have hh := LHeight_actual ht
  rw [hU] at hh
  dsimp [K]
  linarith

end SquaresInCircles.Eight.SecondWord.LPrimaryZero
end
end
end

section
/-!
## Fixed references for the shared L primary zero-source curve

The references use exact harmonic coordinates and squared rational
radical cages. Whole-interval derivative signs, proved in the preceding
module, transfer these references to the complete curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

lemma reference_trig :
    (98315693/100000000:ℝ)≤Real.sin (1387/1000) ∧
    Real.sin (1387/1000)≤98315697/100000000 ∧
    (9138163/50000000:ℝ)≤Real.cos (1387/1000) ∧
    Real.cos (1387/1000)≤4569082/25000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (1387/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1387/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1387/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1387/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates :
    (16895719/10000000:ℝ)≤U (1387/1000) ∧ U (1387/1000)≤8447861/5000000 ∧
    (194741/200000:ℝ)≤w (1387/1000) ∧ w (1387/1000)≤2434263/2500000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [reference_trig.1,reference_trig.2.2.1],
    by linarith [reference_trig.2.1,reference_trig.2.2.2],
    by linarith [reference_trig.1,reference_trig.2.2.2],
    by linarith [reference_trig.2.1,reference_trig.2.2.1]⟩

lemma reference_height_value :
    -(467831/1000000:ℝ)<LHeight.eval (16895719/10000000) := by
  have hr := root_cage (u := (16895719/10000000:ℝ))
    (l := (515011357819/500000000000:ℝ))
    (r := (1030022715639/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma reference_height_slopes :
    (1027303/1000000:ℝ)<LHeight.d1 (16895719/10000000) ∧
    LHeight.d1 (8447861/5000000)<(205461/200000:ℝ) := by
  constructor
  · have hu : (16895719/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (16895719/10000000:ℝ))
      (l := (515011357819/500000000000:ℝ))
      (r := (1030022715639/1000000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    have hp := root_pos (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]
  · have hu : (8447861/5000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (8447861/5000000:ℝ))
      (l := (51501111177/50000000000:ℝ))
      (r := (206004444709/200000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    have hp := root_pos (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]

lemma reference_cost :
    (17999/20000:ℝ)<K (1387/1000) ∧ |KD (1387/1000)|<3/10000 := by
  have hφ : (1387/1000:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := reference_coordinates
  have hU : U (1387/1000)∈Icc (33/20) (383/200) :=
    ⟨by linarith [hu.1],by linarith [hu.2.1]⟩
  have hm := LHeightBounds.eval_monotone
    (show (16895719/10000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) hu.1
  have hdl := LHeightBounds.first_monotone_high
    (show (16895719/10000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hU hu.1
  have hdu := LHeightBounds.first_monotone_high hU
    (show (8447861/5000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hu.2.1
  have hd : (1027303/1000000:ℝ)≤LHeight.d1 (U (1387/1000)) ∧
      LHeight.d1 (U (1387/1000))≤205461/200000 :=
    ⟨reference_height_slopes.1.le.trans hdl,hdu.trans reference_height_slopes.2.le⟩
  have hl := mul_le_mul hd.1 hu.2.2.1 (by norm_num : (0:ℝ)≤194741/200000)
    (by linarith [hd.1] : 0≤LHeight.d1 (U (1387/1000)))
  have hh := mul_le_mul hd.2 hu.2.2.2
    (by linarith [hu.2.2.1] : 0≤w (1387/1000)) (by norm_num : (0:ℝ)≤205461/200000)
  constructor
  · dsimp [K,e]
    linarith [reference_height_value]
  · rw [abs_lt]
    dsimp [KD]
    constructor <;> norm_num at * <;> linarith

lemma middle_reference_coordinates :
    (8384279/5000000:ℝ)≤U (7/5) ∧ U (7/5)≤16768561/10000000 ∧
    (2456467/2500000:ℝ)≤w (7/5) ∧ w (7/5)≤9825871/10000000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [PrimaryZero.terminal_trig.1,PrimaryZero.terminal_trig.2.2.1],
    by linarith [PrimaryZero.terminal_trig.2.1,PrimaryZero.terminal_trig.2.2.2],
    by linarith [PrimaryZero.terminal_trig.1,PrimaryZero.terminal_trig.2.2.2],
    by linarith [PrimaryZero.terminal_trig.2.1,PrimaryZero.terminal_trig.2.2.1]⟩

lemma middle_reference_height :
    (7517/5000:ℝ)<LHeight.d2 (8384279/5000000) ∧
    LHeight.d1 (16768561/10000000)<(5029/5000:ℝ) := by
  constructor
  · have hu : (8384279/5000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (8384279/5000000:ℝ))
      (l := (525298635541/500000000000:ℝ))
      (r := (1050597271083/1000000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hp := root_pos (LHeightBounds.domain hu)
    have hh := LHeight.d2_mul (LHeightBounds.domain hu)
    have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤525298635541/500000000000) hr.1.le 3
    have hu' := pow_le_pow_left₀ hp.le hr.2.le 3
    apply (mul_lt_mul_iff_left₀ (pow_pos hp 3)).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith
  · have hu : (16768561/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (16768561/10000000:ℝ))
      (l := (1050596792253/1000000000000:ℝ))
      (r := (525298396127/500000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hp := root_pos (LHeightBounds.domain hu)
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]

lemma middle_reference :
    (77/100:ℝ)<KDD (7/5) ∧ (11/1000:ℝ)<KD (7/5) := by
  have hφ : (7/5:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := middle_reference_coordinates
  have hdd := LHeightBounds.second_monotone
    (show (8384279/5000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) hu.1
  have hd := LHeightBounds.first_monotone_high
    (show U (7/5)∈Icc (33/20) (383/200) from ⟨by linarith [hu.1],by linarith [hu.2.1]⟩)
    (show (16768561/10000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hu.2.1
  have hm : (1/2:ℝ)≤ m (7/5) ∧ m (7/5)≤6768561/10000000 := by
    dsimp [m,U,PrimaryZero.U] at hu ⊢
    constructor <;> linarith [hu.1,hu.2.1]
  have hdf : LHeight.d1 (U (7/5))≤(5029/5000:ℝ) := hd.trans middle_reference_height.2.le
  have hdf0 := LHeightBounds.first_lower (height_domain hφ)
  have hp := mul_le_mul hdf hm.2 (by linarith [hm.1] : 0≤ m (7/5)) (by norm_num : (0:ℝ)≤5029/5000)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2456467/2500000) hu.2.2.1 2
  have hq := mul_le_mul (middle_reference_height.1.le.trans hdd) hs
    (by positivity : (0:ℝ)≤(2456467/2500000)^2)
    (by linarith [middle_reference_height.1] : 0≤LHeight.d2 (U (7/5)))
  have hprod := mul_le_mul hdf hu.2.2.2
    (by linarith [hu.2.2.1] : 0≤w (7/5)) (by norm_num : (0:ℝ)≤5029/5000)
  constructor
  · dsimp [KDD]
    norm_num at *
    linarith
  · dsimp [KD]
    norm_num at *
    linarith

lemma middle_terminal_coordinates :
    (15961679/10000000:ℝ)≤U (37/25) ∧ U (37/25)≤7980841/5000000 ∧
    w (37/25)≤1291919/1250000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [middle_terminal_trig.1,middle_terminal_trig.2.2.1],
    by linarith [middle_terminal_trig.2.1,middle_terminal_trig.2.2.2],
    by linarith [middle_terminal_trig.2.1,middle_terminal_trig.2.2.1]⟩

lemma middle_terminal_height : LHeight.d1 (15961679/10000000)<(95891/100000:ℝ) := by
  have hu : (15961679/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (15961679/10000000:ℝ))
    (l := (116955035591/100000000000:ℝ))
    (r := (1169550355911/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have hh := LHeight.d1_mul (LHeightBounds.domain hu)
  apply (mul_lt_mul_iff_left₀ hp).mp
  rw [hh]
  norm_num [LHeight,Q0]
  nlinarith [hr.1,hr.2]

lemma middle_terminal_slope : (1/125:ℝ)<KD (37/25) := by
  have hφ : (37/25:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := middle_terminal_coordinates
  have hm := LHeightBounds.first_antitone_low
    (show (15961679/10000000:ℝ)∈Icc (171/125) (8/5) by norm_num)
    (show U (37/25)∈Icc (171/125) (8/5) from ⟨by linarith [hu.1],by linarith [hu.2.1]⟩) hu.1
  have hd := hm.trans middle_terminal_height.le
  have hp := mul_le_mul hd hu.2.2 (w_positive hφ).le (by norm_num : (0:ℝ)≤95891/100000)
  dsimp [KD]
  norm_num at hp
  linarith

lemma late_initial_height : (16167179/10000000:ℝ)≤U (73/50) := by
  have hs := HighOrderTaylor.S11_le_sin (x := (73/50:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (73/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
    at hs hc
  dsimp [U,PrimaryZero.U,PrimaryZero.m]
  linarith

lemma late_initial_value : -(67429/125000:ℝ)<LHeight.eval (16167179/10000000) := by
  have hr := root_cage (u := (16167179/10000000:ℝ))
    (l := (1140974685003/1000000000000:ℝ))
    (r := (285243671251/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma late_initial_cost : (9013/10000:ℝ)<K (73/50) := by
  have hφ : (73/50:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hm := LHeightBounds.eval_monotone
    (show (16167179/10000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) late_initial_height
  dsimp [K,e]
  linarith [late_initial_value]

lemma aligned_height_value : -(326887/500000:ℝ)<LHeight.eval (3/2) := by
  have hr := root_cage (u := (3/2:ℝ))
    (l := (161322658049/125000000000:ℝ))
    (r := (1290581264393/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma aligned_cost : (4489/5000:ℝ)<K (Real.pi/2) := by
  norm_num [K,e,U,PrimaryZero.U,PrimaryZero.m]
  linarith [aligned_height_value,pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.LPrimaryZero
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic

lemma early_middle_lower {φ : ℝ} (hφ : φ∈Icc (33/25) (7/5)) :
    (44997/50000:ℝ)<K φ := by
  have hdom : ∀z∈Icc (33/25) (7/5),z∈middle :=
    fun z hz => ⟨hz.1,by linarith [hz.2]⟩
  have hc : ∀z∈Icc (33/25) (7/5),(77/100:ℝ)≤KDD z := by
    intro z hz
    have hm := KDD_antitone (hdom z hz) (show (7/5:ℝ)∈middle by norm_num [middle]) hz.2
    exact middle_reference.1.le.trans hm
  have ht := curvature_tangent (f := K) (d := KD) (dd := KDD) (κ := (77/100:ℝ))
    hφ (show (1387/1000:ℝ)∈Icc (33/25) (7/5) by norm_num)
    (fun z hz => K_hasDerivAt (middle_subset (hdom z hz)))
    (fun z hz => KD_hasDerivAt (middle_subset (hdom z hz))) hc
  have hd := abs_lt.mp reference_cost.2
  have hp := mul_pos (show 0<KD (1387/1000)+3/10000 by linarith [hd.1])
    (show 0<(3/10000:ℝ)-KD (1387/1000) by linarith [hd.2])
  have hs := sq_nonneg ((77/100)*(φ-1387/1000)+KD (1387/1000))
  nlinarith [reference_cost.1]

lemma middle_tail_slope {φ : ℝ} (hφ : φ∈Icc (7/5) (37/25)) : 0<KD φ := by
  have hdom : ∀z∈Icc (7/5) (37/25),z∈middle := fun z hz => ⟨by linarith [hz.1],hz.2⟩
  have hc : ConcaveOn ℝ (Icc (7/5) (37/25)) KD :=
    concave_of_deriv2 (fun z hz => KD_hasDerivAt (middle_subset (hdom z hz)))
      (fun z hz => KDD_hasDerivAt (middle_subset (hdom z hz)))
      (fun z hz => (KDDD_negative (hdom z hz)).le)
  exact concave_gt_of_endpoints hc hφ
    (by linarith [middle_reference.2]) (by linarith [middle_terminal_slope])

lemma middle_tail_monotone : MonotoneOn K (Icc (7/5) (37/25)) :=
  monoOn_of_hasDeriv_nonneg
    (fun z hz => (K_hasDerivAt (middle_subset
      (show z∈middle from ⟨by linarith [hz.1],hz.2⟩))).continuousAt.continuousWithinAt)
    (fun z hz => K_hasDerivAt (middle_subset
      (show z∈middle from ⟨by linarith [hz.1],hz.2.le⟩)))
    (fun z hz => (middle_tail_slope (Ioo_subset_Icc_self hz)).le)

theorem middle_lower {φ : ℝ} (hφ : φ∈middle) : (44997/50000:ℝ)<K φ := by
  by_cases he : φ≤7/5
  · exact early_middle_lower ⟨hφ.1,he⟩
  · exact (early_middle_lower (show (7/5:ℝ)∈Icc (33/25) (7/5) by norm_num)).trans_le
      (middle_tail_monotone (show (7/5:ℝ)∈Icc (7/5) (37/25) by norm_num)
        ⟨by linarith,hφ.2⟩ (by linarith))

theorem late_lower {φ : ℝ} (hφ : φ∈late) : (4489/5000:ℝ)<K φ := by
  have hc : ConcaveOn ℝ late K :=
    concave_of_deriv2 (fun z hz => K_hasDerivAt (late_subset hz))
      (fun z hz => KD_hasDerivAt (late_subset hz)) (fun z hz => (KDD_negative_late hz).le)
  exact concave_gt_of_endpoints hc hφ
    (by linarith [late_initial_cost]) aligned_cost

/-- Every angle in the complete shared zero-source range. -/
theorem lower {φ : ℝ} (hφ : φ∈angles) : (4489/5000:ℝ)<K φ := by
  by_cases hm : φ≤37/25
  · linarith [middle_lower (show φ∈middle from ⟨hφ.1,hm⟩)]
  · exact late_lower ⟨by linarith,hφ.2⟩

theorem actual_negative {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈angles) (hU : A+1/2=U φ) :
    (17953/20000:ℝ)<φ-e-L B := by
  have hh := lower hφ
  rw [cost_eq ht hU] at hh
  norm_num at *
  linarith

theorem actual_positive {A B φ : ℝ} (ht : OuterState A B)
    (hφ : φ∈angles) (hU : A+1/2=U φ) :
    (361/400:ℝ)<φ-1449/100000-L B := by
  have hh := lower hφ
  rw [cost_eq ht hU] at hh
  dsimp [e] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.LPrimaryZero
end
end
end
