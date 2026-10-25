module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondMixedPrimarySupportLower
public import SquaresInCircles.Eight.TableFree.SecondMixedTransverseSupport
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoUpperSecondary

/-!
# Original P-label chords for the positive core target

Convexity of P gives both restricted chords from one fixed physical
circle point apiece.  The aligned cost uses the already proved
primary-coordinate derivative and the actual unit-primary point.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveCore
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
          (1239/50000) using 1 <;> dsimp [f,P] <;> ring)
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
    (hB : 0≤B) (hx : 0≤x) (hk : 0≤k) (hku : k≤53/100)
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveCore
