module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateShape
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.SupportThird
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData

/-!
# Eight squares: the tight positive-core primary support on its whole interval

The third derivative is positive on the complete deviation half.
An endpoint principle covers the initial range, and one quadratic
tangent covers the remaining range. Fixed Taylor and radical references
are proved by rational interval algebra.
-/

section
/-!
## Original-coordinate data for negative outer to positive core at edge three

The two contact relaxations are functions of the original outer point.
The high transverse-coordinate derivative estimate follows from the
already established primary-coordinate label bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open PositiveThree (Lower lowerAngle)

def g : ℝ := 94831/100000
def c : ℝ := 497/10000
def γ : ℝ := 17953/20000
def value (b B φ : ℝ) : ℝ := φ-c-T b-g*B
def aligned (b : ℝ) : ℝ := Real.pi/2-c-T b-g*(arc b-1)
abbrev secondaryCut := MixedTwo.PositiveCore.secondaryCut
abbrev primaryCut := MixedTwo.PositiveCore.primaryCut
def secondaryContact (b φ : ℝ) : ℝ := φ-c-T b-g*secondaryCut (arc b) b φ
def primaryContact (b φ : ℝ) : ℝ := φ-c-T b-g*primaryCut (arc b) φ

lemma high_ratio {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) :
    TLabel.d1 b<(17/20)*ratio b := by
  have hdom : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  have hs := ShortOuterOne.SameContact.arc_state hdom
  have ha := NegativeTwo.primary_mem hs
  have hu : arc b≤11/10 := by
    have hc := hs.2.2
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5)
      (show 6/5≤b+1/2 by linarith [hb.1]) 2
    norm_num [Q0] at hc
    nlinarith [hs.1,hs.2.1]
  have hr : 0<ratio b := by
    dsimp [ratio]
    exact div_pos (by linarith [hb.1]) (by linarith [hs.1,hs.2.1])
  have hh := mul_lt_mul_of_pos_right (OppositeThree.primary_first_eleven ⟨ha.1,hu⟩) hr
  rw [NegativeThree.primary_first_exchange hs] at hh
  exact hh

lemma aligned_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt aligned (g*ratio b-TLabel.d1 b) b := by
  have hT : HasDerivAt T (TLabel.d1 b) b := TLabel.outer_hasDerivAt (outer_domain hb)
  have h := (hT.const_sub (Real.pi/2-c)).sub
    (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const 1).const_mul g)
  exact h.congr_deriv (by ring)

lemma aligned_monotone : MonotoneOn aligned (Icc (7/10:ℝ) outerDiagonal) := by
  have hdom {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) : b∈Icc 0 outerDiagonal :=
    ⟨by linarith [hb.1],hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (aligned_hasDerivAt (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hh := high_ratio (Ioo_subset_Icc_self hb)
  have hr : 0≤ratio b := by
    dsimp [ratio]
    have hs := ShortOuterOne.SameContact.arc_state (hdom (Ioo_subset_Icc_self hb))
    exact div_nonneg (by linarith [hb.1]) (by linarith [hs.1,hs.2.1])
  norm_num [g] at *
  nlinarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.PrimarySupport
open CommonQuarter CorePairGeometry Arithmetic
open MixedPrimarySupport
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra (rootThree rootStep piBox)

def p : ℝ := 12867969/20000000
def k : ℝ := 128316398/1000000000
def K : ℝ := Real.pi/2-e-k+(g+p)/2-γ
def f := minus g p K
def d := minusD g p K
def dd := minusDD g p K
def ddd := minusDDD g p K

lemma K_bounds : (3433/2500:ℝ)<K ∧ K<(687/500:ℝ) := by
  dsimp [K,g,p,e,k,γ,EdgeThreeAligned.gp,EdgeThreeAligned.ep,EdgeThreeAligned.threshold]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma third_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0<ddd x := by
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hsc := mul_nonneg ht.2.2.1 hc.le
  have hN := mul_le_mul_of_nonneg_left
    (NDDD_upper (g := g) (p := p) (by norm_num [g,EdgeThreeAligned.gp]) hx)
    (by linarith [radius_bounds.1] : 0≤CommonQuarter.radius)
  have hcoef : CommonQuarter.radius*(4*p^2/g)<(393/125:ℝ) := by
    have hh := mul_lt_mul_of_pos_right radius_bounds.2
      (by norm_num [p,g,EdgeThreeAligned.gp] : 0<4*p^2/g)
    norm_num [p,g,EdgeThreeAligned.gp] at hh ⊢
    linarith
  have hn := mul_le_mul_of_nonneg_right hcoef.le hsc
  have hp := mul_nonneg ht.2.2.1
    (show 0≤K-x-(1683/2500)*Real.cos x by linarith [K_bounds.1,hx.2,ht.2.1])
  have hq := mul_nonneg hc.le
    (show 0≤(6177/2500)*(8053/12500-Real.sin x) by linarith [ht.2.2.2.1])
  dsimp only [ddd,minusDDD]
  generalize NDDD g p x=Z at hN ⊢
  simp only [g,EdgeThreeAligned.gp] at hN hn ⊢
  linarith

lemma second_monotone : MonotoneOn dd (Icc (0:ℝ) (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (minusDD_hasDerivAt (g := g) (p := p) (K := K) (by norm_num [g,EdgeThreeAligned.gp])).continuousAt.continuousWithinAt)
    (fun x _ => minusDD_hasDerivAt (g := g) (p := p) (K := K) (by norm_num [g,EdgeThreeAligned.gp]))
    (fun x hx => (third_positive (Ioo_subset_Icc_self hx)).le)

def sinBox {x : ℝ} (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S15_le_sin hx,HighOrderTaylor.sin_le_S13 hx⟩
def cosBox {x : ℝ} (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨HighOrderTaylor.C14_le_cos hx,HighOrderTaylor.cos_le_C12 hx⟩
def radBox {x : ℝ} (C : Interval (Real.cos x)) : Interval (g^2+p^2*(Real.cos x)^2) :=
  (Interval.point (g^2)).add ((Interval.point (p^2)).mul C.square)
def normBox {x : ℝ} (C : Interval (Real.cos x)) (hC : 0≤(radBox C).lo) : Interval (N g p x) :=
  rootThree (radBox C) (6/5) (by norm_num) hC

lemma radius_precise : (1978787507540/1000000000000:ℝ)<CommonQuarter.radius ∧
    CommonQuarter.radius<(1978787507541/1000000000000:ℝ) := by
  have hh := radius_sq
  norm_num [Q0] at hh
  constructor <;> nlinarith [radius_bounds.1]

def radiusBox : Interval CommonQuarter.radius := Interval.of_bounds ⟨radius_precise.1.le,radius_precise.2.le⟩
def KBox : Interval K :=
  ((((piBox.div (Interval.point 2) (by norm_num [Interval.point])).sub (Interval.point e)).sub
    (Interval.point k)).add (Interval.point ((g+p)/2))).sub (Interval.point γ)

def firstNormBox {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) (hN : 0<N₀.lo) : Interval (ND g p x) :=
  (((Interval.point (-p^2)).mul S).mul C).div N₀ hN
def secondNormBox {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) (hN : 0<N₀.lo) : Interval (NDD g p x) :=
  (((Interval.point (-p^2)).mul (C.square.sub S.square)).div N₀ hN).sub
    ((((Interval.point (p^4)).mul S.square).mul C.square).div N₀.cube (Interval.cube_lo_pos hN))
def valueBox {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) : Interval (f x) :=
  (((KBox.sub (Interval.point x)).mul C).add
    ((Interval.point g).mul ((Interval.point 1).add ((Interval.point (13/12)).mul S)))).sub
      (radiusBox.mul N₀)
def slopeBox {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) (hN : 0<N₀.lo) : Interval (d x) :=
  ((((Interval.point (13*g/12-1)).mul C).sub ((KBox.sub (Interval.point x)).mul S)).sub
    (radiusBox.mul (firstNormBox S C N₀ hN)))
def secondBox {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) (hN : 0<N₀.lo) : Interval (dd x) := by
  convert ((((KBox.sub (Interval.point x)).mul C).neg.add ((Interval.point (2-13*g/12)).mul S)).sub
    (radiusBox.mul (secondNormBox S C N₀ hN))) using 1
  dsimp only [dd,minusDD]
  ring

private lemma r48_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl

private lemma r48_secondBox_lo {x : ℝ} (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (N₀ : Interval (N g p x)) (hN : 0<N₀.lo) :
    (secondBox S C N₀ hN).lo=((((KBox.sub (Interval.point x)).mul C).neg.add
      ((Interval.point (2-13*g/12)).mul S)).sub (radiusBox.mul (secondNormBox S C N₀ hN))).lo :=
  r48_mpr_lo (by dsimp only [dd,minusDD]; ring) _ _

local macro "support_reference" : tactic => `(tactic|
  norm_num [sinBox,cosBox,radBox,normBox,rootThree,rootStep,radiusBox,KBox,piBox,
    firstNormBox,secondNormBox,valueBox,slopeBox,secondBox,p,k,g,e,γ,
    EdgeThreeAligned.gp,EdgeThreeAligned.ep,EdgeThreeAligned.threshold,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,
    HighOrderTaylor.C12,sin9,sin7,cos10,cos8,Q0,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.inv,Interval.div])

lemma left_value : (51/25000:ℝ)<f (11/100) := by
  let S := sinBox (x := (11/100:ℝ)) (by norm_num)
  let C := cosBox (x := (11/100:ℝ)) (by norm_num)
  let N₀ := normBox C (by dsimp [C]; support_reference)
  let F₀ := valueBox S C N₀
  have hh : (51/25000:ℝ)<F₀.lo := by dsimp [F₀,S,C,N₀]; support_reference
  exact hh.trans_le F₀.mem.1

lemma middle_reference : (107/25000:ℝ)<f (1/2) ∧ d (1/2)< -(1449/100000:ℝ) ∧
    (3/50:ℝ)<dd (1/2) := by
  let S := sinBox (x := (1/2:ℝ)) (by norm_num)
  let C := cosBox (x := (1/2:ℝ)) (by norm_num)
  let N₀ := normBox C (by dsimp [C]; support_reference)
  have hN : 0<N₀.lo := by dsimp [N₀,C]; support_reference
  let F₀ := valueBox S C N₀
  let D₀ := slopeBox S C N₀ hN
  let D₁ := secondBox S C N₀ hN
  have hf : (107/25000:ℝ)<F₀.lo := by dsimp [F₀,S,C,N₀]; support_reference
  have hd : D₀.hi< -(1449/100000:ℝ) := by dsimp [D₀,S,C,N₀]; support_reference
  have hdd : (3/50:ℝ)<D₁.lo := by
    show (3/50:ℝ)<(secondBox S C N₀ hN).lo
    rw [r48_secondBox_lo]
    dsimp [S,C,N₀]
    support_reference
  exact ⟨hf.trans_le F₀.mem.1,D₀.mem.2.trans_lt hd,hdd.trans_le D₁.mem.1⟩

lemma critical_reference : (163/50000:ℝ)<f (31/50) ∧ |d (31/50)|<(1/2500:ℝ) := by
  let S := sinBox (x := (31/50:ℝ)) (by norm_num)
  let C := cosBox (x := (31/50:ℝ)) (by norm_num)
  let N₀ := normBox C (by dsimp [C]; support_reference)
  have hN : 0<N₀.lo := by dsimp [N₀,C]; support_reference
  let F₀ := valueBox S C N₀
  let D₀ := slopeBox S C N₀ hN
  have hf : (163/50000:ℝ)<F₀.lo := by dsimp [F₀,S,C,N₀]; support_reference
  have hl : -(1/2500:ℝ)<D₀.lo := by dsimp [D₀,S,C,N₀]; support_reference
  have hu : D₀.hi<(1/2500:ℝ) := by dsimp [D₀,S,C,N₀]; support_reference
  exact ⟨hf.trans_le F₀.mem.1,abs_lt.mpr ⟨hl.trans_le D₀.mem.1,D₀.mem.2.trans_lt hu⟩⟩

theorem positive {x : ℝ} (hx : x∈Icc (11/100:ℝ) (7/10)) : 0<f x := by
  have hg : 0<g := by norm_num [g,EdgeThreeAligned.gp]
  by_cases he : x≤1/2
  · have hm := MinimumCalculus.endpoint_minimum (f := f) (d := d) (dd := dd) (ddd := ddd)
      (show x∈Icc (11/100:ℝ) (1/2) from ⟨hx.1,he⟩)
      (fun y _ => minus_hasDerivAt hg) (fun y _ => minusD_hasDerivAt hg)
      (fun y _ => minusDD_hasDerivAt hg)
      (fun y hy => (third_positive ⟨by linarith [hy.1],by linarith [hy.2]⟩).le)
      (by linarith [middle_reference.2.1])
    exact (lt_min (by linarith [left_value]) (by linarith [middle_reference.1])).trans_le hm
  · have hc : ∀y∈Icc (1/2:ℝ) (7/10),(3/50:ℝ)≤dd y := by
      intro y hy
      exact middle_reference.2.2.le.trans
        (second_monotone (by norm_num) ⟨by linarith [hy.1],hy.2⟩ hy.1)
    have ht := curvature_tangent (f := f) (d := d) (dd := dd) (κ := (3/50:ℝ))
      (show x∈Icc (1/2:ℝ) (7/10) from ⟨by linarith,hx.2⟩)
      (show (31/50:ℝ)∈Icc (1/2:ℝ) (7/10) by norm_num)
      (fun y _ => minus_hasDerivAt hg) (fun y _ => minusD_hasDerivAt hg) hc
    have hd := abs_lt.mp critical_reference.2
    have hp := mul_pos (show 0<d (31/50)+1/2500 by linarith [hd.1])
      (show 0<(1/2500:ℝ)-d (31/50) by linarith [hd.2])
    nlinarith [critical_reference.1,sq_nonneg ((3/50)*(x-31/50)+d (31/50))]

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.PrimarySupport
end
end
end
