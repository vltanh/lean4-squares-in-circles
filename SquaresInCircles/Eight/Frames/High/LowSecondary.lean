module

public import SquaresInCircles.Eight.Frames.High.LowContactSelection
public import SquaresInCircles.Eight.Frames.High.LowSecondNormPolynomial
public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Frames.Low.HighParallel

/-!
# Eight squares: the secondary axis of a high source in a high/low pair

A high state and a low state separated along the secondary axis of the high square, at a frame
angle `x ≥ -34/125`, have the cost of the pair above `8833/10000` (`secondary_all`,
`source_secondary_high_low`; `target_secondary_low_high` for the reversed pair); the source is
positive (`high_source_secondary_positive`). For a negative target and `0 < x < 23/50`, the weak
separator is compared with a contact of the two arcs (`interval_weak_separator`): when the
contact height `height x B` reaches the high arc, the cost is at least that of the contact
(`contact_cost_le`); otherwise the continuity of the height and its value at the lower corner
give a contact at the cut `b2`. The diagonal and axial costs of `FrameHighLowContactSelection`
cover the contacts, negative angles follow by `FrameHighLowNegativeAngles.weak_separator`,
angles beyond `23/50` by the tail `high_low_tail`, and a positive target by
`FrameHighLowPositiveCircle.weak_separator`.
-/

section
/-!
## The whole negative-angle high/low secondary contact deformation

The source contact coordinate is explicit and remains on the original
high arc while the angle moves to zero.  The derivative is strictly
negative on the complete interval `[-.272,0]`.  No continuation or
alignment conclusion is supplied as an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowNegativeAngles
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

def domain : Set ℝ := Icc (-(34/125:ℝ)) 0

theorem width_actual {x : ℝ} (hx : x∈domain) :
    FrameLowHighParallelCalculus.width false x=pairWidth x ∧ FrameLowHighParallelCalculus.width false x-1=periodicFrameCost x := by
  have hh := negative_width (show x∈Icc (-(54/125:ℝ)) 0 from
    ⟨by linarith [hx.1],hx.2⟩)
  constructor
  · simpa [FrameLowHighParallelCalculus.width] using hh.1.symm
  · rw [hh.2]
    dsimp [FrameLowHighParallelCalculus.width]
    ring

theorem P_lower {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain) :
    (159/100:ℝ)<P false B x := by
  have ht := negative_trig hx
  have hA := A_low_bounds hB
  have hAc := mul_le_mul
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2.le
    (by norm_num : (0:ℝ)≤963/1000) (by linarith [hA.1,a1_precise.1] : 0≤A B+1/2)
  have hcoef : 0≤1/2-B := by linarith [hB.2,b1_bounds.2]
  have hBs := mul_le_mul_of_nonneg_left
    (show -(34/125:ℝ)≤Real.sin x by linarith [ht.2.1]) hcoef
  dsimp [P,widthD]
  nlinarith [hB.1]

theorem height_antitone {B : ℝ} (hB : B∈Icc 0 b1) :
    AntitoneOn (height false B) domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (height_deriv false B x).continuousAt.continuousWithinAt
  · exact fun x _ => height_deriv false B x
  · intro x hx
    have hh := P_lower hB (Ioo_subset_Icc_self hx)
    linarith

theorem source_contact_le {b B x : ℝ} (hx : x∈domain)
    (hm : 0≤ secondary true false b B x) : height false B x≤b := by
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  dsimp [height]
  rw [(width_actual hx).1]
  linarith

theorem contact_high {b B x t : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) (ht : t∈Icc x 0) :
    height false B t∈Icc b2 c0 := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have h0 := height_antitone hB htd (show (0:ℝ)∈domain by constructor <;> norm_num) ht.2
  have h1 := height_antitone hB hx htd ht.1
  rw [height_zero] at h0
  have hsource := source_contact_le hx hm
  exact ⟨by linarith [hB.2,b1_bounds.2,b2_bounds.2],by linarith [hb.2]⟩

theorem contact_wide {b B x t : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) (ht : t∈Icc x 0) :
    height false B t∈Icc (16/25:ℝ) (93/100) := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have h0 := height_antitone hB htd (show (0:ℝ)∈domain by constructor <;> norm_num) ht.2
  rw [height_zero] at h0
  have hh := contact_high hb hB hx hm ht
  constructor <;> linarith [hB.2,b1_bounds.2,hh.2,c0_bounds.2]

theorem cost_derivative_negative {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain)
    (hz : height false B x∈Icc b2 c0) : highD false B x<0 := by
  have hp := P_lower hB hx
  have hd := high_Hd_lower hz
  have hm := mul_le_mul hd.le hp.le (by norm_num : (0:ℝ)≤159/100)
    (by linarith : 0≤Hd (height false B x))
  have hs := (negative_trig hx).1
  have hc := Real.cos_le_one x
  dsimp [highD,widthD]
  nlinarith

theorem move_to_zero {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) :
    highCost false B 0≤highCost false B x := by
  have ha : AntitoneOn (highCost false B) (Icc x 0) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro t ht
      exact (highCost_deriv false (contact_wide hb hB hx hm ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact highCost_deriv false (contact_wide hb hB hx hm (Ioo_subset_Icc_self ht))
    · intro t ht
      exact (cost_derivative_negative hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        (contact_high hb hB hx hm (Ioo_subset_Icc_self ht))).le
  exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  have hzero := contact_high hb hB hx hm (show (0:ℝ)∈Icc x 0 from ⟨hx.2,le_rfl⟩)
  rw [height_zero] at hzero
  have ha := FrameLowHighAligned.parallel_contact hB hzero (by linarith : (1:ℝ)≤B+(1-B))
  have hinitial : (8833/10000:ℝ)<highCost false B 0 := by
    rw [FrameLowHighParallel.highCost_zero]
    linarith [FrameLowHighAligned.F0_lower]
  have hmove := move_to_zero hb hB hx hm
  have hheight := source_contact_le hx hm
  have hlabel := H_monotone (contact_high hb hB hx hm ⟨le_rfl,hx.2⟩) hb hheight
  have hcost : highCost false B x≤highLowCost true false b B x := by
    dsimp [highCost,highLowCost,sign]
    rw [(width_actual hx).2]
    linarith
  exact hinitial.trans_le (hmove.trans hcost)

end SquaresInCircles.Eight.FrameHighLowNegativeAngles
end
end
end

section
/-!
## One positive quadratic for the complete high/low support interval

Expanding the two displayed quartics and Taylor sums gives a single
absolute-power lower bound.  Every higher power is absorbed into its
quadratic coefficient on `[-.11,.58]`.  Completing the square leaves
the exact reserve `38999/960000000` throughout the entire interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowSupportPolynomial
open FrameHighLowFirstNormPolynomial FrameHighLowSecondNormPolynomial

def V0 (w : ℝ) : ℝ :=
  (19/100+w)-(9/100)*Arithmetic.cos8 (19/100+w)+
    (lam (19/100+w)-9/100)*(Arithmetic.sin9 (19/100+w)-3/100000000)+
      lam (19/100+w)+(314159/100000)/4+
        (FrameHighArc.u-FrameHighArc.v)*(449607/500000)+
        FrameLowArc.u*(56583/40000)+
        (FrameHighArc.u-FrameHighArc.v+FrameLowArc.u+FrameLowArc.v+9/50)/2-
          (494697/250000)*(U1 w+U2 w)-8833/10000

def lowerPolynomial (u : ℝ) : ℝ :=
  37/500000-(179/100000)*u+(1097/25000)*u^2-(3423/500000)*u^3-
    (1059/25000)*u^4-(1219/250000)*u^5-(2391/1000000)*u^6-
      (119/1250000)*u^7-(1017/1000000000)*u^9-(193/250000000)*u^10

def quadraticCoefficient (u : ℝ) : ℝ :=
  1097/25000-(3423/500000)*u-(1059/25000)*u^2-(1219/250000)*u^3-
    (2391/1000000)*u^4-(119/1250000)*u^5-(1017/1000000000)*u^7-
      (193/250000000)*u^8

theorem positive_remainder {u : ℝ} (hu : 0≤u) : lowerPolynomial u<V0 u := by
  have h2 := pow_nonneg hu 2
  have h3 := pow_nonneg hu 3
  have h4 := pow_nonneg hu 4
  have h5 := pow_nonneg hu 5
  have h6 := pow_nonneg hu 6
  have h7 := pow_nonneg hu 7
  have h8 := pow_nonneg hu 8
  have h9 := pow_nonneg hu 9
  have h10 := pow_nonneg hu 10
  simp only [lowerPolynomial,V0,U1,U2,lam,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  linarith

theorem negative_remainder {u : ℝ} (hu : 0≤u) : lowerPolynomial u<V0 (-u) := by
  have h2 := pow_nonneg hu 2
  have h3 := pow_nonneg hu 3
  have h4 := pow_nonneg hu 4
  have h5 := pow_nonneg hu 5
  have h6 := pow_nonneg hu 6
  have h7 := pow_nonneg hu 7
  have h8 := pow_nonneg hu 8
  have h9 := pow_nonneg hu 9
  have h10 := pow_nonneg hu 10
  simp only [lowerPolynomial,V0,U1,U2,lam,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  linarith

theorem absolute_remainder (w : ℝ) : lowerPolynomial |w|<V0 w := by
  by_cases hw : 0≤w
  · simpa only [abs_of_nonneg hw] using positive_remainder hw
  · have hn : w≤0 := le_of_not_ge hw
    have hh := negative_remainder (neg_nonneg.mpr hn)
    simpa only [neg_neg,abs_of_nonpos hn] using hh

theorem quadratic_coefficient_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (29/50)) :
    (3/125:ℝ)<quadraticCoefficient u := by
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h3 := pow_le_pow_left₀ hu.1 hu.2 3
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have h5 := pow_le_pow_left₀ hu.1 hu.2 5
  have h7 := pow_le_pow_left₀ hu.1 hu.2 7
  have h8 := pow_le_pow_left₀ hu.1 hu.2 8
  dsimp [quadraticCoefficient]
  linarith [hu.2]

theorem quadratic_lower {u : ℝ} (hu : u∈Icc (0:ℝ) (29/50)) :
    37/500000-(179/100000)*u+(3/125)*u^2≤lowerPolynomial u := by
  have hh := mul_le_mul_of_nonneg_right (quadratic_coefficient_lower hu).le (sq_nonneg u)
  dsimp [lowerPolynomial,quadraticCoefficient] at *
  nlinarith only [hh]

theorem quadratic_reserve (u : ℝ) :
    (38999/960000000:ℝ)≤37/500000-(179/100000)*u+(3/125)*u^2 := by
  nlinarith [sq_nonneg ((6/125:ℝ)*u-179/100000)]

theorem lower {w : ℝ} (hw : w∈domain) : (38999/960000000:ℝ)<V0 w := by
  have hu : |w|∈Icc (0:ℝ) (29/50) :=
    ⟨abs_nonneg w,abs_le.mpr ⟨by linarith [hw.1],hw.2⟩⟩
  exact (quadratic_reserve |w|).trans_lt ((quadratic_lower hu).trans_lt (absolute_remainder w))

end SquaresInCircles.Eight.FrameHighLowSupportPolynomial
end
end
end

section
/-!
## The complete original positive-high / positive-low secondary branch

The two quartic polynomial bounds are transferred to the actual
circle-force norms by directed global Taylor estimates.  Subtracting
the original weak margin then gives the full support inequality on
`[.08,.77]`; the original angle cut and elementary tail finish every
angle.  No minimizing-point or polynomial-positivity premise is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPositiveCircle
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameHighLowFirstNormPolynomial (lam U1)
open FrameHighLowSecondNormPolynomial (U2)

def domain : Set ℝ := Icc (2/25:ℝ) (77/100)
def n1 (x : ℝ) : ℝ := Real.sqrt (FrameHighArc.u^2+(lam x-FrameHighArc.v)^2)
def n2 (x : ℝ) : ℝ := Real.sqrt (FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
  2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x))
def F (x : ℝ) : ℝ := x-(9/100)*Real.cos x+(lam x-9/100)*Real.sin x+lam x+
  FrameHighArc.k+FrameLowArc.u*a0+
    (FrameHighArc.u-FrameHighArc.v+FrameLowArc.u+FrameLowArc.v+9/50)/2-
      R*(n1 x+n2 x)

theorem centered_domain {x : ℝ} (hx : x∈domain) :
    x-19/100∈FrameHighLowFirstNormPolynomial.domain := by
  constructor <;> linarith [hx.1,hx.2]

theorem taylor_bounds {x : ℝ} (hx : x∈domain) :
    Arithmetic.sin9 x-3/100000000≤Real.sin x ∧ Real.sin x≤Arithmetic.sin9 x ∧
      Arithmetic.cos8 x-3/100000000≤Real.cos x ∧ Real.cos x≤Arithmetic.cos8 x := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hs := HighOrderTaylor.S11_le_sin hx0
  have hc := Arithmetic.cos10_le_cos hx0
  have h11 := pow_le_pow_left₀ hx0 hx.2 11
  have h10 := pow_le_pow_left₀ hx0 hx.2 10
  dsimp [HighOrderTaylor.S11] at hs
  dsimp [Arithmetic.cos10] at hc
  exact ⟨by linarith,Arithmetic.sin_le_sin9 hx0,by linarith,Arithmetic.cos_le_cos8 hx0⟩

theorem n1_square (x : ℝ) :
    (n1 x)^2=FrameHighArc.u^2+(lam x-FrameHighArc.v)^2 :=
  Real.sq_sqrt (by positivity)

theorem n2_energy (x : ℝ) :
    FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
      2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x)=
        (FrameLowArc.u+lam x*Real.sin x)^2+(FrameLowArc.v-lam x*Real.cos x)^2 := by
  linear_combination -(lam x)^2*(Real.sin_sq_add_cos_sq x)

theorem n2_square (x : ℝ) :
    (n2 x)^2=FrameLowArc.u^2+FrameLowArc.v^2+(lam x)^2+
      2*lam x*(FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x) := by
  apply Real.sq_sqrt
  rw [n2_energy]
  positivity

theorem n1_bound {x : ℝ} (hx : x∈domain) : n1 x<U1 (x-19/100) := by
  have hr := FrameHighLowFirstNormPolynomial.squared_reserve (centered_domain hx)
  have hp := FrameHighLowFirstNormPolynomial.U1_positive (centered_domain hx)
  have hs := n1_square x
  have hn : 0≤n1 x := Real.sqrt_nonneg _
  have hid : 19/100+(x-19/100)=x := by ring
  dsimp [FrameHighLowFirstNormPolynomial.A,FrameHighLowFirstNormPolynomial.X1] at hr
  rw [hid] at hr
  nlinarith

theorem n2_taylor {x : ℝ} (hx : x∈domain) :
    (n2 x)^2≤FrameHighLowSecondNormPolynomial.X2 (x-19/100)+9/100000000 := by
  have ht := taylor_bounds hx
  have hl := FrameHighLowFirstNormPolynomial.lam_bounds hx
  have htrig : FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x≤
      FrameLowArc.u*Arithmetic.sin9 x-FrameLowArc.v*Arithmetic.cos8 x+
        FrameLowArc.v*(3/100000000) := by
    dsimp [FrameLowArc.u,FrameLowArc.v]
    linarith
  have hh := mul_le_mul_of_nonneg_left htrig (show 0≤2*lam x by linarith)
  have herr : 2*lam x*FrameLowArc.v*(3/100000000)≤9/100000000 := by
    dsimp [FrameLowArc.v]
    linarith [hl.2]
  have hid : 19/100+(x-19/100)=x := by ring
  rw [n2_square]
  dsimp [FrameHighLowSecondNormPolynomial.X2]
  rw [hid]
  nlinarith only [hh,herr]

theorem n2_bound {x : ℝ} (hx : x∈domain) : n2 x<U2 (x-19/100) := by
  have hr := FrameHighLowSecondNormPolynomial.squared_reserve (centered_domain hx)
  have hp := FrameHighLowSecondNormPolynomial.U2_positive (centered_domain hx)
  have hs := n2_taylor hx
  have hn : 0≤n2 x := Real.sqrt_nonneg _
  dsimp [FrameHighLowSecondNormPolynomial.B] at hr
  nlinarith

theorem polynomial_transfer {x : ℝ} (hx : x∈domain) :
    FrameHighLowSupportPolynomial.V0 (x-19/100)<F x-8833/10000 := by
  have ht := taylor_bounds hx
  have hl := FrameHighLowFirstNormPolynomial.lam_bounds hx
  have hsin := mul_le_mul_of_nonneg_left ht.1 (sub_nonneg.mpr hl.1.le)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2 (by norm_num : (0:ℝ)≤9/100)
  have hsum : n1 x+n2 x≤U1 (x-19/100)+U2 (x-19/100) :=
    add_le_add (n1_bound hx).le (n2_bound hx).le
  have hnorm := mul_le_mul
    (show R≤494697/250000 by linarith [radius_precise.2]) hsum
    (by dsimp [n1,n2]; positivity : 0≤n1 x+n2 x)
    (by norm_num : (0:ℝ)≤494697/250000)
  have hid : 19/100+(x-19/100)=x := by ring
  dsimp [FrameHighLowSupportPolynomial.V0]
  rw [hid]
  dsimp [F,k,FrameHighArc.u,FrameHighArc.v,FrameLowArc.u,FrameLowArc.v]
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.1,a0_precise.1]

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x := by
  have hp := FrameHighLowSupportPolynomial.lower (centered_domain hx)
  have ht := polynomial_transfer hx
  linarith

theorem circle_support {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) : F x≤highLowCost true true b B x := by
  have hlam : 0≤lam x := by linarith [(FrameHighLowFirstNormPolynomial.lam_bounds hx).1]
  have hscaled := mul_nonneg hlam hm
  have hs := circle_linear_lower (A_circle ⟨b2_mem.1.trans hb.1,hb.2⟩)
    (-FrameHighArc.u) (FrameHighArc.v-lam x)
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-lam x*Real.sin x) (lam x*Real.cos x-FrameLowArc.v)
  have hn1 : Real.sqrt ((-FrameHighArc.u)^2+(FrameHighArc.v-lam x)^2)=n1 x := by
    dsimp [n1]
    congr 1
    ring
  have hn2 : Real.sqrt ((-FrameLowArc.u-lam x*Real.sin x)^2+
      (lam x*Real.cos x-FrameLowArc.v)^2)=n2 x := by
    dsimp [n2]
    congr 1
    linear_combination (lam x)^2*(Real.sin_sq_add_cos_sq x)
  rw [hn1] at hs
  rw [hn2] at ht
  have hq : x∈Icc 0 (Real.pi/2) := ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hscaled
  rw [(first_width hq).1] at hscaled
  dsimp [F,highLowCost,H,L,sign]
  rw [(first_width hq).2]
  nlinarith

theorem interval_weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<highLowCost true true b B x :=
  (lower hx).trans_le (circle_support hb hB hx hm)

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary true true b B x) :
    (8833/10000:ℝ)<highLowCost true true b B x := by
  have hcut := high_low_positive_cut hb hB hx hm
  by_cases htail : (77/100:ℝ)≤x
  · exact high_low_tail true true hb hB htail
  · exact interval_weak_separator hb hB ⟨hcut.le,le_of_lt (lt_of_not_ge htail)⟩ hm

end SquaresInCircles.Eight.FrameHighLowPositiveCircle
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowSecondary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameHighLowContactSurface

theorem contact_cost_le {b B x : ℝ} (hb : b∈Icc b2 c0) (_hB : B∈Icc 0 b1)
    (hx : x∈FrameHighLowAxialGeometry.domain) (hz : height x B∈Icc b2 c0)
    (hheight : height x B≤b) : F x B≤highLowCost true false b B x := by
  have hh := H_monotone hz hb hheight
  dsimp [F,highLowCost,sign]
  rw [(first_width (FrameHighLowAxialGeometry.quadrant hx)).2]
  linarith

theorem interval_weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈FrameHighLowAxialGeometry.domain) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  have hheight := height_le_source hx hm
  by_cases hcontact : b2≤height x B
  · have hz : height x B∈Icc b2 c0 := ⟨hcontact,hheight.trans hb.2⟩
    exact (FrameHighLowContactSelection.contact_lower hx hB hz).trans_le
      (contact_cost_le hb hB hx hz hheight)
  · have hcorner : b2<height x 0 := by
      rw [height_zero]
      linarith [(FrameHighLowAxialGeometry.Z_bounds hx).1,b2_bounds.2]
    have hc : ContinuousOn (fun t => -height x t) (Icc 0 B) := by
      intro t ht
      exact (height_deriv (show t∈lowDomain from
        ⟨by linarith [ht.1],ht.2.trans hB.2⟩) x).neg.continuousAt.continuousWithinAt
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hB.1 hc
      (show -b2∈Icc (-height x 0) (-height x B) by constructor <;> linarith)
    have heq : height x t=b2 := by linarith
    have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
    have hthigh : height x t∈Icc b2 c0 := by rw [heq]; exact ⟨le_rfl,b2_mem.2⟩
    have hbound := FrameHighLowContactSelection.contact_lower hx htlow hthigh
    have hH := H_monotone (show b2∈Icc b2 c0 from ⟨le_rfl,b2_mem.2⟩) hb hb.1
    have hL := L_monotone htlow hB ht.2
    have hcost : F x t≤highLowCost true false b B x := by
      dsimp [F,highLowCost,sign]
      rw [heq,(first_width (FrameHighLowAxialGeometry.quadrant hx)).2]
      linarith
    exact hbound.trans_le hcost

theorem positive_negative {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  by_cases htail : (23/50:ℝ)≤x
  · exact high_low_tail true false hb hB htail
  by_cases hnegative : x≤0
  · exact FrameHighLowNegativeAngles.weak_separator hb hB ⟨hx,hnegative⟩ hm
  · exact interval_weak_separator hb hB ⟨le_of_not_ge hnegative,le_of_not_ge htail⟩ hm

theorem secondary_all (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary i k b B x) : (8833/10000:ℝ)<highLowCost i k b B x := by
  have hi := high_source_secondary_positive i k hb hB hm
  subst i
  cases k
  · exact positive_negative hb hB hx hm
  · exact FrameHighLowPositiveCircle.weak_separator hb hB hx hm

theorem source_secondary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_high_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := high_low_angle s t ht hgap
  rw [state_high_low_cost s t hs ht]
  exact secondary_all s.positive t.positive hb hB hx.le hmargin

theorem target_secondary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 2 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_secondary_high_low t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.FrameHighLowSecondary
end
end
end
