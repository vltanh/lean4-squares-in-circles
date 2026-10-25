module

public import SquaresInCircles.Eight.Frames.Low.MidCuts
public import SquaresInCircles.Eight.Frames.Low.MidPrimaryScalars

/-!
# Eight squares: the primary axis of the source in the low/middle pairs

A low source and a middle target, or a middle source and a low target, separated along the
primary axis of the source at a frame angle `x ≥ 0`, have the cost of the pair above `1801/2000`
for all signs (`low_mid_primary`, `mid_low_primary`). A positive target is bounded by the support
of its circle, in the first and in the second quadrant (`low_mid_circle_support`,
`mid_low_circle_support`); a negative low target by the smaller of its values at the two ends of
the low arc (`negative_endpoint_support`), concave in the angle and above `1` on `[11/10, 7/5]`
(`endpoint_concave`, `endpoint_lower`). The sign of the source enters through a monotone loss of
its marker, and the margins are weak.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry FrameLowMidCuts

theorem norm_identity (i : Bool) (x : ℝ) :
    Real.sqrt ((FrameLowMidPrimaryScalars.lam i*Real.cos x-FrameLowMidPrimaryScalars.p i)^2+
      (FrameLowMidPrimaryScalars.lam i*Real.sin x-FrameLowMidPrimaryScalars.q i)^2)=
        FrameLowMidPrimaryScalars.N i x := by
  dsimp [FrameLowMidPrimaryScalars.N,CircularNorm.norm,CircularNorm.energy]
  congr 1
  linear_combination (FrameLowMidPrimaryScalars.lam i)^2*(Real.sin_sq_add_cos_sq x)

theorem low_mid_circle_support (second : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (FrameLowMidPrimaryScalars.left true second)
      (FrameLowMidPrimaryScalars.right second))
    (hm : 0≤primary true b B x) :
    FrameLowMidPrimaryScalars.F true second x≤lowMidCost false true b B x := by
  have hs := low_primary_source hb (show (9/10:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hsource : FrameLowMidPrimaryScalars.sourceFloor true≤-L b-(9/10)*A b := by
    dsimp [FrameLowMidPrimaryScalars.sourceFloor]
    linarith [L1_precise.2,a1_precise.2]
  have hscaled := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    ((9/10)*Real.cos x-FrameMidArc.p) ((9/10)*Real.sin x-FrameMidArc.q)
  have hn := norm_identity true x
  norm_num [FrameLowMidPrimaryScalars.lam,FrameLowMidPrimaryScalars.p,
    FrameLowMidPrimaryScalars.q] at hn
  rw [hn] at ht
  have hdom := FrameLowMidPrimaryScalars.quadrant_domain true second hx
  cases second with
  | false =>
      have hq : x∈Icc 0 (Real.pi/2) :=
        ⟨by norm_num [FrameLowMidPrimaryScalars.start] at hdom; linarith [hdom.1],
          by simpa [FrameLowMidPrimaryScalars.right] using hx.2⟩
      dsimp [primary] at hscaled
      rw [(first_width hq).1] at hscaled
      dsimp [lowMidCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,M]
      rw [(first_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith
  | true =>
      have hq : x∈Icc (Real.pi/2) Real.pi :=
        ⟨by simpa [FrameLowMidPrimaryScalars.left] using hx.1,
          by linarith [hdom.2,FrameLowPair.pi_lower]⟩
      dsimp [primary] at hscaled
      rw [(second_width hq).1] at hscaled
      dsimp [lowMidCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,M]
      rw [(second_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith

theorem mid_low_circle_support (second : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (FrameLowMidPrimaryScalars.left false second)
      (FrameLowMidPrimaryScalars.right second))
    (hm : 0≤primary true b B x) :
    FrameLowMidPrimaryScalars.F false second x≤ midLowCost false true b B x := by
  have hs := middle_primary_source hb (show (47/50:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hsource : FrameLowMidPrimaryScalars.sourceFloor false≤-M b-(47/50)*A b := by
    dsimp [FrameLowMidPrimaryScalars.sourceFloor]
    linarith [M_endpoints.2.2.2,a2_bounds.2]
  have hscaled := mul_nonneg (show (0:ℝ)≤47/50 by norm_num) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    ((47/50)*Real.cos x-FrameLowArc.u) ((47/50)*Real.sin x-FrameLowArc.v)
  have hn := norm_identity false x
  norm_num [FrameLowMidPrimaryScalars.lam,FrameLowMidPrimaryScalars.p,
    FrameLowMidPrimaryScalars.q] at hn
  rw [hn] at ht
  have hbase := mul_le_mul_of_nonneg_left a0_precise.1.le
    (show 0≤FrameLowArc.u by norm_num [FrameLowArc.u])
  have hdom := FrameLowMidPrimaryScalars.quadrant_domain false second hx
  cases second with
  | false =>
      have hq : x∈Icc 0 (Real.pi/2) :=
        ⟨by norm_num [FrameLowMidPrimaryScalars.start] at hdom; linarith [hdom.1],
          by simpa [FrameLowMidPrimaryScalars.right] using hx.2⟩
      dsimp [primary] at hscaled
      rw [(first_width hq).1] at hscaled
      dsimp [midLowCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,L]
      rw [(first_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith
  | true =>
      have hq : x∈Icc (Real.pi/2) Real.pi :=
        ⟨by simpa [FrameLowMidPrimaryScalars.left] using hx.1,
          by linarith [hdom.2,FrameLowPair.pi_lower]⟩
      dsimp [primary] at hscaled
      rw [(second_width hq).1] at hscaled
      dsimp [midLowCost,FrameLowMidPrimaryScalars.F,FrameLowMidPrimaryScalars.K,
        FrameLowMidPrimaryScalars.cosCoefficient,FrameLowMidPrimaryScalars.targetConstant,
        FrameLowMidPrimaryScalars.p,FrameLowMidPrimaryScalars.q,FrameLowMidPrimaryScalars.lam,L]
      rw [(second_width hq).2]
      norm_num [sign] at hscaled ⊢
      nlinarith

def endpointA (i : Bool) : ℝ := if i then a1 else a0
def endpointB (i : Bool) : ℝ := if i then b1 else 0
def endpointL (i : Bool) : ℝ := if i then L1 else 0
def endpointF (i : Bool) (x : ℝ) : ℝ :=
  x+59/100-M2-a2+endpointL i+(41/100-endpointB i)*Real.sin x+
    (41/100+endpointA i)*Real.cos x
def endpointD (i : Bool) (x : ℝ) : ℝ :=
  1+(41/100-endpointB i)*Real.cos x-(41/100+endpointA i)*Real.sin x
def endpointDD (i : Bool) (x : ℝ) : ℝ :=
  -(41/100-endpointB i)*Real.sin x-(41/100+endpointA i)*Real.cos x

theorem endpoint_deriv (i : Bool) (x : ℝ) : HasDerivAt (endpointF i) (endpointD i x) x := by
  refine ((((((((hasDerivAt_id x).add_const (59/100)).sub_const M2).sub_const a2).add_const
    (endpointL i)).add ((Real.hasDerivAt_sin x).const_mul (41/100-endpointB i))).add
      ((Real.hasDerivAt_cos x).const_mul (41/100+endpointA i)))).congr_deriv ?_
  rw [endpointD]
  ring

theorem endpointD_deriv (i : Bool) (x : ℝ) : HasDerivAt (endpointD i) (endpointDD i x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (41/100-endpointB i)).const_add 1).sub
    ((Real.hasDerivAt_sin x).const_mul (41/100+endpointA i))) using 1
  · rfl
  · dsimp [endpointDD]; ring

theorem endpoint_coefficients (i : Bool) :
    0≤41/100-endpointB i ∧ 0≤41/100+endpointA i := by
  cases i <;> dsimp [endpointA,endpointB]
  all_goals constructor <;> linarith [FrameLowMidArc.b1_precise.2,a0_precise.1,a1_precise.1]

theorem endpoint_concave (i : Bool) :
    ConcaveOn ℝ (Icc (11/10:ℝ) (7/5)) (endpointF i) := by
  apply concave_of_deriv2 (fun x _ => endpoint_deriv i x) (fun x _ => endpointD_deriv i x)
  intro x hx
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hp := endpoint_coefficients i
  have h1 := mul_nonneg hp.1 ht.1
  have h2 := mul_nonneg hp.2 ht.2.2.1
  dsimp [endpointDD]
  linarith

theorem endpoint_values (i : Bool) :
    (1:ℝ)<endpointF i (11/10:ℝ) ∧ 1<endpointF i (7/5:ℝ) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤11/10 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤11/10 by norm_num)
  have hsU := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/5 by norm_num)
  have hcU := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hsL hcL hsU hcU
  have hs0 : (89/100:ℝ)≤Real.sin (11/10:ℝ) := by linarith
  have hc0 : (9/20:ℝ)≤Real.cos (11/10:ℝ) := by linarith
  have hs1 : (49/50:ℝ)≤Real.sin (7/5:ℝ) := by linarith
  have hc1 : (169/1000:ℝ)≤Real.cos (7/5:ℝ) := by linarith
  have hp := endpoint_coefficients i
  have h1 := mul_le_mul_of_nonneg_left hs0 hp.1
  have h2 := mul_le_mul_of_nonneg_left hc0 hp.2
  have h3 := mul_le_mul_of_nonneg_left hs1 hp.1
  have h4 := mul_le_mul_of_nonneg_left hc1 hp.2
  cases i <;> dsimp [endpointF,endpointA,endpointB,endpointL] at *
  all_goals constructor <;>
    linarith [M_endpoints.2.2.2,a2_bounds.2,a0_precise.1,a1_precise.1,
      FrameLowMidArc.b1_precise.2,L1_precise.1]

theorem endpoint_lower (i : Bool) {x : ℝ} (hx : x∈Icc (11/10:ℝ) (7/5)) :
    (1:ℝ)<endpointF i x :=
  concave_gt_of_endpoints (endpoint_concave i) hx (endpoint_values i).1 (endpoint_values i).2

theorem negative_endpoint_support {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (11/10:ℝ) (7/5)) (hm : 0≤primary false b B x) :
    min (endpointF false x) (endpointF true x)≤ midLowCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := middle_primary_source hb (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have htarget := linear_endpoint_lower (p := FrameLowArc.u+Real.cos x)
    (q := FrameLowArc.v-Real.sin x)
    (by dsimp [FrameLowArc.u]; linarith [ht.2.2.1]) (by norm_num) b1_mem.2 hB
  simp only [linear,A_zero,A_b1,mul_zero,add_zero] at htarget
  dsimp [primary] at hm
  rw [(first_width hxq).1] at hm
  norm_num [sign] at hm
  rcases le_total ((FrameLowArc.u+Real.cos x)*a0)
    ((FrameLowArc.u+Real.cos x)*a1+(FrameLowArc.v-Real.sin x)*b1) with he | he
  · rw [min_eq_left he] at htarget
    apply (min_le_left _ _).trans
    dsimp [endpointF,endpointA,endpointB,endpointL,midLowCost,L]
    rw [(first_width hxq).2]
    norm_num [sign]
    nlinarith
  · rw [min_eq_right he] at htarget
    apply (min_le_right _ _).trans
    dsimp [endpointF,endpointA,endpointB,endpointL,midLowCost,L,L1]
    rw [(first_width hxq).2]
    norm_num [sign]
    nlinarith

theorem low_mid_primary (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : 0≤x)
    (hm : 0≤primary k b B x) : (1801/2000:ℝ)<lowMidCost i k b B x := by
  apply lt_of_lt_of_le _ (low_mid_weaken_source i k hb)
  cases k with
  | false =>
      have hcut := low_mid_negative_cut hb hB hx hm
      exact low_mid_tail false false hb hB (by simpa [lowMidTail] using hcut.le)
  | true =>
      have hcut := low_mid_positive_cut hb hB hx hm
      by_cases htail : (171/100:ℝ)≤x
      · exact low_mid_tail false true hb hB (by simpa [lowMidTail] using htail)
      · by_cases hquad : x≤Real.pi/2
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left true false)
              (FrameLowMidPrimaryScalars.right false) := by
            simpa [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,
              FrameLowMidPrimaryScalars.start] using And.intro hcut.le hquad
          exact (FrameLowMidPrimaryScalars.lower true false hdom).trans_le
            (low_mid_circle_support false hb hB hdom hm)
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left true true)
              (FrameLowMidPrimaryScalars.right true) := by
            simp only [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,ite_true]
            exact ⟨(lt_of_not_ge hquad).le,(lt_of_not_ge htail).le⟩
          exact (FrameLowMidPrimaryScalars.lower true true hdom).trans_le
            (low_mid_circle_support true hb hB hdom hm)

theorem mid_low_primary (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : 0≤x)
    (hm : 0≤primary k b B x) : (1801/2000:ℝ)< midLowCost i k b B x := by
  apply lt_of_lt_of_le _ (mid_low_weaken_source i k hb)
  cases k with
  | false =>
      have hcut := mid_low_negative_cut hb hB hx hm
      by_cases htail : (7/5:ℝ)≤x
      · exact mid_low_tail false false hb hB (by simpa [midLowTail] using htail)
      · have hdom : x∈Icc (11/10:ℝ) (7/5) := ⟨hcut.le,(lt_of_not_ge htail).le⟩
        have hh := (lt_min (endpoint_lower false hdom) (endpoint_lower true hdom)).trans_le
          (negative_endpoint_support hb hB hdom hm)
        linarith
  | true =>
      have hcut := mid_low_positive_cut hb hB hx hm
      by_cases htail : (171/100:ℝ)≤x
      · exact mid_low_tail false true hb hB (by simpa [midLowTail] using htail)
      · by_cases hquad : x≤Real.pi/2
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left false false)
              (FrameLowMidPrimaryScalars.right false) := by
            simpa [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,
              FrameLowMidPrimaryScalars.start] using And.intro hcut.le hquad
          exact (FrameLowMidPrimaryScalars.lower false false hdom).trans_le
            (mid_low_circle_support false hb hB hdom hm)
        · have hdom : x∈Icc (FrameLowMidPrimaryScalars.left false true)
              (FrameLowMidPrimaryScalars.right true) := by
            simp only [FrameLowMidPrimaryScalars.left,FrameLowMidPrimaryScalars.right,ite_true]
            exact ⟨(lt_of_not_ge hquad).le,(lt_of_not_ge htail).le⟩
          exact (FrameLowMidPrimaryScalars.lower false true hdom).trans_le
            (mid_low_circle_support true hb hB hdom hm)

end SquaresInCircles.Eight.FrameLowMidPrimary
