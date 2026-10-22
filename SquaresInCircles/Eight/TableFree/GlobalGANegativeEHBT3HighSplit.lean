module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Blocks

/-!
# The high-total EH1/BT3 split and its actual endpoint functions

Uncompiled Sections 5 and 7. The negative H/G/B increment is fixed
while the original A/BT split varies. The moving D coefficient remains
inside its own circle norm. Its shifted concave part is composed with
the harmonic coefficient, and the existing strict rest-curvature bound
pays the shift. The A-support transition is inherited with matching
first derivatives from the already proved rest theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SplitConcavityTools

lemma full_baseline_concave {k l m θ low : ℝ}
    (hl : 0<l) (hmLow : (9/10)*l≤m) (hmHigh : m≤(11/10)*l)
    (ht : θ∈Icc 0 frameCap) (hlow : 0<low)
    (hc : ∀a∈Icc 0 θ,PositiveTD.tilted m (θ-a)∈Icc low (6/5:ℝ))
    (hrot : ∀a∈Icc 0 θ,PositiveTD.tilted m (θ-a)≤(23/20)*l) :
    ConcaveOn ℝ (Icc 0 θ)
      (fun a => PositiveBT3.Analytic.fullBaseline k l m (θ-a)+l*TwoPositive.ASupport.charge a) := by
  have hm : 0<m := by linarith
  have hcomp := (compose (PositiveBT3.Analytic.shiftedD_concave hlow)
    (PositiveBT3.Analytic.shiftedD_monotone hlow)
    (TwoPositive.Split.tilted_concave hm ht) hc).add
      (PositiveBT3.Analytic.shiftedRest_concave hl hmLow hmHigh ht hrot)
  have hh := TwoPositive.Split.add_constant hcomp
    (PositiveBT3.Analytic.fixedPart k l m θ 0 0-PositiveBT3.Analytic.negative k l m θ 0)
  apply TwoPositive.Split.congr_on hh
  intro a ha
  have he := PositiveBT3.Analytic.large_split_form (k:=k) (l:=l) (m:=m)
    (e:=0) (0:Fin 3) ht ha
  simp only [PositiveBT3.Analytic.largeScalar,TwoPositive.ASupport.charge_zero,
    add_zero] at he
  simp only [Pi.add_apply]
  linarith only [he]

lemma small_high_base_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => baseline .smallHigh θ a (θ-a)) := by
  have hd := Blocks.small_high_domain hθ
  have hb := NonnegativeTotals.Explicit.base_bounds .triangle hd
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have hc (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .smallHigh θ) (θ-a)∈
        Icc (Explicit.k .smallHigh θ) (6/5:ℝ) := by
    have hz : θ-a∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) := by
      simp only [NonnegativeTotals.Explicit.theta]
      constructor <;> linarith [ha.1,ha.2]
    have hh := And.intro (NonnegativeTotals.Explicit.tilted_lower .triangle hd hz).le
      (NonnegativeTotals.Explicit.tilted_upper .triangle hd hz).le
    simpa [Explicit.k,Explicit.m,L,NonnegativeTotals.Explicit.k,
      NonnegativeTotals.Explicit.c,NonnegativeTotals.Explicit.tilted,
      NonnegativeTotals.Explicit.tilt] using hh
  have hrot (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .smallHigh θ) (θ-a)≤(23/20)*Explicit.l .smallHigh θ := by
    have hz : θ-a∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) := by
      simp only [NonnegativeTotals.Explicit.theta]
      constructor <;> linarith [ha.1,ha.2]
    have hh := (NonnegativeTotals.Explicit.tilted_ratio .triangle hd hz).2.le
    simpa [Explicit.l,Explicit.m,L,NonnegativeTotals.Explicit.l,
      NonnegativeTotals.Explicit.c,NonnegativeTotals.Explicit.tilted,
      NonnegativeTotals.Explicit.tilt] using hh
  have hk : 0<Explicit.k .smallHigh θ := by
    change 0<NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0
    linarith [hb.k_lower]
  have hl : 0<Explicit.l .smallHigh θ := hb.l_positive
  have hmL : (9/10)*Explicit.l .smallHigh θ≤Explicit.m .smallHigh θ := hb.c_lower_ratio
  have hmU : Explicit.m .smallHigh θ≤(11/10)*Explicit.l .smallHigh θ := hb.c_upper_ratio
  simpa only [baseline,reduceCtorEq,if_false] using
    full_baseline_concave (k:=Explicit.k .smallHigh θ) hl hmL hmU ht hk hc hrot

lemma far_high_base_concave {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => baseline .farHigh θ a (θ-a)) := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have hl : 0<Explicit.l .farHigh θ := by linarith [hr.2.1.1]
  have hmL : (9/10)*Explicit.l .farHigh θ≤Explicit.m .farHigh θ := by
    change (9/10)*NegativeEHPositiveTD.Explicit.l .far .high θ≤
      NegativeEHPositiveTD.Explicit.c .far .high θ
    linarith [hr.2.1.1,hr.2.2.2.1]
  have hmU : Explicit.m .farHigh θ≤(11/10)*Explicit.l .farHigh θ := by
    change NegativeEHPositiveTD.Explicit.c .far .high θ≤
      (11/10)*NegativeEHPositiveTD.Explicit.l .far .high θ
    linarith [hr.2.1.1,hr.2.2.2.2]
  have hc (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .farHigh θ) (θ-a)∈Icc (3/5:ℝ) (6/5) := by
    have hh := NegativeEHPositiveTD.Explicit.far_high_tilted hθ
      (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)
    have hk := hr.1.1
    change NegativeEHPositiveTD.Explicit.m .far .high θ (θ-a)∈Icc _ _
    exact ⟨by linarith [(lt_min_iff.mp hh.2.2.1).2],
      by linarith [(max_lt_iff.mp hh.2.2.2.1).2]⟩
  have hrot (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .farHigh θ) (θ-a)≤(23/20)*Explicit.l .farHigh θ := by
    exact (NegativeEHPositiveTD.Explicit.far_high_tilted hθ
      (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)).2.2.2.2.le
  simpa only [baseline,reduceCtorEq,if_false] using full_baseline_concave
    (k:=Explicit.k .farHigh θ) hl hmL hmU ht (by norm_num : (0:ℝ)<3/5) hc hrot

lemma small_high_endpoint (ep : Certificate.Split) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    0<baseline .smallHigh θ (EndpointInputs.aAt ep θ) (EndpointInputs.zAt ep θ)+
      charge .smallHigh (1/10)+Blocks.ordinaryV .smallHigh θ i (θ-1/10) := by
  have hx := Endpoints.native_coordinate (.smallHigh i) hθ
  have hc := EndpointInputs.coefficient_bounds (.smallHigh i) hx
  have hk1 : Explicit.k .smallHigh θ≤1 := by
    simpa [EndpointInputs.Kactual,EndpointInputs.thetaAt,Certificate.family] using hc.2.2.2.1
  have hkl : Explicit.k .smallHigh θ≤Explicit.l .smallHigh θ := by
    simpa [EndpointInputs.Kactual,EndpointInputs.Lactual,EndpointInputs.thetaAt,
      Certificate.family] using hc.2.2.2.2
  have hh := Endpoints.original_endpoint_positive (.smallHigh i) ep hθ
  fin_cases i <;>
    simpa [EndpointNorms.value,EndpointNorms.increment,EndpointNorms.pAt,EndpointNorms.qAt,
      EndpointSupport.pairA,EndpointSupport.pairB,EndpointInputs.Kactual,
      EndpointInputs.Lactual,EndpointInputs.Mactual,EndpointInputs.argument,EndpointInputs.thetaAt,
      Certificate.family,Certificate.index,Certificate.equal,Certificate.positive,
      Certificate.gainArgument,Certificate.left,Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,
      min_eq_left hk1,max_eq_right hk1,min_eq_left hkl,max_eq_right hkl,v] using hh

lemma far_high_endpoint (ep : Certificate.Split) (upper : Bool) {θ : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (i : Fin 3) :
    0<baseline .farHigh θ (EndpointInputs.aAt ep θ) (EndpointInputs.zAt ep θ)+
      charge .farHigh (if upper then (1/4:ℝ) else 1/10)+
      Blocks.ordinaryV .farHigh θ i (θ-(if upper then (1/4:ℝ) else 1/10)) := by
  have hx := Endpoints.native_coordinate (.farHigh i upper) hθ
  have hc := EndpointInputs.coefficient_bounds (.farHigh i upper) hx
  have hk1 : Explicit.k .farHigh θ≤1 := by
    simpa [EndpointInputs.Kactual,EndpointInputs.thetaAt,Certificate.family] using hc.2.2.2.1
  have hkl : Explicit.k .farHigh θ≤Explicit.l .farHigh θ := by
    simpa [EndpointInputs.Kactual,EndpointInputs.Lactual,EndpointInputs.thetaAt,
      Certificate.family] using hc.2.2.2.2
  have hh := Endpoints.original_endpoint_positive (.farHigh i upper) ep hθ
  cases upper <;> fin_cases i <;>
    simpa [EndpointNorms.value,EndpointNorms.increment,EndpointNorms.pAt,EndpointNorms.qAt,
      EndpointSupport.pairA,EndpointSupport.pairB,EndpointInputs.Kactual,
      EndpointInputs.Lactual,EndpointInputs.Mactual,EndpointInputs.argument,EndpointInputs.thetaAt,
      Certificate.family,Certificate.index,Certificate.equal,Certificate.positive,
      Certificate.gainArgument,Certificate.left,Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,
      min_eq_left hk1,max_eq_right hk1,min_eq_left hkl,max_eq_right hkl,u,v] using hh

lemma small_high_cut {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh (1/10)+
      Blocks.ordinaryV .smallHigh (a+z) i (a+z-1/10) := by
  have hc := TwoPositive.Split.add_constant (small_high_base_concave hθ)
    (charge .smallHigh (1/10)+Blocks.ordinaryV .smallHigh (a+z) i (a+z-1/10))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using small_high_endpoint .atT hθ i)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using small_high_endpoint .atA hθ i)
  simpa [show a+z-a=z by ring,add_assoc] using hh

lemma far_high_cut (upper : Bool) {a z : ℝ} (hθ : a+z∈Icc (1/4:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<baseline .farHigh (a+z) a z+charge .farHigh (if upper then (1/4:ℝ) else 1/10)+
      Blocks.ordinaryV .farHigh (a+z) i (a+z-(if upper then (1/4:ℝ) else 1/10)) := by
  have hc := TwoPositive.Split.add_constant (far_high_base_concave hθ)
    (charge .farHigh (if upper then (1/4:ℝ) else 1/10)+
      Blocks.ordinaryV .farHigh (a+z) i (a+z-(if upper then (1/4:ℝ) else 1/10)))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using far_high_endpoint .atT upper hθ i)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using far_high_endpoint .atA upper hθ i)
  simpa [show a+z-a=z by ring,add_assoc] using hh

lemma small_high_zero {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<baseline .smallHigh (a+z) a z+Blocks.ordinaryV .smallHigh (a+z) i (a+z) := by
  have hh := PositiveBT3.Analytic.large_scalar_positive .triangle i
    (Blocks.small_high_domain hθ)
    (show a∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (a+z-1/6) 0) by
      simp only [NonnegativeTotals.Explicit.theta]; constructor <;> linarith)
  simpa [PositiveBT3.Analytic.largeScalar,baseline,Blocks.ordinaryV,
    Blocks.ordinaryP,Blocks.ordinaryQ,PositiveBT3.Analytic.negative,
    NonnegativeTotals.Analytic.negative,NonnegativeTotals.Explicit.k,
    NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,NonnegativeTotals.Explicit.theta,
    NonnegativeTotals.Explicit.e,Explicit.k,Explicit.l,Explicit.m,L,
    TwoPositive.ASupport.charge_zero,show a+z-a=z by ring] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.HighSplit
