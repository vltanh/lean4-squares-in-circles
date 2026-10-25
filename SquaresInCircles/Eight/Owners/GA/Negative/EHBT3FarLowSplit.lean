module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3FarLowInputs

/-!
# Eight squares: every far-low intrinsic endpoint at the original A/BT split

The positive D alternative is kept explicitly.
Its shifted coefficient function is concave and increasing on the
whole coefficient rectangle; the short-angle rest curvature pays the
shift. The other five endpoint forms have a fixed ordinary increment.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open SplitConcavityTools

@[simp] lemma charge_eq (s : ℝ) : charge .farLow s=NegativeEH.G s := by
  dsimp [charge,far,gain,NegativeEH.G,NegativeEH.g,NegativeEH.K,NegativeEH.beta,NegativeEH.p]

def shiftedCoefficient (δ c : ℝ) : ℝ := TwoPositive.Coefficient.affineBranch 1 δ (1/25) 0 c

def shiftedRest (m l θ a : ℝ) : ℝ :=
  TwoPositive.Split.rest m l θ a-(1/25)*PositiveTD.tilted m (θ-a)

lemma coefficient_slope {δ c : ℝ} (hδ : δ∈Icc (0:ℝ) (1/10))
    (hc : c∈Icc (1/2:ℝ) (111/100)) :
    R*TwoPositive.Coefficient.normD 1 δ c<(77/50:ℝ) := by
  have hdf : δ∈Icc 0 frameCap := ⟨hδ.1,by norm_num [frameCap]; linarith [hδ.2]⟩
  have hc0 : 0<c := by linarith [hc.1]
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<1) hc0
    (show |δ|≤frameCap by rw [abs_of_nonneg hδ.1]; exact hdf.2)
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<1) hc0
    (show |δ|≤frameCap by rw [abs_of_nonneg hδ.1]; exact hdf.2)
  have hs0 := (transport_trig hdf).2.2.1
  have hs1 : Real.sin δ≤1/10 := (Real.sin_le hδ.1).trans hδ.2
  have hc2 := pow_le_pow_left₀ hc0.le hc.2 2
  have hs2 := pow_le_pow_left₀ hs0 hs1 2
  have hcs := mul_le_mul hc.2 hs1 hs0 (by norm_num : (0:ℝ)≤111/100)
  have hpoly : 0<(77/50:ℝ)^2*(1+c^2+2*c*Real.sin δ)-qCap*(c+Real.sin δ)^2 := by
    norm_num [qCap] at *
    nlinarith only [hc2,hs2,hcs]
  have hsq : (R*(c+Real.sin δ))^2<(77/50:ℝ)^2*(pairNorm 1 c δ)^2 := by
    rw [mul_pow,radius_sq]
    simp only [pairEnergy,pairProduct,one_pow,one_mul] at hn2
    nlinarith only [hpoly,hn2]
  have hh := OrdinaryCurvatureBounds.quotient_lt_of_square hn (by norm_num : (0:ℝ)<77/50) hsq
  have e : R*TwoPositive.Coefficient.normD 1 δ c=R*(c+Real.sin δ)/pairNorm 1 c δ := by
    simp only [TwoPositive.Coefficient.normD,one_mul]
    ring
  rw [e]
  exact hh

lemma coefficient_concave {δ : ℝ} (hδ : δ∈Icc (0:ℝ) (1/10)) :
    ConcaveOn ℝ (Icc (1/2:ℝ) (111/100)) (shiftedCoefficient δ) := by
  apply TwoPositive.Coefficient.affine_concave (by norm_num) (by norm_num)
  rw [abs_of_nonneg hδ.1]
  norm_num [frameCap]
  linarith [hδ.2]

lemma coefficient_monotone {δ : ℝ} (hδ : δ∈Icc (0:ℝ) (1/10)) :
    MonotoneOn (shiftedCoefficient δ) (Icc (1/2:ℝ) (111/100)) := by
  have hd : |δ|≤frameCap := by rw [abs_of_nonneg hδ.1]; norm_num [frameCap]; linarith [hδ.2]
  apply monoOn_of_hasDeriv_nonneg
  · intro c hc
    exact (TwoPositive.Coefficient.affine_derivative (w:=1/25) (b:=0)
      (by norm_num : (0:ℝ)<1) (by linarith [hc.1]) hd).continuousAt.continuousWithinAt
  · intro c hc
    exact TwoPositive.Coefficient.affine_derivative (w:=1/25) (b:=0)
      (by norm_num : (0:ℝ)<1) (by linarith [hc.1]) hd
  · intro c hc
    have hh := coefficient_slope hδ (Ioo_subset_Icc_self hc)
    dsimp [TwoPositive.Coefficient.affineD]
    linarith

lemma short_rest_curvature {m l θ a d : ℝ}
    (hl : 0<l) (hmL : l≤ m) (hmU : m≤(111/100)*l)
    (hθ : θ∈Icc (0:ℝ) (1/4)) (ha : a∈Icc 0 θ)
    (hc : PositiveTD.tilted m (θ-a)≤(117/100)*l)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    TwoPositive.Split.smoothDD m θ a+l*d+(1/25)*PositiveTD.tilted m (θ-a)<0 := by
  have hm : 0< m := hl.trans_le hmL
  have hz : θ-a∈Icc (0:ℝ) (1/4) := ⟨by linarith [ha.2],by linarith [ha.1,hθ.2]⟩
  have ha' : a∈Icc (0:ℝ) (1/4) := ⟨ha.1,ha.2.trans hθ.2⟩
  have hca : (31/32:ℝ)≤Real.cos a := by
    have hh := Real.one_sub_sq_div_two_le_cos (x:=a)
    have ha2 := pow_le_pow_left₀ ha.1 ha'.2 2
    nlinarith
  have hcz : (31/32:ℝ)≤Real.cos (θ-a) := by
    have hh := Real.one_sub_sq_div_two_le_cos (x:=θ-a)
    have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
    nlinarith
  have haf : a∈Icc 0 frameCap := ⟨ha.1,by norm_num [frameCap]; linarith [ha'.2]⟩
  have hzf : θ-a∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩
  have hsa := (transport_trig haf).2.2.1
  have hsz := (transport_trig hzf).2.2.1
  have hcosM := mul_le_mul_of_nonneg_right hmL (show 0≤Real.cos (θ-a) by linarith)
  have hcosA := mul_le_mul_of_nonneg_left hca hl.le
  have hcosZ := mul_le_mul_of_nonneg_left hcz hl.le
  have hsigma := mul_le_mul_of_nonneg_right
    (show PositiveTD.sigma-1/2≤229/250 by linarith [TwoPositive.Split.sigma_bound]) hsz
  have hsigmaM := mul_le_mul_of_nonneg_left hsigma hm.le
  have hsinM := mul_le_mul_of_nonneg_right hmU hsz
  have hsinSum : Real.sin a+Real.sin (θ-a)≤1/4 := by
    linarith [Real.sin_le ha.1,Real.sin_le hz.1,hθ.2]
  have hsinL := mul_le_mul_of_nonneg_left hsinSum hl.le
  have hsinAL := mul_nonneg hl.le hsa
  have hdL := mul_le_mul_of_nonneg_left hd hl.le
  dsimp [TwoPositive.Split.smoothDD]
  nlinarith only [hcosM,hcosA,hcosZ,hsigmaM,hsinM,hsinL,hsinAL,hdL,hc,hl]

lemma rest_concave {m l θ : ℝ}
    (hl : 0<l) (hmL : l≤ m) (hmU : m≤(111/100)*l)
    (hθ : θ∈Icc (0:ℝ) (1/4))
    (hc : ∀a∈Icc 0 θ,PositiveTD.tilted m (θ-a)≤(117/100)*l) :
    ConcaveOn ℝ (Icc 0 θ) (shiftedRest m l θ) := by
  have hax : ConcaveOn ℝ (Icc 0 θ) (TwoPositive.Split.axialRest (1/25) m l θ) := by
    apply concave_of_deriv2
      (fun a _ => TwoPositive.Split.axial_derivative (1/25) m l θ a)
      (fun a _ => TwoPositive.Split.axial_second (1/25) m l θ a)
    intro a ha
    have haf : a∈Icc 0 frameCap := ⟨ha.1,by norm_num [frameCap]; linarith [ha.2,hθ.2]⟩
    exact (short_rest_curvature hl hmL hmU hθ ha (hc a ha)
      (TwoPositive.Split.high_axial_bound haf)).le
  apply TwoPositive.Split.congr_on hax
  intro a ha
  have hcut : a≤TwoPositive.ASupport.alpha := by linarith [ha.2,hθ.2,TwoPositive.ASupport.alpha_bounds.1]
  simp [TwoPositive.Split.axialRest,shiftedRest,TwoPositive.Split.rest,TwoPositive.ASupport.charge,hcut]

lemma with_D_concave {θ δ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hδ : δ∈Icc (0:ℝ) (1/10)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => baseline .farLow θ a (θ-a)+
      U R 1 (Explicit.c .farLow θ (θ-a)) δ) := by
  have hr := coefficient_ranges hθ (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,hθ.1⟩)
  have hl : 0<Explicit.l .farLow θ := by linarith [hr.2.1.1]
  have hm : 0<Explicit.m .farLow θ := by linarith [hr.2.2.1.1]
  have hmU : Explicit.m .farLow θ≤(111/100)*Explicit.l .farLow θ := by
    dsimp [Explicit.m,Explicit.l]
    linarith [hθ.1]
  have ht : θ∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  have hcoef (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .farLow θ) (θ-a)∈Icc (1/2:ℝ) (111/100) := by
    have hh := coefficient_ranges (z:=θ-a) hθ ⟨by linarith [ha.2],by linarith [ha.1]⟩
    change Explicit.c .farLow θ (θ-a)∈Icc _ _
    exact ⟨by linarith [hh.2.2.1.1,hh.2.2.2.2.1],hh.2.2.2.2.2.1⟩
  have hrot (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .farLow θ) (θ-a)≤(117/100)*Explicit.l .farLow θ :=
    (coefficient_ranges (z:=θ-a) hθ ⟨by linarith [ha.2],by linarith [ha.1]⟩).2.2.2.2.2.2.le
  have hc := (compose (coefficient_concave hδ) (coefficient_monotone hδ)
    (TwoPositive.Split.tilted_concave hm ht) hcoef).add
      (rest_concave hl hr.2.2.2.1.le hmU hθ hrot)
  let fixed : ℝ := Explicit.k .farLow θ+2*Explicit.l .farLow θ+5/2-
    fullSupport 1 (Explicit.k .farLow θ)-fullSupport (Explicit.l .farLow θ) (Explicit.k .farLow θ)-
    fullSupport (Explicit.m .farLow θ) (Explicit.l .farLow θ)+PositiveAngularEnvelope.phi δ-1
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hc fixed)
  intro a ha
  have hz : θ-a∈Icc 0 frameCap := ⟨by linarith [ha.2],by linarith [ha.1,ht.2]⟩
  have hs := TwoPositive.Split.smooth_actual (c:=Explicit.m .farLow θ) hz
  simp only [Pi.add_apply,baseline,reduceCtorEq,↓reduceIte,PositiveBT3.Analytic.fullBaseline,
    U,shiftedCoefficient,TwoPositive.Coefficient.affineBranch,shiftedRest,TwoPositive.Split.rest]
  rw [fullSupport_pair (PositiveBT3.tilted (Explicit.m .farLow θ) (θ-a)) 1,
    pairNorm_symm (PositiveBT3.tilted (Explicit.m .farLow θ) (θ-a)) 1,hs]
  dsimp [fixed,Explicit.c,PositiveBT3.tilted,PositiveTD.tilted]
  ring

lemma base_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => baseline .farLow θ a (θ-a)) := by
  simpa only [U_zero,add_zero] using with_D_concave hθ (show (0:ℝ)∈Icc 0 (1/10:ℝ) by norm_num)

lemma equal_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) : 0<baseline .farLow (a+z) a z+charge .farLow (a+z) := by
  have hc := TwoPositive.Split.add_constant
    (base_concave (show a+z∈Icc (0:ℝ) (1/4) from ⟨by linarith [hθ.1],hθ.2⟩)) (charge .farLow (a+z))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using Endpoints.far_low_equal .atT hθ)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using Endpoints.far_low_equal .atA hθ)
  simpa [show a+z-a=z by ring] using hh

lemma positive_endpoint (ep : Certificate.Split) {θ : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/10)) (i : Fin 3) :
    0<baseline .farLow θ (EndpointInputs.aAt ep θ) (EndpointInputs.zAt ep θ)+charge .farLow (1/10)+
      Blocks.positive .farLow θ (EndpointInputs.zAt ep θ) (1/10-θ) (![0,2,3] i) := by
  have hθ' : θ∈Icc ((Certificate.left (.farPositive i):ℚ):ℝ) (Certificate.right (.farPositive i)) := by
    norm_num [Certificate.left,Certificate.right]; exact hθ
  have hh := Endpoints.original_endpoint_positive (.farPositive i) ep hθ'
  have hk : Explicit.k .farLow θ≤1 := by norm_num [Explicit.k]
  fin_cases i <;>
    simpa [EndpointNorms.value,EndpointNorms.increment,EndpointNorms.pAt,EndpointNorms.qAt,
      EndpointSupport.pairA,EndpointSupport.pairB,EndpointInputs.Kactual,EndpointInputs.Lactual,
      EndpointInputs.Mactual,EndpointInputs.Cactual,EndpointInputs.argument,EndpointInputs.thetaAt,
      Certificate.family,Certificate.index,Certificate.equal,Certificate.positive,Certificate.gainArgument,
      Certificate.left,Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,min_eq_left hk,max_eq_right hk,epsilon,far,v] using hh

lemma positive_start {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) :
    0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.positive .farLow (a+z) z (1/10-(a+z)) i := by
  have ht : a+z∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hd : 1/10-(a+z)∈Icc (0:ℝ) (1/10) := ⟨by linarith [hθ.2],by linarith [hθ.1]⟩
  have hs : a∈Icc 0 (a+z) := ⟨ha,by linarith⟩
  have gen (j : Fin 4) (hc : ConcaveOn ℝ (Icc 0 (a+z)) (fun b =>
        baseline .farLow (a+z) b (a+z-b)+charge .farLow (1/10)+
          Blocks.positive .farLow (a+z) (a+z-b) (1/10-(a+z)) j))
      (hT : 0<baseline .farLow (a+z) 0 (a+z)+charge .farLow (1/10)+
        Blocks.positive .farLow (a+z) (a+z) (1/10-(a+z)) j)
      (hA : 0<baseline .farLow (a+z) (a+z) 0+charge .farLow (1/10)+
        Blocks.positive .farLow (a+z) 0 (1/10-(a+z)) j) :
      0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
        Blocks.positive .farLow (a+z) z (1/10-(a+z)) j := by
    have hh := concave_gt_of_endpoints hc hs (by simpa using hT) (by simpa using hA)
    simpa [show a+z-a=z by ring] using hh
  have h0 : 0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.positive .farLow (a+z) z (1/10-(a+z)) 0 := by
    refine gen 0 ?_
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atT hθ 0)
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atA hθ 0)
    refine (TwoPositive.Split.add_constant (base_concave ht)
      (charge .farLow (1/10)+(U R (Explicit.k .farLow (a+z)) 1 (1/10-(a+z))-
        epsilon .farLow*(1/10-(a+z))))).congr ?_
    intro b _
    simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,Matrix.cons_val_zero]
    ring
  have h2 : 0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.positive .farLow (a+z) z (1/10-(a+z)) 2 := by
    refine gen 2 ?_
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atT hθ 1)
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atA hθ 1)
    refine (TwoPositive.Split.add_constant (base_concave ht)
      (charge .farLow (1/10)+(U R (min (Explicit.l .farLow (a+z)) (Explicit.m .farLow (a+z)))
        (max (Explicit.l .farLow (a+z)) (Explicit.m .farLow (a+z))) (1/10-(a+z))-
          epsilon .farLow*(1/10-(a+z))))).congr ?_
    intro b _
    simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,Matrix.cons_val]
    ring
  have h3 : 0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.positive .farLow (a+z) z (1/10-(a+z)) 3 := by
    refine gen 3 ?_
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atT hθ 2)
      (by simpa [EndpointInputs.aAt,EndpointInputs.zAt] using positive_endpoint .atA hθ 2)
    refine (TwoPositive.Split.add_constant (with_D_concave ht hd)
      (charge .farLow (1/10)-epsilon .farLow*(1/10-(a+z)))).congr ?_
    intro b hb
    have hcb := small_total_c_ge_one (z:=a+z-b) hθ ⟨by linarith [hb.2],by linarith [hb.1]⟩
    simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,Matrix.cons_val,
      min_eq_left hcb,max_eq_right hcb]
    ring
  fin_cases i
  · exact h0
  · have hcmp := positive_HG ht ⟨hz,by linarith⟩
      (show 1/10-(a+z)∈Icc 0 frameCap from ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩)
    exact h0.trans_le (add_le_add le_rfl hcmp)
  · exact h2
  · exact h3

lemma negative_start {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 2) :
    0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.ordinaryV .farLow (a+z) i.castSucc (a+z-1/10) := by
  have ht : a+z∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hpair := coefficient_ranges ht ⟨hz,by linarith⟩
  have hk1 : Explicit.k .farLow (a+z)≤1 := by norm_num [Explicit.k]
  have hkl : Explicit.k .farLow (a+z)≤Explicit.l .farLow (a+z) := by
    rw [hpair.1]; linarith [hpair.2.1.1]
  have he (ep : Certificate.Split) :
      0<baseline .farLow (a+z) (EndpointInputs.aAt ep (a+z)) (EndpointInputs.zAt ep (a+z))+
        charge .farLow (1/10)+Blocks.ordinaryV .farLow (a+z) i.castSucc (a+z-1/10) := by
    have hθ' : a+z∈Icc ((Certificate.left (.farNegative i):ℚ):ℝ)
        (Certificate.right (.farNegative i)) := by
      norm_num [Certificate.left,Certificate.right]; exact hθ
    have hh := Endpoints.original_endpoint_positive (.farNegative i) ep hθ'
    fin_cases i <;>
      simpa [EndpointNorms.value,EndpointNorms.increment,EndpointNorms.pAt,EndpointNorms.qAt,
        EndpointSupport.pairA,EndpointSupport.pairB,EndpointInputs.Kactual,EndpointInputs.Lactual,
        EndpointInputs.Mactual,EndpointInputs.argument,EndpointInputs.thetaAt,
        Certificate.family,Certificate.index,Certificate.equal,Certificate.positive,Certificate.gainArgument,
        Certificate.left,Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,
        min_eq_left hk1,max_eq_right hk1,min_eq_left hkl,max_eq_right hkl,v] using hh
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (charge .farLow (1/10)+Blocks.ordinaryV .farLow (a+z) i.castSucc (a+z-1/10))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using he .atT)
    (by simpa [EndpointInputs.aAt,EndpointInputs.zAt,add_assoc] using he .atA)
  simpa [show a+z-a=z by ring,add_assoc] using hh


end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
