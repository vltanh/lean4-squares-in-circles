module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3FarLowSplit
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarLowSeparated

/-!
# Complete far-EH, low-total BT3 scalar exclusion

Uncompiled Section 6. All four pure positive alternatives include D;
the negative B/D alternatives are compared with H. Every common-mass
endpoint is paid before the EH magnitude is varied. The original fixed
coefficient angle and A/BT split are unchanged throughout each argument.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.PositiveSlope

lemma positive_monotone {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    MonotoneOn (fun s => charge .farLow s+Blocks.positive .farLow θ z (s-θ) i)
      (Icc (max (1/10) θ) (1/4:ℝ)) := by
  have hp := pair_data hθ hz i
  have hp0 : 0<Blocks.p .farLow θ z i := by linarith [hp.1]
  have hq0 : 0<Blocks.q .farLow θ z i := hp0.trans_le hp.2.1
  have hqp : Blocks.q .farLow θ z i≤2*Blocks.p .farLow θ z i := by linarith [hp.1,hp.2.2.1]
  have hd (s : ℝ) (hs : s∈Icc (max (1/10) θ) (1/4:ℝ)) :=
    ((NegativeEH.G_hasDerivAt s).add
      ((U_hasDerivAt hp0 hq0
        (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1,le_max_right (1/10:ℝ) θ],
          by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)).comp s
            ((hasDerivAt_id s).sub_const θ))).sub
      (((hasDerivAt_id s).sub_const θ).const_mul (1/200))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => by simpa [Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,
      sub_add_eq_add_sub] using (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => by simpa [Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,
      sub_add_eq_add_sub] using hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf : s∈Icc (1/10:ℝ) (1/4) := ⟨(le_max_left _ _).trans hs.1.le,hs.2.le⟩
  have hg := NegativeEH.far_slope hsf
  have hu := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole hp0 hp.2.1 hqp
    (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1,le_max_right (1/10:ℝ) θ],
      by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)
  norm_num only [mul_one]
  linarith [hp.2.2.2]

lemma pure_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : a+z≤s) (i : Fin 4) :
    0<baseline .farLow (a+z) a z+charge .farLow s+
      Blocks.positive .farLow (a+z) z (s-(a+z)) i := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hsm : s∈Icc (max (1/10) (a+z)) (1/4) := ⟨max_le hs.1 horder,hs.2⟩
  by_cases ht : a+z≤1/10
  · have hstart := positive_start ⟨hθ.1,ht⟩ ha hz i
    have hm := positive_monotone hθ hsplit i
      (show (1/10:ℝ)∈Icc (max (1/10) (a+z)) (1/4) by rw [max_eq_left ht]; norm_num)
      hsm hs.1
    linarith
  · have hstart := equal_positive ⟨(lt_of_not_ge ht).le,hθ.2⟩ ha hz
    have hm := positive_monotone hθ hsplit i
      (show a+z∈Icc (max (1/10) (a+z)) (1/4) by
        rw [max_eq_right (lt_of_not_ge ht).le]; exact ⟨le_rfl,hθ.2⟩) hsm horder
    simp only [sub_self,Blocks.positive,ChargedOrdinaryConcentration.positive_zero,add_zero] at hm
    linarith

lemma pure_negative {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : s≤a+z) (i : Fin 4) :
    0<baseline .farLow (a+z) a z+charge .farLow s+
      Blocks.negative .farLow (a+z) z (a+z-s) i := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have htot : a+z∈Icc (1/10:ℝ) (1/4) := ⟨hs.1.trans horder,hθ.2⟩
  have ht : a+z-s∈Icc 0 frameCap := ⟨by linarith,by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩
  obtain ⟨j,hj⟩ := negative_representative hθ hsplit ht i
  have hp := pair_data hθ hsplit j.castSucc.castSucc
  have hpi : 0<Blocks.ordinaryP .farLow (a+z) j.castSucc := by linarith [hp.1]
  have hpq : Blocks.ordinaryP .farLow (a+z) j.castSucc≤Blocks.ordinaryQ .farLow (a+z) j.castSucc := hp.2.1
  have hqp : Blocks.ordinaryQ .farLow (a+z) j.castSucc≤2*Blocks.ordinaryP .farLow (a+z) j.castSucc := by
    linarith [hp.1,hp.2.2.1]
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap]; linarith [hθ.2] : a+z≤frameCap)) (convex_Icc (1/10:ℝ) (a+z))
  have hv := concave_affine_argument (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=a+z)
    (fun t ht => ⟨by linarith [ht.2],by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (baseline .farLow (a+z) a z)
  have hh := concave_gt_of_endpoints hc ⟨hs.1,horder⟩
    (by simpa [Blocks.ordinaryV,neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using
      negative_start htot ha hz j)
    (by simpa [Blocks.ordinaryV,V_zero,neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using
      equal_positive htot ha hz)
  have hpos : 0<baseline .farLow (a+z) a z+charge .farLow s+
      Blocks.ordinaryV .farLow (a+z) j.castSucc (a+z-s) := by
    simpa [Blocks.ordinaryV,neg_one_mul,neg_add_eq_sub,add_comm,add_left_comm,add_assoc] using hh
  linarith

lemma pure_all {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<baseline .farLow (a+z) a z+charge .farLow s+Blocks.pure .farLow (a+z) z s i j := by
  by_cases horder : s≤a+z
  · simpa [Blocks.pure,ChargedOrdinaryConcentration.pure,horder,Blocks.negative] using
      pure_negative hθ ha hz hs horder j
  · simpa [Blocks.pure,ChargedOrdinaryConcentration.pure,horder,Blocks.positive] using
      pure_positive hθ ha hz hs (lt_of_not_ge horder).le i

lemma same_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 4) :
    Blocks.pure .farLow θ z s i i≤Blocks.saturated .farLow θ z s i i := by
  have hp := pair_data hθ hz i
  have hP : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hN : 0≤frameCap-s := by norm_num [frameCap]; linarith [hs.2]
  have hNc : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  have hPc : frameCap-θ≤frameCap := by linarith [hθ.1]
  by_cases horder : s≤θ
  · have hh := NegativeEH.SameBlock.negative_charged hp.1 hp.2.2.1 hP
      (show frameCap-θ≤frameCap-s by linarith) hNc
    simpa [Blocks.pure,Blocks.saturated,ChargedOrdinaryConcentration.pure,
      ChargedOrdinaryConcentration.saturated,ChargedOrdinaryConcentration.block,
      horder,epsilon,far,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  · have hh := NegativeEH.SameBlock.positive_charged hp.1 hp.2.2.1 hN
      (show frameCap-s≤frameCap-θ by linarith) hPc hNc
    simpa [Blocks.pure,Blocks.saturated,ChargedOrdinaryConcentration.pure,
      ChargedOrdinaryConcentration.saturated,ChargedOrdinaryConcentration.block,
      ChargedOrdinaryConcentration.positive,horder,epsilon,far,
      show frameCap-θ-(frameCap-s)=s-θ by ring] using hh

lemma separated_at_left {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) (j : Fin 2) :
    0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
      Blocks.positive .farLow (a+z) z (frameCap-(a+z)) i+
        Blocks.ordinaryV .farLow (a+z) j.castSucc (3/5) := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hu := positive_lower hθ hsplit
    (show frameCap-(a+z)∈Icc 0 frameCap from
      ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩) i
  have hq : Blocks.ordinaryQ .farLow (a+z) j.castSucc∈Icc (91/100:ℝ) 1 := by
    fin_cases j
    · norm_num [Blocks.ordinaryQ]
    · exact (coefficient_ranges hθ hsplit).2.1
  have hv := NegativeEHPositiveTD.FarLowSeparated.negative_at_six hq
  change (31581/70000:ℝ)≤Blocks.ordinaryV .farLow (a+z) j.castSucc (3/5) at hv
  by_cases hlow : a+z≤1/10
  · have hh := positive_start ⟨hθ.1,hlow⟩ ha hz 0
    have hlin := NegativeEH.PositiveD.H_linear_upper (k:=Explicit.k .farLow (a+z))
      (by norm_num [Explicit.k])
      (show 1/10-(a+z)∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.1]⟩)
    have hd : 0≤diagonal-1/2 := by linarith [diagonal_bounds.1]
    have hδ : 0≤1/10-(a+z) := by linarith
    have hpay := mul_nonneg hd hδ
    dsimp [Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,epsilon,far] at hh
    norm_num [frameCap] at hu
    nlinarith [hθ.1]
  · have hh := negative_start ⟨(lt_of_not_ge hlow).le,hθ.2⟩ ha hz 0
    have hH := NegativeEHPositiveTD.FarLowSlopes.H_upper (θ:=a+z) (z:=z)
      (show a+z-1/10∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.2]⟩)
    change Blocks.ordinaryV .farLow (a+z) 0 (a+z-1/10)≤(41/40)*(a+z-1/10) at hH
    norm_num [frameCap] at hu
    nlinarith [hθ.2]

lemma separated_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<baseline .farLow (a+z) a z+charge .farLow s+
      Blocks.positive .farLow (a+z) z (frameCap-(a+z)) i+
        Blocks.negative .farLow (a+z) z (frameCap-s) j := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  obtain ⟨r,hr⟩ := negative_representative hθ hsplit
    (show frameCap-s∈Icc 0 frameCap by
      norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2]) j
  have hq : Blocks.ordinaryQ .farLow (a+z) r.castSucc∈Icc (91/100:ℝ) 1 := by
    fin_cases r
    · norm_num [Blocks.ordinaryQ]
    · exact (coefficient_ranges hθ hsplit).2.1
  have hm := NegativeEHPositiveTD.FarLowSeparated.energy_monotone hq
    (show (1/10:ℝ)∈Icc (1/10:ℝ) (1/4) by norm_num) hs hs.1
  have hleft := separated_at_left hθ ha hz i r
  have hk : Blocks.ordinaryP .farLow (a+z) r.castSucc=121/200 := by
    fin_cases r <;> rfl
  simp only [NegativeEHPositiveTD.FarLowSeparated.energy] at hm
  rw [show frameCap-(1/10:ℝ)=3/5 by norm_num [frameCap]] at hm
  simp only [Blocks.ordinaryV,hk,charge_eq] at hleft hr ⊢
  linarith

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .farLow (a+z) a z+charge .farLow s+
      ∑i,Blocks.block .farLow (a+z) z (P i) (N i) i := by
  have hz' : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hpair (i : Fin 4) : 0<Blocks.p .farLow (a+z) z i ∧
      Blocks.p .farLow (a+z) z i≤Blocks.q .farLow (a+z) z i ∧
      Blocks.q .farLow (a+z) z i≤2*Blocks.p .farLow (a+z) z i := by
    have hp := pair_data hθ hz' i
    exact ⟨by linarith [hp.1],hp.2.1,by linarith [hp.1,hp.2.2.1]⟩
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .farLow P N hpair
    (show a+z∈Icc 0 frameCap from ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩)
    (show s∈Icc 0 frameCap from ⟨by linarith [hs.1],by norm_num [frameCap]; linarith [hs.2]⟩)
    hP hN hPb hNb hbalance
  have hp := pure_all hθ ha hz hs i j
  have ht : 0<baseline .farLow (a+z) a z+charge .farLow s+
      Blocks.saturated .farLow (a+z) z s i j := by
    by_cases he : i=j
    · subst j
      linarith [same_lower hθ hz' hs i]
    · simpa [Blocks.saturated,ChargedOrdinaryConcentration.saturated,he,
        Blocks.positive,Blocks.negative,add_assoc] using separated_positive hθ ha hz hs i j
  have hm : -(baseline .farLow (a+z) a z+charge .farLow s)<
      min (Blocks.pure .farLow (a+z) z s i j) (Blocks.saturated .farLow (a+z) z s i j) :=
    lt_min (by linarith) (by linarith)
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.FarLow
