module

public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ANormalForm
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3FarLowSplit
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSeparated

/-!
# Eight squares: complete far-EH, low-total BT3 scalar exclusion

All four pure positive alternatives include D;
the negative B/D alternatives are compared with H. Every common-mass
endpoint is paid before the EH magnitude is varied. The original fixed
coefficient angle and A/BT split are unchanged throughout each argument.
-/

section
/-!
## Both negative A primaries use the written G5 reflection

The reflected triple is (B*,A*,G*). Original AB2 becomes HG0 and
original GA3 becomes GA1, so the existing flat-core transport applies
literally. Its strict core and containment facts are pulled back before
the aligned secondary owner is selected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
open Candidate Secondary MixedNegativeA

def Result.rebase {Q θG θA θA' θB : ℝ} {G A A' B : SignedPoint}
    (R : Result Q G A' B θG θA' θB)
    (hframe : θA'=θA ∨ θA'=θG ∨ θA'=θB) : Result Q G A B θG θA θB where
  point := R.point
  theta := R.theta
  ga := R.ga
  ab := R.ab
  sorted := R.sorted
  contained := R.contained
  core := R.core
  radial := R.radial
  tangent_upper := R.tangent_upper
  frame := by
    rcases R.frame with hh|hh|hh
    · rw [hh]
      exact hframe
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  GA := R.GA
  AB := R.AB
  reduced := R.reduced

theorem flat_high_tangent_upper {G A : SignedPoint} {s : ℝ}
    (hG : G.a<283/200) (hflat : A.a=7/12)
    (hs : s∈Icc 0 frameCap) (hGA : quarterFeasible G A (-s) 3) : A.y<1/2 := by
  have ht := transport_trig hs
  have hc : 0≤Real.cos s := by linarith [ht.1]
  have hsum := one_le_abs_cos_add_abs_sin s
  rw [abs_of_nonneg hc,abs_of_nonneg ht.2.2.1] at hsum
  by_contra! hbad
  have hy := mul_le_mul_of_nonneg_right hbad hc
  dsimp [quarterFeasible,quarterProjection] at hGA
  simp only [Real.cos_neg,Real.sin_neg,hflat] at hGA
  rw [edgeWidth_negative_formula hs] at hGA
  nlinarith only [hGA,hy,hsum,hG,ht.2.2.1]

theorem both_negative {Q θG θA θB : ℝ} {G A B : SignedPoint}
    (hQ : Q≤qCap)
    (hGs : G.Sorted) (hGc : G.Contained Q) (hGcore : G.AvoidsCore)
    (hGy : G.y≤0) (hGupper : G.a<283/200)
    (hAs : A.Sorted) (hAc : A.Contained Q) (hAcore : A.AvoidsCore)
    (hflat : A.a=7/12) (hAy : 0<A.y)
    (hBs : B.Sorted) (hBc : B.Contained Q) (hBcore : B.AvoidsCore)
    (hBo : B.Outer Q) (hBy : B.y≤0)
    (hu : θA<θG) (hv : θB<θA)
    (hspan : |θG-θB|≤frameCap)
    (hGA : quarterFeasible G A (θA-θG) 3)
    (hAB : zeroFeasible A B (θB-θA) 2) :
    Nonempty (Result Q G A B θG θA θB) := by
  let z : ℝ := θG-θA
  let Θ : ℝ := θG-θB
  have hz : 0<z ∧ z≤7/10 := by
    dsimp [z]
    dsimp [frameCap] at hspan
    exact ⟨by linarith,by linarith [(le_abs_self (θG-θB)).trans hspan]⟩
  have hΘ : |Θ|≤(7/10:ℝ) := by simpa [Θ,frameCap] using hspan
  have hgap : |z-Θ|≤(7/10:ℝ) := by
    apply abs_le.mpr
    have hb := abs_le.mp hΘ
    dsimp [z,Θ] at *
    constructor <;> linarith
  have hHG : zeroFeasible B.reflect A.reflect (z-Θ) 0 := by
    have hh := (zeroFeasible_reflect A B (θB-θA) 2).2 hAB
    convert hh using 1 <;> try rfl
    dsimp [z,Θ]
    ring
  have hGA' : quarterFeasible A.reflect G.reflect (-z) 1 := by
    have hh := (quarterFeasible_reflect G A (θA-θG) 3).2 hGA
    convert hh using 1 <;> try rfl
    dsimp [z]
    ring
  obtain ⟨P,x,hPa,hendpoint,hx,hPs,hPcore,hPavoid,hPcircle,hzero,hquarter,hhard,hstrict,hPy⟩ :=
    flat_core_negative_ga1_hg0_transport (H:=B.reflect) (G:=A.reflect) (A:=G.reflect) hQ
      (by simpa using hBs) (by simpa using hAs) (by simpa using hGs)
      (by simpa using hBc) (by simpa using hAc) (by simpa using hGc)
      (by simpa using hBcore) (by simpa using hAcore) (by simpa using hGcore)
      (by simpa [SignedPoint.reflect] using hflat) (by simpa [SignedPoint.reflect] using hAy.le)
      hz hΘ hgap hHG hGA'
  let A' := P.reflect
  let θ' := θG-x
  have hAs' : A'.Sorted := by simpa [A'] using hPs
  have hAc' : A'.Contained Q := by simpa [A',SignedPoint.Contained] using hPcircle.le
  have hAcore' : A'.AvoidsCore := by simpa [A'] using hPavoid
  have hAr' : A'.Boundary Q := Or.inr (by simpa [A'] using hPcore)
  have hflat' : A'.a=7/12 := by simpa [A',SignedPoint.reflect,hflat] using hPa
  have hAy' : 0<A'.y := by simpa [A',SignedPoint.reflect] using neg_pos.mpr hPy
  have hxdom : x∈Icc 0 frameCap := by
    rcases hendpoint with hh|hh
    · rw [hh]
      norm_num [frameCap]
    · rw [hh]
      dsimp [Θ]
      exact ⟨by linarith,(le_abs_self _).trans hspan⟩
  have hnewGA : quarterFeasible G A' (θ'-θG) 3 := by
    have hh := (quarterFeasible_reflect P G.reflect (-x) 1).2 hquarter
    simpa [θ',A',reflectedOwner] using hh
  have hnewAB : zeroFeasible A' B (θB-θ') 2 := by
    have hh := (zeroFeasible_reflect B.reflect P (x-Θ) 0).2 hzero
    convert hh using 1 <;> try simp [reflectedOwner]
    dsimp [θ',Θ]
    ring
  have hAyupper : A'.y<1/2 := by
    apply flat_high_tangent_upper hGupper hflat' hxdom
    simpa [θ'] using hnewGA
  have hframe : θ'=θG ∨ θ'=θB := by
    rcases hendpoint with hh|hh
    · exact Or.inl (by simp [θ',hh])
    · exact Or.inr (by dsimp [θ',Θ] at *; linarith)
  have hu' : |θ'-θG|≤frameCap := by
    rw [show θ'-θG= -x by dsimp [θ']; ring,abs_neg,abs_of_nonneg hxdom.1]
    exact hxdom.2
  have hv' : |θB-θ'|≤frameCap := by
    rcases hframe with hh|hh
    · rw [hh,abs_sub_comm]
      exact hspan
    · rw [hh,sub_self,abs_zero]
      norm_num [frameCap]
  have hAouter' : A'.y≤0 → A'.Outer Q := by intro hh; linarith
  rcases hframe with hleft|hright
  · have hGA2 : quarterFeasible G A' (θ'-θG) 2 := by
      rw [hleft,sub_self] at hnewGA ⊢
      exact (quarter_high_tie G A').2 hnewGA
    obtain ⟨R⟩ := single false true (Or.inl rfl) hGs hGc hGy
      hAs' hAc' hAcore' hAr' hAyupper hAouter' hBs hBo hBy hQ hu' hv' hGA2 hnewAB
    exact ⟨R.rebase (Or.inr (Or.inl hleft))⟩
  · have hAB0 : zeroFeasible A' B (θB-θ') 0 := by
      rw [hright,sub_self] at hnewAB ⊢
      exact (zero_owner_tie A' B).2 hnewAB
    obtain ⟨R⟩ := single true false (Or.inr rfl) hGs hGc hGy
      hAs' hAc' hAcore' hAr' hAyupper hAouter' hBs hBo hBy hQ hu' hv' hnewGA hAB0
    exact ⟨R.rebase (Or.inr (Or.inr hright))⟩

end SquaresInCircles.Eight.GlobalGA.NegativeANormalForm
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.PositiveSlope

private lemma r76_fl_ordinaryP_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryP f θ i=Blocks.p f θ z i.castSucc := by
  fin_cases i <;> rfl

private lemma r76_fl_ordinaryQ_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryQ f θ i=Blocks.q f θ z i.castSucc := by
  fin_cases i <;> rfl

lemma positive_monotone {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    MonotoneOn (fun s => charge .farLow s+Blocks.positive .farLow θ z (s-θ) i)
      (Icc (max (1/10) θ) (1/4:ℝ)) := by
  have hp := pair_data hθ hz i
  have hp0 : 0<Blocks.p .farLow θ z i := by linarith [hp.1]
  have hq0 : 0<Blocks.q .farLow θ z i := hp0.trans_le hp.2.1
  have hqp : Blocks.q .farLow θ z i≤2*Blocks.p .farLow θ z i := by linarith [hp.1,hp.2.2.1]
  have e : (fun s => charge .farLow s+Blocks.positive .farLow θ z (s-θ) i)=
      fun s => NegativeEH.G s+U R (Blocks.p .farLow θ z i) (Blocks.q .farLow θ z i) (s-θ)-
        1/200*(s-θ) := by
    funext x
    simp only [charge_eq,Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,
      ↓reduceIte]
    ring
  have hd (s : ℝ) (hs : s∈Icc (max (1/10) θ) (1/4:ℝ)) :
      HasDerivAt (fun s => NegativeEH.G s+U R (Blocks.p .farLow θ z i) (Blocks.q .farLow θ z i) (s-θ)-
        1/200*(s-θ))
        (NegativeEH.GD s+Ud (Blocks.p .farLow θ z i) (Blocks.q .farLow θ z i) (s-θ)*1-1/200*1) s := by
    have hU : HasDerivAt (U R (Blocks.p .farLow θ z i) (Blocks.q .farLow θ z i))
        (Ud (Blocks.p .farLow θ z i) (Blocks.q .farLow θ z i) (s-θ)) (s-θ) :=
      U_hasDerivAt hp0 hq0
        (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1,le_max_right (1/10:ℝ) θ],
          by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)
    have h := ((NegativeEH.G_hasDerivAt s).add (hU.comp s ((hasDerivAt_id' s).sub_const θ))).sub
      (((hasDerivAt_id' s).sub_const θ).const_mul (1/200))
    exact h
  rw [e]
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf : s∈Icc (1/10:ℝ) (1/4) := ⟨(le_max_left _ _).trans hs.1.le,hs.2.le⟩
  have hg := NegativeEH.far_slope hsf
  have hu := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole hp0 hp.2.1 hqp
    (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1,le_max_right (1/10:ℝ) θ],
      by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)
  linarith [hp.2.2.2]

lemma pure_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : a+z≤ s) (i : Fin 4) :
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
    simp only [Blocks.positive]
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
  have hpi : 0<Blocks.ordinaryP .farLow (a+z) j.castSucc := by
    rw [r76_fl_ordinaryP_eq _ _ z]; linarith [hp.1]
  have hpq : Blocks.ordinaryP .farLow (a+z) j.castSucc≤Blocks.ordinaryQ .farLow (a+z) j.castSucc := by
    rw [r76_fl_ordinaryP_eq _ _ z,r76_fl_ordinaryQ_eq _ _ z]; exact hp.2.1
  have hqp : Blocks.ordinaryQ .farLow (a+z) j.castSucc≤2*Blocks.ordinaryP .farLow (a+z) j.castSucc := by
    rw [r76_fl_ordinaryP_eq _ _ z,r76_fl_ordinaryQ_eq _ _ z]; linarith [hp.1,hp.2.2.1]
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap]; linarith [hθ.2] : a+z≤frameCap)) (convex_Icc (1/10:ℝ) (a+z))
  have hv := concave_affine_argument (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=a+z)
    (fun t ht => ⟨by linarith [ht.2],by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc (1/10) (a+z)) (fun t => baseline .farLow (a+z) a z+charge .farLow t+
      Blocks.ordinaryV .farLow (a+z) j.castSucc (a+z-t)) := by
    refine ((hg.add hv).add_const (baseline .farLow (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,charge_eq,Blocks.ordinaryV]
    ring
  have h1 : 0<baseline .farLow (a+z) a z+charge .farLow (a+z)+
      Blocks.ordinaryV .farLow (a+z) j.castSucc (a+z-(a+z)) := by
    have hV : Blocks.ordinaryV .farLow (a+z) j.castSucc 0=0 := by simp [Blocks.ordinaryV,V]
    rw [sub_self,hV,add_zero]
    exact equal_positive htot ha hz
  have hpos := concave_gt_of_endpoints hc ⟨hs.1,horder⟩ (negative_start htot ha hz j) h1
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
  have hk : Blocks.ordinaryP .farLow (a+z) j.castSucc=121/200 := by
    fin_cases j <;> rfl
  rw [← hk] at hv
  change (31581/70000:ℝ)≤Blocks.ordinaryV .farLow (a+z) j.castSucc (3/5) at hv
  by_cases hlow : a+z≤1/10
  · have hh := positive_start ⟨hθ.1,hlow⟩ ha hz 0
    have hlin := NegativeEH.PositiveD.H_linear_upper (k:=Explicit.k .farLow (a+z))
      (by norm_num [Explicit.k])
      (show 1/10-(a+z)∈Icc 0 frameCap from
        ⟨by linarith,by norm_num [frameCap]; linarith [hθ.1]⟩)
    have hd : 0≤Secondary.diagonal-1/2 := by linarith [diagonal_bounds.1]
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
    have hh' : 0<baseline .farLow (a+z) a z+charge .farLow (1/10)+
        Blocks.ordinaryV .farLow (a+z) 0 (a+z-1/10) := hh
    simp only [frameCap] at hu ⊢
    linarith [hθ.2]

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

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
end
end
end
