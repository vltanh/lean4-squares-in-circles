module

public import SquaresInCircles.Eight.Owners.ChargedOrdinaryConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Balanced
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Split

/-!
# Eight squares: the high-total EH1/BT3 split and its actual endpoint functions

The negative H/G/B increment is fixed
while the original A/BT split varies. The moving D coefficient remains
inside its own circle norm. Its shifted concave part is composed with
the harmonic coefficient, and the existing strict rest-curvature bound
pays the shift. The A-support transition is inherited with matching
first derivatives from the already proved rest theorem.
-/

section
/-!
## Original four-block coefficients for the EH1/BT3 scalar reductions

The fourth block is ordinary and retains
both original arguments. The small-high coefficients are exactly the
already proved nonnegative-total family at e=0. Far-high coefficients
are the original far-EH family with the unrotated and tilted D weights
kept in their correct roles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Blocks
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev p (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  PositiveBT3.pWeights (Explicit.k f θ) (Explicit.l f θ) (Explicit.m f θ) (Explicit.c f θ z)
abbrev q (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  PositiveBT3.qWeights (Explicit.k f θ) (Explicit.l f θ) (Explicit.m f θ) (Explicit.c f θ z)
def positive (f : Family) (θ z P : ℝ) (i : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.positive R (epsilon f) (p f θ z) (q f θ z) i P
def negative (f : Family) (θ z N : ℝ) (i : Fin 4) : ℝ := V R (p f θ z i) (q f θ z i) N
def block (f : Family) (θ z P N : ℝ) (i : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.block R (epsilon f) (p f θ z) (q f θ z) i P N
def pure (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.pure R (epsilon f) (p f θ z) (q f θ z) i j s θ
def saturated (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedOrdinaryConcentration.saturated R (epsilon f) (p f θ z) (q f θ z) i j s θ

def ordinaryP (f : Family) (θ : ℝ) : Fin 3→ℝ :=
  ![Explicit.k f θ,Explicit.k f θ,min (Explicit.l f θ) (Explicit.m f θ)]
def ordinaryQ (f : Family) (θ : ℝ) : Fin 3→ℝ :=
  ![1,Explicit.l f θ,max (Explicit.l f θ) (Explicit.m f θ)]
def ordinaryV (f : Family) (θ : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  V R (ordinaryP f θ i) (ordinaryQ f θ i) t

@[simp] lemma negative_ordinary (f : Family) (θ z t : ℝ) (i : Fin 3) :
    negative f θ z t i.castSucc=ordinaryV f θ i t := by fin_cases i <;> rfl

lemma small_high_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    NonnegativeTotals.Explicit.Domain .triangle (θ-1/6) 0 := by
  dsimp [NonnegativeTotals.Explicit.Domain]
  exact ⟨by linarith [hθ.1],le_rfl,by linarith [hθ.2]⟩

lemma small_high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<p .smallHigh θ z i ∧ p .smallHigh θ z i≤q .smallHigh θ z i ∧
      (2/3)*q .smallHigh θ z i≤p .smallHigh θ z i := by
  have hh := PositiveBT3.Balanced.pair_domain .triangle (small_high_domain hθ)
    (show z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) by
      simpa [NonnegativeTotals.Explicit.theta] using hz) i
  have heP : PositiveBT3.pWeights (NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z) i=p .smallHigh θ z i := by
    simp [p,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
      NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
      NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted]
  have heQ : PositiveBT3.qWeights (NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0)
      (NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z) i=q .smallHigh θ z i := by
    simp [q,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
      NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
      NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted]
  rw [heP,heQ] at hh
  exact ⟨hh.1,hh.2.1,by linarith [hh.2.2]⟩

lemma small_high_scale {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    min 1 (Explicit.l .smallHigh θ)≤q .smallHigh θ z i ∧
      q .smallHigh θ z i≤(6/5)*min 1 (Explicit.l .smallHigh θ) := by
  have hh := PositiveBT3.Balanced.scale_bounds .triangle (small_high_domain hθ)
    (show z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) by
      simpa [NonnegativeTotals.Explicit.theta] using hz) i
  simpa [q,Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
    NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
    NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted] using hh

lemma far_high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤p .farHigh θ z i ∧ p .farHigh θ z i≤q .farHigh θ z i ∧
      q .farHigh θ z i≤(5/3)*p .farHigh θ z i ∧ q .farHigh θ z i≤1 := by
  have h0 : (0:ℝ)∈Icc 0 θ := ⟨le_rfl,by linarith [hθ.1]⟩
  have hp := NegativeEHPositiveTD.Explicit.far_pairs .high hθ h0
  have hq := NegativeEHPositiveTD.Explicit.far_high_q_le_one hθ h0
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted hθ hz
  have hck : Explicit.k .farHigh θ<Explicit.c .farHigh θ z := by
    simpa [Explicit.k,Explicit.c,Explicit.m,PositiveBT3.tilted,
      NegativeEHPositiveTD.Explicit.k,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c,NegativeEHPositiveTD.Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta] using (lt_min_iff.mp hc.2.2.1).2
  have hc1 : Explicit.c .farHigh θ z<1 := by
    simpa [Explicit.c,Explicit.m,PositiveBT3.tilted,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c,NegativeEHPositiveTD.Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta] using (max_lt_iff.mp hc.2.2.2.1).2
  have hkn : (121/200:ℝ)≤Explicit.k .farHigh θ := hr.1.1
  have ep : p .farHigh θ z 2=NegativeEHPositiveTD.Explicit.p .far .high θ 0 2 := by
    simp [p,PositiveBT3.pWeights,Explicit.l,Explicit.m,NegativeEHPositiveTD.Explicit.p,
      NegativeEHPositiveTD.Explicit.l,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c]
  have eq : q .farHigh θ z 2=NegativeEHPositiveTD.Explicit.q .far .high θ 0 2 := by
    simp [q,PositiveBT3.qWeights,Explicit.l,Explicit.m,NegativeEHPositiveTD.Explicit.q,
      NegativeEHPositiveTD.Explicit.l,NegativeEHPositiveTD.Explicit.m,
      NegativeEHPositiveTD.Explicit.c]
  have i2 : (3/5:ℝ)≤p .farHigh θ z 2 ∧ p .farHigh θ z 2≤q .farHigh θ z 2 ∧
      q .farHigh θ z 2≤(5/3)*p .farHigh θ z 2 ∧ q .farHigh θ z 2≤1 := by
    rw [ep,eq]
    exact ⟨(hp 2).1,(hp 2).2.1,(hp 2).2.2,hq 2⟩
  have e3 : p .farHigh θ z 3=Explicit.c .farHigh θ z ∧ q .farHigh θ z 3=1 :=
    ⟨min_eq_right hc1.le,max_eq_left hc1.le⟩
  have i3 : (3/5:ℝ)≤p .farHigh θ z 3 ∧ p .farHigh θ z 3≤q .farHigh θ z 3 ∧
      q .farHigh θ z 3≤(5/3)*p .farHigh θ z 3 ∧ q .farHigh θ z 3≤1 := by
    rw [e3.1,e3.2]
    exact ⟨by linarith,hc1.le,by linarith,le_rfl⟩
  fin_cases i
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2,hq 0⟩
  · exact ⟨(hp 1).1,(hp 1).2.1,(hp 1).2.2,hq 1⟩
  · exact i2
  · exact i3

lemma concentrate (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hpair : ∀i,0<p f θ z i ∧ p f θ z i≤q f θ z i ∧ q f θ z i≤2*p f θ z i)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure f θ z s i j) (saturated f θ z s i j)≤∑k,block f θ z (P k) (N k) k := by
  exact ChargedOrdinaryConcentration.concentrate R (epsilon f) (p f θ z) (q f θ z) P N
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (hpair i).1)
    (fun i => (hpair i).2.1) (fun i => (hpair i).2.2) hP hN hs hθ hPb hNb hbalance

/-- The negative-angle derivative in the smaller coefficient is nonnegative
for every ratio in `(0,1]` (the published bound covers `[1/2,1]`). -/
private theorem r75_smallerD_nonneg {R r t : ℝ} (hR : 0≤R) (hr : r∈Ioc (0:ℝ) 1)
    (ht : t∈Icc 0 frameCap) : 0≤OrdinaryNegativeEnvelope.smallerD R r t := by
  obtain ⟨u,hu_def⟩ : ∃ u,u=Real.sin t := ⟨_,rfl⟩
  have hu : u∈Icc 0 frameCap := by rw [hu_def]; exact VaryingBFunctions.sin_mem ht
  have huSmall : u<129/200 := by rw [hu_def]; linarith [(transport_trig ht).2.2.2.1]
  have hr0 : 0≤r := hr.1.le
  have hS := OrdinaryCurvatureBounds.shape_pos r
  have hN := VaryingBFunctions.root_pos r hu
  have hS2 := OrdinaryCurvatureBounds.shape_sq r
  have hN2 := VaryingBFunctions.root_sq r hu
  have hfrac : (r-u)/VaryingBFunctions.root r u≤r/OrdinaryCurvatureBounds.shape r := by
    apply (div_le_div_iff₀ hN hS).2
    by_cases hru : r-u≤0
    · exact (mul_nonpos_of_nonpos_of_nonneg hru hS.le).trans (mul_nonneg hr0 hN.le)
    · have hfactor : 0≤2*r-(1+r^2)*u := by
        have h1 : 0≤1-r*u := by nlinarith [hr.2,hu.1,huSmall]
        nlinarith [mul_nonneg hr0 h1]
      have hsquare : ((r-u)*OrdinaryCurvatureBounds.shape r)^2≤
          (r*VaryingBFunctions.root r u)^2 := by
        have he : (r*VaryingBFunctions.root r u)^2-((r-u)*OrdinaryCurvatureBounds.shape r)^2=
            u*(2*r-(1+r^2)*u) := by
          calc
            (r*VaryingBFunctions.root r u)^2-((r-u)*OrdinaryCurvatureBounds.shape r)^2=
                r^2*(VaryingBFunctions.root r u)^2-(r-u)^2*(OrdinaryCurvatureBounds.shape r)^2 := by
              ring
            _=u*(2*r-(1+r^2)*u) := by rw [hN2,hS2]; ring
        have h := mul_nonneg hu.1 hfactor
        rw [← he] at h
        linarith
      nlinarith [mul_nonneg hr0 hN.le,mul_nonneg (lt_of_not_ge hru).le hS.le]
  dsimp [OrdinaryNegativeEnvelope.smallerD]
  rw [← hu_def]
  exact mul_nonneg hR (sub_nonneg.mpr hfrac)

/-- The D-negative comparison only requires a positive k, not a high-family
lower cutoff. It therefore also applies to the actual far-EH coefficients. -/
lemma D_redundant {k c t : ℝ} (hk : k∈Ioc (0:ℝ) 1)
    (hkc : k≤c) (hc : c≤6/5) (ht : t∈Icc 0 frameCap) :
    V R k 1 t≤V R (min 1 c) (max 1 c) t := by
  have hmono : ∀ {a b : ℝ},0<a → a≤b → b≤1 → V R a 1 t≤V R b 1 t := by
    intro a b ha hab hb
    have hm : MonotoneOn (fun x => V R x 1 t) (Icc a b) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact (OrdinaryNegativeEnvelope.V_hasDerivAt_p (R:=R) (by linarith [hx.1]) one_pos
          ht).continuousAt.continuousWithinAt
      · intro x hx
        exact OrdinaryNegativeEnvelope.V_hasDerivAt_p (R:=R) (by linarith [hx.1]) one_pos ht
      · intro x hx
        rw [div_one]
        exact r75_smallerD_nonneg (Real.sqrt_nonneg qCap)
          ⟨by linarith [hx.1],by linarith [hx.2]⟩ ht
    exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  by_cases hc1 : c≤1
  · rw [min_eq_right hc1,max_eq_left hc1]
    exact hmono hk.1 hkc hc1
  · have hc1' : 1≤c := (lt_of_not_ge hc1).le
    rw [min_eq_left hc1',max_eq_right hc1']
    exact (hmono hk.1 hk.2 le_rfl).trans (PositiveATD0.balanced_second_coefficient
      (by norm_num) le_rfl hc1' (by linarith) ht)

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Blocks
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SplitConcavityTools

lemma full_baseline_concave {k l m θ low : ℝ}
    (hl : 0<l) (hmLow : (9/10)*l≤ m) (hmHigh : m≤(11/10)*l)
    (ht : θ∈Icc 0 frameCap) (hlow : 0<low)
    (hc : ∀a∈Icc 0 θ,PositiveTD.tilted m (θ-a)∈Icc low (6/5:ℝ))
    (hrot : ∀a∈Icc 0 θ,PositiveTD.tilted m (θ-a)≤(23/20)*l) :
    ConcaveOn ℝ (Icc 0 θ)
      (fun a => PositiveBT3.Analytic.fullBaseline k l m (θ-a)+l*TwoPositive.ASupport.charge a) := by
  have hm : 0< m := by linarith
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
  have ek : Explicit.k .smallHigh θ=NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0 := by
    simp only [Explicit.k,NonnegativeTotals.Explicit.k,L]; ring
  have el : Explicit.l .smallHigh θ=NonnegativeTotals.Explicit.l .triangle (θ-1/6) 0 := by
    simp only [Explicit.l,NonnegativeTotals.Explicit.l,L]; ring
  have em : Explicit.m .smallHigh θ=NonnegativeTotals.Explicit.c .triangle (θ-1/6) 0 := by
    simp only [Explicit.m,NonnegativeTotals.Explicit.c,L]; ring
  have etil (z : ℝ) : PositiveTD.tilted (Explicit.m .smallHigh θ) z=
      NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z := by
    simp only [PositiveTD.tilted,NonnegativeTotals.Explicit.tilted,
      NonnegativeTotals.Explicit.tilt,em,PositiveTD.eta]
  have hz (a : ℝ) (ha : a∈Icc 0 θ) :
      θ-a∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) := by
    simp only [NonnegativeTotals.Explicit.theta]
    constructor <;> linarith [ha.1,ha.2]
  have hc (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .smallHigh θ) (θ-a)∈
        Icc (Explicit.k .smallHigh θ) (6/5:ℝ) := by
    rw [etil,ek]
    exact ⟨(NonnegativeTotals.Explicit.tilted_lower .triangle hd (hz a ha)).le,
      (NonnegativeTotals.Explicit.tilted_upper .triangle hd (hz a ha)).le⟩
  have hrot (a : ℝ) (ha : a∈Icc 0 θ) :
      PositiveTD.tilted (Explicit.m .smallHigh θ) (θ-a)≤(23/20)*Explicit.l .smallHigh θ := by
    rw [etil,el]
    exact (NonnegativeTotals.Explicit.tilted_ratio .triangle hd (hz a ha)).2.le
  have hk : 0<Explicit.k .smallHigh θ := by rw [ek]; linarith [hb.k_lower]
  have hl : 0<Explicit.l .smallHigh θ := by rw [el]; exact hb.l_positive
  have hmL : (9/10)*Explicit.l .smallHigh θ≤Explicit.m .smallHigh θ := by
    rw [el,em]; exact hb.c_lower_ratio
  have hmU : Explicit.m .smallHigh θ≤(11/10)*Explicit.l .smallHigh θ := by
    rw [el,em]; exact hb.c_upper_ratio
  simpa only [baseline,reduceCtorEq,↓reduceIte] using
    full_baseline_concave (k:=Explicit.k .smallHigh θ) hl hmL hmU ht hk hc hrot

lemma far_high_base_concave {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => baseline .farHigh θ a (θ-a)) := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have hl : 0<Explicit.l .farHigh θ := by
    change 0<NegativeEHPositiveTD.Explicit.l .far .high θ
    linarith [hr.2.1.1]
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
  simpa only [baseline,reduceCtorEq,↓reduceIte] using full_baseline_concave
    (k:=Explicit.k .farHigh θ) hl hmL hmU ht (by norm_num : (0:ℝ)<3/5) hc hrot

lemma small_high_endpoint (ep : Certificate.Split) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    0<baseline .smallHigh θ (EndpointInputs.aAt ep θ) (EndpointInputs.zAt ep θ)+
      charge .smallHigh (1/10)+Blocks.ordinaryV .smallHigh θ i (θ-1/10) := by
  have hθ' : θ∈Icc ((Certificate.left (.smallHigh i):ℚ):ℝ) (Certificate.right (.smallHigh i)) := by
    norm_num [Certificate.left,Certificate.right]; exact hθ
  have hx := Endpoints.native_coordinate (.smallHigh i) hθ'
  have hc := EndpointInputs.coefficient_bounds (.smallHigh i) hx
  have hk1 : Explicit.k .smallHigh θ≤1 := by
    simpa [EndpointInputs.Kactual,EndpointInputs.thetaAt,Certificate.family] using hc.2.2.2.1
  have hkl : Explicit.k .smallHigh θ≤Explicit.l .smallHigh θ := by
    simpa [EndpointInputs.Kactual,EndpointInputs.Lactual,EndpointInputs.thetaAt,
      Certificate.family] using hc.2.2.2.2
  have hh := Endpoints.original_endpoint_positive (.smallHigh i) ep hθ'
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
  have hθ' : θ∈Icc ((Certificate.left (.farHigh i upper):ℚ):ℝ)
      (Certificate.right (.farHigh i upper)) := by
    norm_num [Certificate.left,Certificate.right]; exact hθ
  have hx := Endpoints.native_coordinate (.farHigh i upper) hθ'
  have hc := EndpointInputs.coefficient_bounds (.farHigh i upper) hx
  have hk1 : Explicit.k .farHigh θ≤1 := by
    simpa [EndpointInputs.Kactual,EndpointInputs.thetaAt,Certificate.family] using hc.2.2.2.1
  have hkl : Explicit.k .farHigh θ≤Explicit.l .farHigh θ := by
    simpa [EndpointInputs.Kactual,EndpointInputs.Lactual,EndpointInputs.thetaAt,
      Certificate.family] using hc.2.2.2.2
  have hh := Endpoints.original_endpoint_positive (.farHigh i upper) ep hθ'
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
  fin_cases i <;> simpa [PositiveBT3.Analytic.largeScalar,baseline,Blocks.ordinaryV,
    Blocks.ordinaryP,Blocks.ordinaryQ,PositiveBT3.Analytic.negative,
    NonnegativeTotals.Analytic.negative,NonnegativeTotals.Explicit.k,
    NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,NonnegativeTotals.Explicit.theta,
    NonnegativeTotals.Explicit.e,Explicit.k,Explicit.l,Explicit.m,L,
    TwoPositive.ASupport.charge_zero,show a+z-a=z by ring] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighSplit
end
end
end
