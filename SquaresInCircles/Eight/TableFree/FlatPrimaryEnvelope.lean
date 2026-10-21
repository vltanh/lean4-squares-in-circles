module

public import SquaresInCircles.Eight.TableFree.FlatPrimaryConcentration

/-!
# Angular envelope with all flat negative E primaries removed

Uncompiled source. Ordinary and modified one-angle blocks share the
same full-range secant coefficient. The remaining positive and negative
masses are concentrated analytically, with their original imbalance.
The coefficient hypotheses below are numerical domains, to be supplied
by the actual positive-T and negative-T stress families.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FlatPrimaryEnvelope
open PositiveAngularEnvelope PositiveStressCoefficients PositivePrimaryBaselines
open OrdinaryAngleConcavity OrdinaryAngleConcentration OrdinaryPositiveEnvelope
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope PositiveOrdinaryEnvelope
open NegativeEOneAngle FlatPrimaryConcentration VaryingBComparison

structure Domain {ι : Type*} (d s l : ℝ) (p q : ι → ℝ) : Prop where
  angle : d∈Icc 0 frameCap
  removed : s∈Icc 0 frameCap
  ell_lower : 1/2<l
  ell_upper : l≤k
  positive : ∀ i,0<p i
  ordered : ∀ i,p i≤q i
  ratio_two : ∀ i,q i≤2*p i
  large_lower : ∀ i,k≤q i
  secant_upper : ∀ i,q i≤(2069/2000)/Real.cos s
  relaxed : ∀ i,(ratio d-31/10000)*q i≤p i
  shape : ∀ i,p i=l ∨ (k≤p i ∧ q i≤109/100)
  pure_ratio : ∀ i,p i=l → s≤d → ratio (d-s)*q i≤l
  high : 3/10≤d → ∀ i,(2/3)*q i≤p i
  low : d≤3/10 → ∀ i,lP d≤p i ∧ (p i=l → q i≤1)
  low_ell : d≤3/10 → l≤1631/2500

theorem U'_lower {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (m : Bool) (i : ι) {P : ℝ}
    (hP : P∈Icc 0 frameCap) :
    -gamma s*P≤U' m (p i) (q i) s P := by
  cases m
  · have hU := U_lower (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
      (h.positive i) (h.ordered i) (h.ratio_two i) hP
    have hc := mul_le_mul_of_nonneg_left (h.secant_upper i)
      (by norm_num : (0:ℝ)≤109/200)
    have hm := mul_le_mul_of_nonneg_right hc hP.1
    dsimp [U',gamma]
    nlinarith
  · simp [U']

theorem target_to_large {l p q t : ℝ}
    (hl : 1/2<l) (hlk : l≤k) (hp : k≤p) (hpq : p≤q)
    (hq : q≤109/100) (ht : t∈Icc 0 frameCap) :
    V (Real.sqrt qCap) l k t≤V (Real.sqrt qCap) p q t := by
  have hk : 0<k := by norm_num [k]
  have hqk : k≤q := hp.trans hpq
  have hq0 : 0<q := hk.trans_le hqk
  have hfirst := V_monotone_smaller (Real.sqrt_nonneg qCap) hk ht
    (show l∈Icc (k/2) k by constructor; norm_num [k]; linarith; exact hlk)
    (show k∈Icc (k/2) k by norm_num [k]) hlk
  have hsecond := V_larger_coefficient hk le_rfl hqk
    (show ratio frameCap*q≤k by norm_num [ratio,frameCap,k] at *; linarith)
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  have hthird := V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 ht
    (show k∈Icc (q/2) q by constructor; norm_num [k] at *; linarith; exact hqk)
    (show p∈Icc (q/2) q by constructor; norm_num [k] at hp; linarith; exact hpq) hp
  exact hfirst.trans (hsecond.trans hthird)

theorem canonical_to_large {p q t : ℝ}
    (hp : k≤p) (hpq : p≤q) (hq : q∈Icc 1 (109/100))
    (ht : t∈Icc 0 frameCap) :
    V (Real.sqrt qCap) k 1 t≤V (Real.sqrt qCap) p q t := by
  have hk : 0<k := by norm_num [k]
  have hq0 : 0<q := by linarith [hq.1]
  have hfirst := V_larger_coefficient hk (by norm_num [k] : k≤1) hq.1
    (show ratio frameCap*q≤k by norm_num [ratio,frameCap,k]; linarith [hq.2])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  have hsecond := V_monotone_smaller (Real.sqrt_nonneg qCap) hq0 ht
    (show k∈Icc (q/2) q by norm_num [k]; constructor <;> linarith [hq.1,hq.2])
    (show p∈Icc (q/2) q by constructor; norm_num [k] at hp; linarith [hq.2]; exact hpq) hp
  exact hfirst.trans hsecond

theorem pure_lower {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (m : Bool) (i : ι) (hsd : s≤d)
    {u : ℝ} (hu : u∈Icc 0 (d-s)) :
    V (Real.sqrt qCap) l k u≤V' m (p i) (q i) u := by
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,h.angle.2,h.removed.1]⟩
  cases m
  · rcases h.shape i with he | he
    · change _≤V (Real.sqrt qCap) (p i) (q i) u
      rw [he]
      exact V_larger_coefficient (by linarith [h.ell_lower]) h.ell_upper
        (h.large_lower i) (h.pure_ratio i he hsd)
        ⟨by linarith,by linarith [h.angle.2,h.removed.1]⟩ hu
    · exact target_to_large h.ell_lower h.ell_upper he.1 (h.ordered i) he.2 hu'
  · exact target_to_large h.ell_lower h.ell_upper le_rfl
      (by norm_num [k]) (by norm_num) hu'

theorem high_growth {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (hd : 3/10≤d) (m : Bool) (i : ι)
    {u v : ℝ} (hu : u∈Icc 0 (frameCap-s))
    (hv : v∈Icc 0 (frameCap-s)) (huv : u≤v) :
    gamma s*(v-u)≤V' m (p i) (q i) v-V' m (p i) (q i) u := by
  cases m
  · exact OrdinaryLongSecantGrowth.growth (h.positive i) (h.ordered i)
      (h.high hd i) (h.large_lower i) h.removed hu hv huv
  · exact OrdinaryLongSecantGrowth.growth (by norm_num [k]) (by norm_num [k])
      (by norm_num [k]) (by norm_num [k]) h.removed hu hv huv

theorem low_base {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    (1263/2500 : ℝ)≤lP d := by
  have hd2 : d^2≤(3/10)*d := by nlinarith [hd.1,hd.2]
  dsimp [lP]
  nlinarith

theorem low_gamma {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (hd : d≤3/10) (m : Bool) (i : ι)
    {u : ℝ} (hu : u∈Icc 0 (frameCap-s)) :
    gamma s*u≤V' m (p i) (q i) u := by
  cases m
  · have hlow := h.low hd i
    have hp0 := (low_base ⟨h.angle.1,hd⟩).trans hlow.1
    by_cases hq : q i≤1
    · exact LowSecantTransfer.coefficient_interval hp0 ⟨h.large_lower i,hq⟩
        (h.ordered i) h.removed hu
    · rcases h.shape i with he | he
      · exact False.elim (hq (hlow.2 he))
      · have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,h.removed.1]⟩
        exact (LowSecantTransfer.canonical h.removed hu).trans
          (canonical_to_large he.1 (h.ordered i) ⟨(lt_of_not_ge hq).le,he.2⟩ hu')
  · exact LowSecantTransfer.canonical h.removed hu

theorem pure_gamma {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (m : Bool) (i : ι)
    {u : ℝ} (hu : u∈Icc 0 (frameCap-s)) :
    gamma s*u≤V' m (p i) (q i) u := by
  by_cases hd : d≤3/10
  · exact low_gamma h hd m i hu
  · have hz : (0:ℝ)∈Icc 0 (frameCap-s) := ⟨le_rfl,by linarith [h.removed.2]⟩
    simpa only [sub_zero,V'_zero] using high_growth h (lt_of_not_ge hd).le m i hz hu hu.1

theorem low_chord {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (hd : d≤3/10) (m : Bool) (i : ι)
    {u : ℝ} (hu : u∈Icc 0 frameCap) :
    (87/70)*lP d*u≤V' m (p i) (q i) u := by
  cases m
  · have hb := V_chord_lower (h.positive i) (h.ordered i) (h.ratio_two i) hu
    have hm := mul_le_mul_of_nonneg_right (h.low hd i).1 hu.1
    dsimp [V']
    nlinarith
  · have hb := V_chord_lower (by norm_num [k] : 0<k)
      (by norm_num [k] : k≤1) (by norm_num [k] : 1≤2*k) hu
    have hk : lP d≤k := by
      have hh := PositiveOrdinaryParameters.low_P h.angle hd
      norm_num [k]
      linarith
    have hm := mul_le_mul_of_nonneg_right hk hu.1
    dsimp [V']
    nlinarith

theorem gamma_small {s : ℝ} (hs : s∈Icc 0 (3/10)) : gamma s≤591/1000 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hcos : (191/200 : ℝ)≤Real.cos s := by nlinarith
  dsimp [gamma]
  apply (div_le_iff₀ (by linarith : 0<Real.cos s)).2
  nlinarith

theorem low_reserve {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    (87/70)*lP d≤26/25 ∧
      0<(87/100)*lP d-(26/25)*d-(591/1000)*(frameCap-d) := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hlo := PositiveOrdinaryParameters.low_P
    (show d∈Icc 0 frameCap from ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩) hd.2
  constructor
  · linarith
  · dsimp [lP,frameCap]
    nlinarith

theorem separated_negative {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (m : ι → Bool) (i j : ι) (hsd : s≤d) :
    V (Real.sqrt qCap) l k (d-s)≤
      U' (m i) (p i) (q i) s (frameCap-d)+V' (m j) (p j) (q j) (frameCap-s) := by
  have hP : frameCap-d∈Icc 0 frameCap :=
    ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by linarith [h.removed.2],by linarith [h.removed.1]⟩
  have hw : d-s∈Icc 0 frameCap := ⟨by linarith,by linarith [h.angle.2,h.removed.1]⟩
  have hU := U'_lower h (m i) i hP
  by_cases hd : d≤3/10
  · have hgamma := gamma_small (show s∈Icc 0 (3/10) from ⟨h.removed.1,hsd.trans hd⟩)
    have hmul := mul_le_mul_of_nonneg_right hgamma hP.1
    have hV := low_chord h hd (m j) j hN
    have ht := V_tangent_zero (by linarith [h.ell_lower] : 0<l) h.ell_upper
      (by norm_num [k]; linarith [h.ell_lower] : k≤2*l) hw
    have ht' := mul_le_mul_of_nonneg_right
      (target_zero_slope h.ell_lower (h.low_ell hd)).le hw.1
    have hr := low_reserve ⟨h.angle.1,hd⟩
    have hreserve := mul_nonneg (sub_nonneg.mpr hr.1) h.removed.1
    dsimp [frameCap] at *
    nlinarith
  · have hg := high_growth h (lt_of_not_ge hd).le (m j) j
      (show d-s∈Icc 0 (frameCap-s) from ⟨by linarith,by linarith [h.angle.2]⟩)
      (show frameCap-s∈Icc 0 (frameCap-s) from ⟨hN.1,le_rfl⟩)
      (by linarith [h.angle.2])
    have hv := pure_lower h (m j) j hsd ⟨by linarith,le_rfl⟩
    nlinarith

theorem same_negative {ι : Type*} {d s l : ℝ} {p q : ι → ℝ}
    (h : Domain d s l p q) (m : ι → Bool) (i : ι) (hsd : s≤d) :
    V (Real.sqrt qCap) l k (d-s)≤
      F (m i) (p i) (q i) s (frameCap-d) (frameCap-s) := by
  cases he : m i
  · have hh := RelaxedSameBlock.negative_surplus (R := Real.sqrt qCap)
      ((h.positive i).trans_le (h.ordered i)).le (h.relaxed i) h.angle ⟨h.removed.1,hsd⟩
    have hv := pure_lower h false i hsd ⟨by linarith,le_rfl⟩
    simpa [he,F,V'] using hv.trans hh
  · have hh := separated_negative h m i i hsd
    simpa [he,F,U',V'] using hh

theorem negative_sum {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {d s l : ℝ} {p q : ι → ℝ} (h : Domain d s l p q)
    (m : ι → Bool) (P N : ι → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) (hsd : s≤d) :
    V (Real.sqrt qCap) l k (d-s)≤∑ i,F (m i) (p i) (q i) s (P i) (N i) := by
  obtain ⟨i,j,hc⟩ := negative_endpoints m p q P N h.positive h.ordered h.ratio_two
    hP hN h.angle ⟨h.removed.1,hsd⟩ hbudget hbalance
  refine (le_min (pure_lower h (m j) j hsd ⟨by linarith,le_rfl⟩) ?_).trans hc
  by_cases hij : i=j
  · rw [if_pos hij]
    exact same_negative h m i hsd
  · rw [if_neg hij]
    exact separated_negative h m i j hsd

theorem positive_sum {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {d s l : ℝ} {p q : ι → ℝ} (h : Domain d s l p q)
    (m : ι → Bool) (P N : ι → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) (hds : d≤s) :
    -gamma s*(s-d)≤∑ i,F (m i) (p i) (q i) s (P i) (N i) := by
  have hP0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hN i)
  have hPt : (∑ i,P i)≤frameCap := by linarith [h.angle.1]
  have hNt : (∑ i,N i)≤frameCap-s := by rw [hbalance]; linarith
  obtain ⟨i,j,hc⟩ := both_signs m p q P N s h.positive h.ordered h.ratio_two hP hN
    hPt (by linarith [h.removed.1])
  have hseparated (a b : ι) : -gamma s*(s-d)≤
      U' (m a) (p a) (q a) s (∑ i,P i)+V' (m b) (p b) (q b) (∑ i,N i) := by
    have hu := U'_lower h (m a) a ⟨hP0,hPt⟩
    have hv := pure_gamma h (m b) b ⟨hN0,hNt⟩
    nlinarith
  apply le_trans ?_ hc
  by_cases hij : i=j
  · rw [if_pos hij]
    cases hm : m i
    · have hratio : (29/50)*q i≤p i := by
        have hnon : 0≤q i := ((h.positive i).trans_le (h.ordered i)).le
        have hh : 29/50≤ratio d-31/10000 := by dsimp [ratio]; linarith [h.angle.1]
        exact (mul_le_mul_of_nonneg_right hh hnon).trans (h.relaxed i)
      have hs := RelaxedSameBlock.positive_surplus (R := Real.sqrt qCap)
        ((h.positive i).trans_le (h.ordered i)).le hratio ⟨hP0,hPt⟩
        (show (∑ i,N i)∈Icc 0 (∑ i,P i) from ⟨hN0,by linarith⟩)
      have he : (∑ i,P i)-(∑ i,N i)=s-d := by linarith
      rw [he] at hs
      have hu := U'_lower h false i
        (show s-d∈Icc 0 frameCap from ⟨by linarith,by linarith [h.removed.2,h.angle.1]⟩)
      simpa [hm,F,U'] using hu.trans hs
    · simpa [hm,F,U',V'] using hseparated i i
  · rw [if_neg hij]
    exact hseparated i j

theorem gain_junction {d s l λ : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 d) (hl : 1/2<l) (hlk : l≤k) :
    min (V (Real.sqrt qCap) l k d) (λ*d)≤λ*s+V (Real.sqrt qCap) l k (d-s) := by
  have hv := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by linarith : 0<l) hlk (by norm_num [k]; linarith : k≤2*l)
  have ha := concave_affine_argument hv (a := -1) (b := d) (l := 0) (u := d)
    (fun x hx => ⟨by linarith [hx.2],by linarith [hd.2,hx.1]⟩)
  have hc : ConcaveOn ℝ (Icc 0 d)
      (fun x => λ*x+V (Real.sqrt qCap) l k (d-x)) := by
    convert (NegativeOrdinaryEnvelope.affine_concave λ 0 0 d).add ha using 1
    funext x
    congr 1 <;> ring
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ hs
  simpa only [mul_zero,sub_zero,zero_add,sub_self,V_zero,add_zero] using hh

theorem mixed_sum_lower {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {d s l λ : ℝ} {p q : ι → ℝ} (h : Domain d s l p q)
    (hλ : 369/500≤λ) (m : ι → Bool) (P N : ι → ℝ)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    min (V (Real.sqrt qCap) l k d) (λ*d)≤
      λ*s+∑ i,F (m i) (p i) (q i) s (P i) (N i) := by
  by_cases hsd : s≤d
  · have hj := gain_junction h.angle ⟨h.removed.1,hsd⟩ h.ell_lower h.ell_upper (λ := λ)
    have hs := negative_sum h m P N hP hN hbudget hbalance hsd
    linarith
  · have hds := (lt_of_not_ge hsd).le
    have hs := positive_sum h m P N hP hN hbudget hbalance hds
    have hgamma := (gamma_bound h.removed).2.le.trans hλ
    have hm := mul_le_mul_of_nonneg_right hgamma (show 0≤s-d by linarith)
    have hh := min_le_right (V (Real.sqrt qCap) l k d) (λ*d)
    nlinarith

end SquaresInCircles.Eight.TableFree.FlatPrimaryEnvelope
