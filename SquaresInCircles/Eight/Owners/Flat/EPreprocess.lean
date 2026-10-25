module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Boundary.ActualSortedSupport
public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.LowSecantTransfer
public import SquaresInCircles.Eight.Owners.Negative.TerminalSharp
public import SquaresInCircles.Eight.Owners.Negative.SecondaryEExclusion
public import SquaresInCircles.Eight.Owners.Positive.SecondaryEExclusion
public import SquaresInCircles.Eight.Words.Core.ENegativeExclusion
public import SquaresInCircles.Eight.Words.Core.EOrdinaryEnvelope

/-!
# Eight squares: the T entry when E is on the flat core

When E is on the flat side of the core with nonpositive DE and EH primaries, every preprocessed
row of T is impossible (`preprocessed_flat_E_false`): a secondary owner of T is selected again
from a weak projection of the cycle, and a negative primary gives its flat T and short angle
(`negative_TD_false`, `negative_BT_aligned_false`). The witnesses and coordinates of E stay fixed.
-/

section
/-!
## Joint concentration of ordinary and modified one-angle blocks

The modified one-angle lower bound is linear in
positive mass and concave in negative mass. It therefore joins the
ordinary blocks in the same exact finite-simplex argument. The resulting
concentrations are analytic lower bounds on the original signed angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatPrimaryConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveStressCoefficients NegativeEOneAngle

def F (modified : Bool) (p q s P N : ℝ) : ℝ :=
  if modified then -gamma s*P+V (Real.sqrt qCap) k 1 N
  else mixedBlock (Real.sqrt qCap) p q P N

def U' (modified : Bool) (p q s P : ℝ) : ℝ :=
  if modified then -gamma s*P else U (Real.sqrt qCap) p q P

def V' (modified : Bool) (p q N : ℝ) : ℝ :=
  if modified then V (Real.sqrt qCap) k 1 N else V (Real.sqrt qCap) p q N

@[simp] theorem F_zero (m : Bool) (p q s : ℝ) : F m p q s 0 0=0 := by cases m <;> simp [F]
@[simp] theorem F_zero_right (m : Bool) (p q s P : ℝ) : F m p q s P 0=U' m p q s P := by
  cases m <;> simp [F,U']
@[simp] theorem F_zero_left (m : Bool) (p q s N : ℝ) : F m p q s 0 N=V' m p q N := by
  cases m <;> simp [F,V']
@[simp] theorem U'_zero (m : Bool) (p q s : ℝ) : U' m p q s 0=0 := by cases m <;> simp [U']
@[simp] theorem V'_zero (m : Bool) (p q : ℝ) : V' m p q 0=0 := by cases m <;> simp [V']

theorem canonical_concave : ConcaveOn ℝ (Icc 0 frameCap) (V (Real.sqrt qCap) k 1) :=
  V_concave (Real.sqrt_nonneg _) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by norm_num [k]) (by norm_num [k]) (by norm_num [k])

theorem F_concave_P {m : Bool} {p q s N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F m p q s P N) := by
  cases m
  · exact mixedBlock_concave_positive (Real.sqrt_nonneg _)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp hN
  · exact NegativeOrdinaryEnvelope.affine_concave (-gamma s) (V (Real.sqrt qCap) k 1 N) 0 frameCap

theorem F_concave_N {m : Bool} {p q s P : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun N => F m p q s P N) := by
  cases m
  · exact mixedBlock_concave_negative (Real.sqrt_nonneg _)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp hP
  · convert (concaveOn_const (-gamma s*P) (convex_Icc (0:ℝ) frameCap)).add canonical_concave
      using 1
    funext N
    simp [F]

theorem U'_concave {m : Bool} {p q s : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (U' m p q s) := by
  simpa only [F_zero_right] using F_concave_P (m := m) (s := s) hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem V'_concave {m : Bool} {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    ConcaveOn ℝ (Icc 0 frameCap) (V' m p q) := by
  simpa only [F_zero_left] using F_concave_N (m := m) (s := 0) hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])

theorem negative_line_concave {m : Bool} {p q s z : ℝ}
    (hp : 0<p) (hpq : p≤q) (_hqp : q≤2*p) (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z)) (fun P => F m p q s P (z+P)) := by
  cases m
  · exact sameBlockLine_concave hp.le (hp.trans_le hpq).le hz
  · have hv := concave_affine_argument canonical_concave
      (a := 1) (b := z) (l := 0) (u := frameCap-z)
      (fun x hx => ⟨by linarith [hz.1,hx.1],by linarith [hx.2]⟩)
    have hl := NegativeOrdinaryEnvelope.affine_concave (-gamma s) 0 0 (frameCap-z)
    convert hl.add hv using 1
    funext P
    simp [F,add_comm]

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (p q : ι → ℝ) (s : ℝ) (i j : ι) (P N : ℝ) :
    (∑ a,F (m a) (p a) (q a) s (massAt i P a) (massAt j N a))=
      if i=j then F (m i) (p i) (q i) s P N
      else U' (m i) (p i) (q i) s P+V' (m j) (p j) (q j) N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : F (m a) (p a) (q a) s (massAt i P a) (massAt i N a)=
        if a=i then F (m i) (p i) (q i) s P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : F (m a) (p a) (q a) s (massAt i P a) (massAt j N a)=
        (if a=i then U' (m i) (p i) (q i) s P else 0)+
        (if a=j then V' (m j) (p j) (q j) N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

theorem both_signs {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (p q P N : ι → ℝ) (s : ℝ)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap) :
    ∃ i j, (if i=j then F (m i) (p i) (q i) s (∑ a,P a) (∑ a,N a)
      else U' (m i) (p i) (q i) s (∑ a,P a)+V' (m j) (p j) (q j) (∑ a,N a))≤
        ∑ a,F (m a) (p a) (q a) s (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hj⟩ := concave_sum_concentrates
    (fun i n => F (m i) (p i) (q i) s (P i) n) N hN rfl hNt
    (fun i => F_concave_N (hp i) (hpq i) (hqp i) (hPi i))
  have hNT : (∑ a,N a)∈Icc 0 frameCap := ⟨Finset.sum_nonneg (fun a _ => hN a),hNt⟩
  obtain ⟨i,hi⟩ := concave_sum_concentrates
    (fun a p' => F (m a) (p a) (q a) s p' (massAt j (∑ b,N b) a)) P hP rfl hPt
    (fun a => F_concave_P (hp a) (hpq a) (hqp a) (massAt_mem hNT))
  refine ⟨i,j,?_⟩
  rw [concentrated_sum] at hi
  exact hi.trans hj

theorem negative_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (p q P N : ι → ℝ) {d s : ℝ}
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    ∃ i j, min (V' (m j) (p j) (q j) (d-s))
      (if i=j then F (m i) (p i) (q i) s (frameCap-d) (frameCap-s)
       else U' (m i) (p i) (q i) s (frameCap-d)+V' (m j) (p j) (q j) (frameCap-s))≤
        ∑ a,F (m a) (p a) (q a) s (P a) (N a) := by
  have hz : d-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hd.2,hs.1]⟩
  obtain ⟨i,j,hij⟩ := both_signs m p q P N s hp hpq hqp hP hN
    (by linarith [hd.1]) (by rw [hbalance]; linarith [hs.1])
  have htotal : (∑ a,P a)∈Icc 0 (frameCap-d) :=
    ⟨Finset.sum_nonneg (fun a _ => hP a),hbudget⟩
  have hspan : 0≤frameCap-d := by linarith [hd.2]
  have hsub : Icc (0:ℝ) (frameCap-d)⊆Icc 0 (frameCap-(d-s)) :=
    Icc_subset_Icc le_rfl (by linarith [hs.1])
  refine ⟨i,j,?_⟩
  by_cases he : i=j
  · subst j
    simp only [↓reduceIte] at hij ⊢
    rw [hbalance] at hij
    have hc := (negative_line_concave (m := m i) (s := s)
      (hp i) (hpq i) (hqp i) hz).subset hsub (convex_Icc 0 (frameCap-d))
    have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    rw [add_zero,F_zero_left,show d-s+(frameCap-d)=frameCap-s by ring] at hh
    exact hh.trans hij
  · simp only [he,↓reduceIte] at hij ⊢
    rw [hbalance] at hij
    have hU := (U'_concave (m := m i) (s := s) (hp i) (hpq i) (hqp i)).subset
      (Icc_subset_Icc le_rfl (by linarith [hd.1])) (convex_Icc 0 (frameCap-d))
    have hV := concave_affine_argument
      (V'_concave (m := m j) (hp j) (hpq j) (hqp j))
      (a := 1) (b := d-s) (l := 0) (u := frameCap-d)
      (fun x hx => ⟨by linarith [hz.1,hx.1],by linarith [hs.1,hx.2]⟩)
    have hh := (hU.add hV).min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    simp only [Pi.add_apply,one_mul,U'_zero,zero_add] at hh
    rw [show frameCap-d+(d-s)=frameCap-s by ring,
      show (∑ a,P a)+(d-s)=d-s+∑ a,P a by ring] at hh
    exact hh.trans hij

end SquaresInCircles.Eight.FlatPrimaryConcentration
end
end
end

section
/-!
## Angular envelope with all flat negative E primaries removed

Ordinary and modified one-angle blocks share the
same full-range secant coefficient. The remaining positive and negative
masses are concentrated analytically, with their original imbalance.
The coefficient hypotheses below are numerical domains, to be supplied
by the actual positive-T and negative-T stress families.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatPrimaryEnvelope
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
    have hg : gamma s*P=109/200*(2069/2000/Real.cos s)*P := by dsimp only [gamma]; ring
    simp only [U',Bool.false_eq_true,↓reduceIte]
    linarith
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
  · rw [ite_eq_left hij]
    exact same_negative h m i hsd
  · rw [ite_eq_right hij]
    exact separated_negative h m i j hsd

theorem positive_sum {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {d s l : ℝ} {p q : ι → ℝ} (h : Domain d s l p q)
    (m : ι → Bool) (P N : ι → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) (hds : d≤ s) :
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
    have hb : gamma s*(∑ i,N i)=gamma s*(d-s)+gamma s*(∑ i,P i) := by rw [hbalance]; ring
    linarith
  apply le_trans ?_ hc
  by_cases hij : i=j
  · rw [ite_eq_left hij]
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
  · rw [ite_eq_right hij]
    exact hseparated i j

theorem gain_junction {d s l lam : ℝ} (hd : d∈Icc 0 frameCap)
    (hs : s∈Icc 0 d) (hl : 1/2<l) (hlk : l≤k) :
    min (V (Real.sqrt qCap) l k d) (lam*d)≤lam*s+V (Real.sqrt qCap) l k (d-s) := by
  have hv := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by linarith : 0<l) hlk (by norm_num [k]; linarith : k≤2*l)
  have ha := concave_affine_argument hv (a := -1) (b := d) (l := 0) (u := d)
    (fun x hx => ⟨by linarith [hx.2],by linarith [hd.2,hx.1]⟩)
  have hc : ConcaveOn ℝ (Icc 0 d)
      (fun x => lam*x+V (Real.sqrt qCap) l k (d-x)) := by
    convert (NegativeOrdinaryEnvelope.affine_concave lam 0 0 d).add ha using 1
    funext x
    congr 1 <;> ring
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ hs
  simpa only [mul_zero,sub_zero,zero_add,sub_self,V_zero,add_zero] using hh

theorem mixed_sum_lower {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {d s l lam : ℝ} {p q : ι → ℝ} (h : Domain d s l p q)
    (hlam : 369/500≤lam) (m : ι → Bool) (P N : ι → ℝ)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    min (V (Real.sqrt qCap) l k d) (lam*d)≤
      lam*s+∑ i,F (m i) (p i) (q i) s (P i) (N i) := by
  by_cases hsd : s≤d
  · have hj := gain_junction h.angle ⟨h.removed.1,hsd⟩ h.ell_lower h.ell_upper (lam := lam)
    have hs := negative_sum h m P N hP hN hbudget hbalance hsd
    linarith
  · have hds := (lt_of_not_ge hsd).le
    have hs := positive_sum h m P N hP hN hbudget hbalance hds
    have hgamma := (gamma_bound h.removed).2.le.trans hlam
    have hm := mul_le_mul_of_nonneg_right hgamma (show 0≤ s-d by linarith)
    have hh := min_le_right (V (Real.sqrt qCap) l k d) (lam*d)
    nlinarith

end SquaresInCircles.Eight.FlatPrimaryEnvelope
end
end
end

section
/-!
## The original four anchor blocks with negative E secants

Only the two E stress multipliers change. Every
signed angle, owner, and source point remains the original one. The
positive and negative budgets below are exact sums of those angles.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatEBlocks
open Candidate PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open ActualOrdinaryBlocks ActualCoreEBlocks OrdinaryAngleConcavity
open FlatPrimaryConcentration FlatPrimaryEnvelope NegativeEOneAngle

def deAngle (C : SignedCycle) (de : Fin 4) : ℝ := -primaryDE C de
def ehAngle (C : SignedCycle) (eh : Fin 4) : ℝ := -primaryEH C eh
def deWeight (C : SignedCycle) (de : Fin 4) : ℝ := 1/Real.cos (deAngle C de)
def ehWeight (C : SignedCycle) (eh : Fin 4) : ℝ := 1/Real.cos (ehAngle C eh)

def blocks (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : Fin 4 → Block :=
  ![⟨n,ehWeight C eh,delta C.theta H,ordinaryEH C eh⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨deWeight C de,t,ordinaryDE C de,if td=0 then delta C.theta T else 0⟩]

def modified (de eh : Fin 4) : Fin 4 → Bool := ![decide (eh=1),false,false,decide (de=3)]

def positiveRemoved (C : SignedCycle) (bt td : Fin 4) : ℝ :=
  positivePart (delta C.theta G)+(if bt=3 then positivePart (delta C.theta B) else 0)+
    (if td=2 then positivePart (delta C.theta T) else 0)

def negativeRemoved (C : SignedCycle) (bt td de eh : Fin 4) : ℝ :=
  negativePart (delta C.theta G)+(if bt=3 then negativePart (delta C.theta B) else 0)+
    (if td=2 then negativePart (delta C.theta T) else 0)+deAngle C de+ehAngle C eh

theorem sum_parts (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (f : ℝ → ℝ) (hf0 : f 0=0) :
    (∑ i,(f (blocks C ab bt td de eh n k l b t i).u+
      f (blocks C ab bt td de eh n k l b t i).v))=
      (∑ j,f (delta C.theta j))-f (delta C.theta G)-
        (if bt=3 then f (delta C.theta B) else 0)-
        (if td=2 then f (delta C.theta T) else 0)-
        f (primaryDE C de)-f (primaryEH C eh) := by
  have he (i : Fin 4) :
      f (blocks C ab bt td de eh n k l b t i).u+f (blocks C ab bt td de eh n k l b t i).v=
      f (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).u+
        f (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).v := by
    fin_cases i <;> simp [blocks,ActualCoreEBlocks.blocks]
  simp_rw [he]
  exact ActualCoreEBlocks.sum_parts C hab hbt htd hde heh n k l b t f hf0

theorem removed_nonneg {C : SignedCycle} {bt td de eh : Fin 4}
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    0≤positiveRemoved C bt td ∧ 0≤negativeRemoved C bt td de eh ∧
      deAngle C de∈Icc 0 (negativeRemoved C bt td de eh) ∧
      ehAngle C eh∈Icc 0 (negativeRemoved C bt td de eh) := by
  have hPB : 0≤(if bt=3 then positivePart (delta C.theta B) else 0) := by
    split_ifs
    · exact positivePart_nonneg _
    · exact le_rfl
  have hPT : 0≤(if td=2 then positivePart (delta C.theta T) else 0) := by
    split_ifs
    · exact positivePart_nonneg _
    · exact le_rfl
  have hNB : 0≤(if bt=3 then negativePart (delta C.theta B) else 0) := by
    split_ifs
    · exact negativePart_nonneg _
    · exact le_rfl
  have hNT : 0≤(if td=2 then negativePart (delta C.theta T) else 0) := by
    split_ifs
    · exact negativePart_nonneg _
    · exact le_rfl
  have hPG := positivePart_nonneg (delta C.theta G)
  have hNG := negativePart_nonneg (delta C.theta G)
  dsimp only [positiveRemoved,negativeRemoved,deAngle,ehAngle]
  exact ⟨by linarith,by linarith,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem budgets {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    positiveRemoved C bt td∈Icc 0 frameCap ∧
    negativeRemoved C bt td de eh∈Icc 0 frameCap ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤frameCap-positiveRemoved C bt td ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      positiveRemoved C bt td-negativeRemoved C bt td de eh+
        ∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  have hp := sum_parts C hab hbt htd hde heh n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t negativePart negativePart_zero
  have hPd : positivePart (primaryDE C de)=0 := max_eq_right hd
  have hPe : positivePart (primaryEH C eh)=0 := max_eq_right he
  have hNd : negativePart (primaryDE C de)=deAngle C de := max_eq_left (neg_nonneg.mpr hd)
  have hNe : negativePart (primaryEH C eh)=ehAngle C eh := max_eq_left (neg_nonneg.mpr he)
  have hp' : (∑ i,(blocks C ab bt td de eh n k l b t i).P)=
      positiveVariation C.theta-positiveRemoved C bt td := by
    change (∑ i,(positivePart (blocks C ab bt td de eh n k l b t i).u+
      positivePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hp,hPd,hPe]
    dsimp [positiveVariation,positiveRemoved]
    ring
  have hn' : (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      negativeVariation C.theta-negativeRemoved C bt td de eh := by
    change (∑ i,(negativePart (blocks C ab bt td de eh n k l b t i).u+
      negativePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hn,hNd,hNe]
    dsimp [negativeVariation,negativeRemoved]
    ring
  have hP0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).N_nonneg)
  have hn0 := removed_nonneg (bt := bt) (td := td) hd he
  have hv := variations_equal C.theta
  exact ⟨⟨hn0.1,by linarith⟩,⟨hn0.2.1,by linarith⟩,by linarith,by linarith⟩

theorem block_minorant {C : SignedCycle} {ab bt td de eh : Fin 4}
    {n l b t s : ℝ} {p q : Fin 4 → ℝ}
    (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hn : k≤n ∧ n≤2069/2000) (ht : k≤t ∧ (td=0 → t≤2069/2000))
    (hs : s∈Icc 0 frameCap)
    (hd : deAngle C de∈Icc 0 s) (he : ehAngle C eh∈Icc 0 s)
    (hp : ∀ i,0<p i)
    (hcoeff : ∀ i,(ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=p i ∧
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=q i)
    (hP : ∀ i,(blocks C ab bt td de eh n k l b t i).P≤frameCap)
    (hN : ∀ i,(blocks C ab bt td de eh n k l b t i).N≤frameCap-s)
    (i : Fin 4) :
    F (modified de eh i) (p i) (q i) s
      (blocks C ab bt td de eh n k l b t i).P
      (blocks C ab bt td de eh n k l b t i).N≤
        (blocks C ab bt td de eh n k l b t i).increment (Real.sqrt qCap) := by
  have hordinary (j : Fin 4)
      (hb : blocks C ab bt td de eh n k l b t j=
        ActualCoreEBlocks.blocks C ab bt td de eh n k l b t j)
      (hm : modified de eh j=false) :
      F (modified de eh j) (p j) (q j) s
        (blocks C ab bt td de eh n k l b t j).P
        (blocks C ab bt td de eh n k l b t j).N≤
          (blocks C ab bt td de eh n k l b t j).increment (Real.sqrt qCap) := by
    have hc := hcoeff j
    have hpos : 0≤(blocks C ab bt td de eh n k l b t j).p := by rw [hb,hc.1]; exact (hp j).le
    have hh := (blocks C ab bt td de eh n k l b t j).minorant (Real.sqrt qCap)
      hpos (hP j) (by linarith [hN j,hs.1])
    simpa [hm,F,hb,hc.1,hc.2] using hh
  fin_cases i
  · rcases heh with rfl | rfl
    · apply hordinary 0
      · simp [blocks,ActualCoreEBlocks.blocks,ehWeight,ehAngle,primaryEH]
      · simp [modified]
    · have hbud : negativePart (delta C.theta H)≤frameCap-s := by
        simpa [blocks,Block.N,ordinaryEH] using hN 0
      have hh := actual_minorant hn hs he (hsmall H) hbud
      simpa [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryEH,
        ehWeight,NegativeEOneAngle.increment] using hh
  · apply hordinary 1 <;> simp [blocks,ActualCoreEBlocks.blocks,modified]
  · apply hordinary 2 <;> simp [blocks,ActualCoreEBlocks.blocks,modified]
  · rcases hde with rfl | rfl
    · apply hordinary 3
      · simp [blocks,ActualCoreEBlocks.blocks,deWeight,deAngle,primaryDE]
      · simp [modified]
    · rcases htd with rfl | rfl
      · have hbud : negativePart (delta C.theta T)≤frameCap-s := by
          simpa [blocks,Block.N,ordinaryDE] using hN 3
        have hh := actual_minorant ⟨ht.1,ht.2 rfl⟩ hs hd (hsmall T) hbud
        simpa [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryDE,
          deWeight,NegativeEOneAngle.increment,pairNorm_symm] using hh
      · simp [blocks,Block.P,Block.N,Block.increment,modified,F,ordinaryDE]

theorem actual_lower {C : SignedCycle} {ab bt td de eh : Fin 4} {n l b t lam : ℝ}
    {p q : Fin 4 → ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hn : k≤n ∧ n≤2069/2000) (ht : k≤t ∧ (td=0 → t≤2069/2000))
    (hdom : Domain (positiveRemoved C bt td) (negativeRemoved C bt td de eh) l p q)
    (hcoeff : ∀ i,(ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=p i ∧
      (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=q i)
    (hlam : 369/500≤lam) :
    min (V (Real.sqrt qCap) l k (positiveRemoved C bt td)) (lam*positiveRemoved C bt td)≤
      lam*negativeRemoved C bt td de eh+
        ∑ i,(blocks C ab bt td de eh n k l b t i).increment (Real.sqrt qCap) := by
  have hb := budgets hab hbt htd hde heh n k l b t hvar hd he
  have hremoved := removed_nonneg (bt := bt) (td := td) hd he
  have hPsum : (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤frameCap := by
    linarith [hb.2.2.1,hb.1.1]
  have hNsum : (∑ i,(blocks C ab bt td de eh n k l b t i).N)≤
      frameCap-negativeRemoved C bt td de eh := by
    rw [hb.2.2.2]
    linarith [hb.2.2.1]
  have hP (i : Fin 4) : (blocks C ab bt td de eh n k l b t i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => (blocks C ab bt td de eh n k l b t j).P_nonneg)
      (Finset.mem_univ i)).trans hPsum
  have hN (i : Fin 4) : (blocks C ab bt td de eh n k l b t i).N≤
      frameCap-negativeRemoved C bt td de eh :=
    (Finset.single_le_sum (fun j _ => (blocks C ab bt td de eh n k l b t j).N_nonneg)
      (Finset.mem_univ i)).trans hNsum
  have hminor := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    block_minorant htd hde heh hsmall hn ht hb.2.1 hremoved.2.2.1 hremoved.2.2.2
      hdom.positive hcoeff hP hN i)
  have hangular := mixed_sum_lower hdom hlam (modified de eh)
    (fun i => (blocks C ab bt td de eh n k l b t i).P)
    (fun i => (blocks C ab bt td de eh n k l b t i).N)
    (fun i => (blocks C ab bt td de eh n k l b t i).P_nonneg)
    (fun i => (blocks C ab bt td de eh n k l b t i).N_nonneg)
    hb.2.2.1 hb.2.2.2
  exact hangular.trans (by linarith)

end SquaresInCircles.Eight.FlatEBlocks
end
end
end

section
/-!
## The original seven-edge stress with both E secants

The two negative primary multipliers cancel E's
tangential force exactly. Its remaining work uses the original flat
coordinate 7/12. All other point bounds use the same original radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatEStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks

def weights (C : SignedCycle) (de eh : Fin 4) (n k l b t : ℝ) : Vertex → ℝ :=
  ![n,k,l,b,t,deWeight C de,ehWeight C eh]

def forces (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : Vertex → Point :=
  force C (CoreEStress.owners ab bt td de eh) (weights C de eh n k l b t)

def bound (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : Vertex → ℝ :=
  let F := forces C ab bt td de eh n k l b t
  ![signedSupport R 1 (F H),circleSupport R (F G),signedSupport R 1 (F A),
    signedSupport R (-1) (F B),
    if flatT then work (F T) (C.point T) else circleSupport R (F T),
    signedSupport R (-1) (F D),work (F E) (C.point E)]

def defect (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : ℝ :=
  demand C (weights C de eh n k l b t)-∑ i,bound C ab bt td de eh flatT n k l b t R i

def anchorNorms (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  pairNorm (ehWeight C eh) n (delta C.theta H+ordinaryEH C eh)+
  pairNorm k l (if ab=0 then 0 else delta C.theta A)+
  pairNorm l b ((if ab=0 then delta C.theta A else 0)+(if bt=2 then delta C.theta B else 0))+
  pairNorm (deWeight C de) t (ordinaryDE C de+(if td=0 then delta C.theta T else 0))

def halfShift (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  (n*PositiveAngularEnvelope.phi (delta C.theta H)+ehWeight C eh*PositiveAngularEnvelope.phi (ordinaryEH C eh)+k+
    l*PositiveAngularEnvelope.phi (if ab=0 then 0 else delta C.theta A)+
    b*PositiveAngularEnvelope.phi (if bt=2 then delta C.theta B else 0)+
    l*PositiveAngularEnvelope.phi (if ab=0 then delta C.theta A else 0)+
    deWeight C de*PositiveAngularEnvelope.phi (ordinaryDE C de)+t*PositiveAngularEnvelope.phi (if td=0 then delta C.theta T else 0))/2

def zeroNorms (C : SignedCycle) (de eh : Fin 4) (n k l b t : ℝ) : ℝ :=
  pairNorm n (ehWeight C eh) 0+pairNorm k l 0+pairNorm l b 0+pairNorm (deWeight C de) t 0

def increment (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t R : ℝ) : ℝ :=
  ∑ i,(FlatEBlocks.blocks C ab bt td de eh n k l b t i).increment R

theorem force_H {eh : Fin 4} (heh : eh=0 ∨ eh=1)
    (C : SignedCycle) (ab bt td de : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t H=
      rotatedPair (ehWeight C eh) n (delta C.theta H) (ordinaryEH C eh) := by
  rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,H,E,source,target,
      add,scale,rotatedPair,ordinaryEH] <;> (try refine ⟨?_,?_⟩) <;> ring

theorem force_A (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t A=CoreEStress.forces C ab bt td de eh n k l b t A := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,A]

theorem force_B (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t B=CoreEStress.forces C ab bt td de eh n k l b t B := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,B]

theorem force_D {td de : Fin 4} (htd : td=0 ∨ td=2) (hde : de=2 ∨ de=3)
    (C : SignedCycle) (ab bt eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t D=
      let v := rotatedPair (deWeight C de) t (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
      (v.1,-v.2) := by
  rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,D,T,source,target,
      add,scale,rotatedPair,ordinaryDE] <;> ring

theorem force_G (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t G=CoreEStress.forces C ab bt td de eh n k l b t G := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,G]

theorem force_T (C : SignedCycle) (ab bt td de eh : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t T=CoreEStress.forces C ab bt td de eh n k l b t T := by
  simp [forces,CoreEStress.forces,force,weights,SecondaryEStress.weights,previous,T]

theorem force_E {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    forces C ab bt td de eh n k l b t E=
      (-(Real.tan (deAngle C de)+Real.tan (ehAngle C eh)),0) := by
  have hcD : Real.cos (delta C.theta 5)≠0 := (transport_cos_pos (hsmall 5)).ne'
  have hcE : Real.cos (delta C.theta 6)≠0 := (transport_cos_pos (hsmall 6)).ne'
  rcases hde with rfl | rfl <;> rcases heh with rfl | rfl <;>
    simp [forces,force,CoreEStress.owners,weights,previous,word,D,E,source,target,
      add,scale,deWeight,ehWeight,deAngle,ehAngle,primaryDE,primaryEH,
      Real.tan_eq_sin_div_cos] <;> (try refine ⟨?_,?_⟩) <;> field_simp [hcD,hcE] <;> ring

theorem E_work {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hflat : (C.point E).a=7/12)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    work (forces C ab bt td de eh n k l b t E) (C.point E)=
      -(7/12)*(Real.tan (deAngle C de)+Real.tan (ehAngle C eh)) := by
  rw [force_E hde heh hsmall]
  simp [work,hflat]
  ring

theorem increment_eq {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (n k l b t R : ℝ) :
    increment C ab bt td de eh n k l b t R=
      n*psi (delta C.theta H)+l*psi (delta C.theta A)+
      b*psi (if bt=2 then delta C.theta B else 0)+t*psi (if td=0 then delta C.theta T else 0)+
      deWeight C de*psi (ordinaryDE C de)+ehWeight C eh*psi (ordinaryEH C eh)-
      R*(anchorNorms C ab bt td de eh n k l b t-zeroNorms C de eh n k l b t) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;> rcases htd with rfl | rfl <;>
    simp [increment,FlatEBlocks.blocks,ActualOrdinaryBlocks.Block.increment,
      anchorNorms,zeroNorms,Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm n (ehWeight C eh)] <;> ring

theorem defect_as_anchors {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (flatT : Bool) (n k l b t R : ℝ) :
    defect C ab bt td de eh flatT n k l b t R=
      demand C (weights C de eh n k l b t)+halfShift C ab bt td de eh n k l b t-
      R*anchorNorms C ab bt td de eh n k l b t-
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t G)-
      (if flatT then work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t T))-
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
  have hH := rotatedPair_signedSupport R (ehWeight C eh) n (delta C.theta H) (ordinaryEH C eh)
  have hA := rotatedPair_signedSupport R k l (if ab=0 then 0 else delta C.theta A) 0
  have hB := reflected_rotatedPair_signedSupport R b l
    (if ab=0 then delta C.theta A else 0) (if bt=2 then delta C.theta B else 0)
  have hD := reflected_rotatedPair_signedSupport R (deWeight C de) t
    (if td=0 then delta C.theta T else 0) (ordinaryDE C de)
  rw [pairNorm_symm b l] at hB
  unfold defect
  have hsum : (∑ i,bound C ab bt td de eh flatT n k l b t R i)=
      signedSupport R 1 (forces C ab bt td de eh n k l b t H)+
      circleSupport R (forces C ab bt td de eh n k l b t G)+
      signedSupport R 1 (forces C ab bt td de eh n k l b t A)+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t B)+
      (if flatT then work (forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (forces C ab bt td de eh n k l b t T))+
      signedSupport R (-1) (forces C ab bt td de eh n k l b t D)+
      work (forces C ab bt td de eh n k l b t E) (C.point E) := by
    simp [bound,Fin.sum_univ_succ,H,G,A,B,T,D,E]
    ring
  rw [hsum,force_H heh,force_A,force_B,CoreEStress.force_A hab,CoreEStress.force_B hab hbt,
    force_D htd hde,force_G,force_T,hH,hA,hB,hD]
  simp only [phi_zero,mul_one,add_zero]
  dsimp [anchorNorms,halfShift]
  rw [add_comm (if td=0 then delta C.theta T else 0) (ordinaryDE C de)]
  ring

theorem necessary_at_cap {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    {n k l b t : ℝ} (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (flatT : Bool) (hw : 0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) :
    defect C ab bt td de eh flatT n k l b t (Real.sqrt qCap)≤0 := by
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hp := primary_small (de := de) (eh := eh) hsmall
  have hcD : 0<Real.cos (deAngle C de) := by
    simpa [deAngle] using transport_cos_pos hp.1
  have hcE : 0<Real.cos (ehAngle C eh) := by
    simpa [ehAngle] using transport_cos_pos hp.2
  have hweight : ∀ i,0≤weights C de eh n k l b t i := by
    intro i
    fin_cases i <;> simp [weights,deWeight,ehWeight] <;>
      first | positivity | linarith [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2]
  have hc (i : Vertex) : (C.point i).Contained ((Real.sqrt qCap)^2) := by
    rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
    exact (hC.contained i).trans hq
  have hb : ∀ i,work (forces C ab bt td de eh n k l b t i) (C.point i)≤
      bound C ab bt td de eh flatT n k l b t (Real.sqrt qCap) i := by
    intro i
    fin_cases i
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc H) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.H_nonneg]) _
    · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted G) (hc G) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc A) (Or.inl rfl)
        (by simp [abs_of_nonneg hn.A_nonneg]) _
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc B) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.B_nonpos]) _
    · cases flatT
      · exact work_le_circleSupport (Real.sqrt_nonneg _) (hC.sorted T) (hc T) _
      · exact le_rfl
    · exact work_le_signed_support (Real.sqrt_nonneg _) (hc D) (Or.inr rfl)
        (by simp [abs_of_nonpos hn.D_nonpos]) _
    · exact le_rfl
  have hh := weighted_separation_le hweight hf hb
  dsimp [defect]
  linarith

end SquaresInCircles.Eight.FlatEStress
end
end
end

section
/-!
## Actual coefficient families for the flat-primary angular envelope

Every coefficient condition in the joint envelope
is proved here for the existing positive and negative T weights. The
total removed mass may include either or both negative E primaries;
the short negative T angle remains its original independent summand.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FlatPrimaryParameters
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open PositiveOrdinaryEnvelope FlatPrimaryEnvelope

theorem secant_mono {u s : ℝ} (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 s) :
    (2069/2000)/Real.cos u≤(2069/2000)/Real.cos s := by
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,hu.2.trans hs.2⟩
  have hcU : 0<Real.cos u := by linarith [(transport_trig hu').1]
  have hcS : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hu.1
    (by norm_num [frameCap] at hs; linarith [hs.2,Real.pi_gt_three]) hu.2
  exact (div_le_div_iff₀ hcU hcS).2 (by linarith)

theorem positive {d s l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t)
    (hs : s∈Icc 0 frameCap) : Domain d s l (ps n l t) (qs b t) := by
  have hd := PositiveOrdinaryEnvelope.domains h
  have hsec : (2069/2000 : ℝ)≤(2069/2000)/Real.cos s := by
    simpa using secant_mono hs (show (0:ℝ)∈Icc 0 s from ⟨le_rfl,hs.1⟩)
  refine ⟨h.angle,hs,h.ell_lower,h.ell_upper.le,
    (fun i => (hd i).1),(fun i => (hd i).2.1),(fun i => (hd i).2.2.1),
    (fun i => (hd i).2.2.2.2.1),
    (fun i => (hd i).2.2.2.2.2.trans hsec),?_,?_,?_,
    PositiveOrdinaryEnvelope.high_domains h,?_,(fun hz => (h.low hz).2.2.2)⟩
  · intro i
    have hq0 := ((hd i).1.trans_le (hd i).2.1).le
    have hh := mul_le_mul_of_nonneg_right
      (show ratio d-31/10000≤ratio d by linarith) hq0
    exact hh.trans (hd i).2.2.2.1
  · intro i
    have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
    have hDup : max 1 t≤109/100 := max_le (by norm_num) (by linarith [h.D_upper])
    fin_cases i
    · right; simpa [ps,qs] using And.intro h.H_lower (by norm_num : (1:ℝ)≤109/100)
    · left; simp [ps]
    · left; simp [ps]
    · right; simpa [ps,qs] using And.intro hDlo hDup
  · intro i hi _
    have hq0 := ((hd i).1.trans_le (hd i).2.1).le
    have hr : ratio (d-s)≤ratio d := by dsimp [ratio]; linarith [hs.1]
    have hh := (mul_le_mul_of_nonneg_right hr hq0).trans (hd i).2.2.2.1
    simpa [hi] using hh
  · intro hz i
    have hh := PositiveOrdinaryEnvelope.low_domains h hz i
    exact ⟨hh.1,fun _ => hh.2⟩

theorem negative {d u s b t : ℝ}
    (h : NegativeOrdinaryParameters.Bounds d u b t)
    (hs : s∈Icc 0 frameCap) (hus : u≤ s)
    (hblow : d≤3/10 → b≤1) :
    Domain d s (lN d) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t) (qs b t) := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hd := NegativeOrdinaryParameters.domains h
  have hsec := secant_mono hs ⟨h.short.1,hus⟩
  have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDup : max 1 t≤109/100 :=
    max_le (by norm_num) (NegativeOrdinaryParameters.coefficient_ranges h).2.1
  refine ⟨h.angle,hs,hb.ell_lower,hb.ell_upper.le,
    (fun i => (hd i).1),(fun i => (hd i).2.1),(fun i => (hd i).2.2.1),
    (fun i => (hd i).2.2.2.2.1),
    (fun i => (hd i).2.2.2.2.2.1.trans hsec),
    (fun i => (hd i).2.2.2.1),?_,?_,NegativeOrdinaryParameters.high_domains h,?_,
    (fun hz => (hb.low hz).2.2.2)⟩
  · intro i
    fin_cases i
    · right; simpa [ps,qs] using And.intro hb.H_lower (by norm_num : (1:ℝ)≤109/100)
    · left; simp [ps]
    · left; simp [ps]
    · right; simpa [ps,qs] using And.intro hDlo hDup
  · intro i hi hsd
    have hr : ratio (d-s)≤ratio (d-u) := by dsimp [ratio]; linarith
    have hB0 : 0≤b := (by norm_num [k] : (0:ℝ)≤k).trans h.B_lower
    have hB := (mul_le_mul_of_nonneg_right hr hB0).trans
      (h.shortened (hus.trans hsd))
    have hr' : ratio (d-s)≤ratio d := by dsimp [ratio]; linarith [hs.1]
    have hA : ratio (d-s)*k≤lN d := by
      have hh := (mul_le_mul_of_nonneg_left hb.B_lower
        (show 0≤ratio d by dsimp [ratio]; linarith [h.angle.1])).trans hb.correlated
      exact (mul_le_mul_of_nonneg_right hr' (by norm_num [k] : 0≤k)).trans hh
    fin_cases i
    · change SecondaryEStress.tiltedWeight k (19/50) d=lN d at hi
      exact False.elim (by linarith [hb.H_lower,hb.ell_upper])
    · simpa [ps,qs] using hA
    · simpa [ps,qs] using hB
    · simp [ps] at hi
      exact False.elim (by linarith [hDlo,hb.ell_upper])
  · intro hz i
    refine ⟨(NegativeOrdinaryParameters.low_domains h hz i).1,?_⟩
    intro hi
    fin_cases i
    · simp [qs]
    · norm_num [qs,k]
    · simpa [qs] using hblow hz
    · simp [ps] at hi
      exact False.elim (by linarith [hDlo,hb.ell_upper])

theorem low_cN {d : ℝ} (hd : d∈Icc 0 (3/10)) : cN d≤1909/2000 := by
  have hm := mul_nonneg (show 0≤3/10-d by linarith [hd.2])
    (show 0≤7/20-(3/20)*(d+3/10) by linarith [hd.1,hd.2])
  dsimp [cN]
  nlinarith

theorem low_secant_cN {d u : ℝ} (hd : d∈Icc 0 (3/10))
    (hu : u∈Icc 0 (3/10)) : cN d/Real.cos u≤1 := by
  have hc := NegativeOrdinaryParameters.short_cos hu
  exact (div_le_one hc.2.1).2 (by linarith [low_cN hd,hc.1])

theorem negativeTD {d u s : ℝ} (hd : d∈Icc 0 frameCap)
    (hu : u∈Icc 0 (3/10)) (hs : s∈Icc 0 frameCap) (hus : u≤ s) :
    Domain d s (lN d)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) (cN d/Real.cos u))
      (qs (cN d) (cN d/Real.cos u)) := by
  apply negative (NegativeOrdinaryParameters.familyTD hd hu) hs hus
  intro hz
  linarith [low_cN ⟨hd.1,hz⟩]

theorem negativeBT {d u s : ℝ} (hd : d∈Icc 0 frameCap)
    (hu : u∈Icc 0 (9/100)) (hs : s∈Icc 0 frameCap) (hus : u≤ s) :
    Domain d s (lN d)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) (cN d))
      (qs (cN d/Real.cos u) (cN d)) := by
  apply negative (NegativeOrdinaryParameters.familyBT hd hu) hs hus
  intro hz
  exact low_secant_cN ⟨hd.1,hz⟩ ⟨hu.1,by linarith [hu.2]⟩

end SquaresInCircles.Eight.FlatPrimaryParameters
end
end
end

section
/-!
## Applying the joint envelope to the original flat-E stress

The coefficient maps are instantiated here, and the
removed masses are evaluated in each actual T regime. Every secant gain
is the proved analytic gain of the same weighted anchor norm.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatEAngularApplication
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks
open FlatTStress GlobalGA PositiveOrdinaryEnvelope

theorem secant_lower {a e : ℝ} (ha : k≤a) (he : e∈Icc 0 frameCap) :
    (103/100)*e≤ secantCharge (Real.sqrt qCap) 1 a e := by
  rw [secantCharge_eq (by norm_num : (0:ℝ)<1) he]
  simp only [div_one,one_mul]
  by_cases hz : e=0
  · simp [hz,secantGain_zero]
  · exact (PositiveSecantGain.strict_gain (q := qCap) (by norm_num [qCap]) le_rfl
      ha ⟨lt_of_le_of_ne he.1 (Ne.symm hz),he.2⟩).le

theorem pair_gain {n t a e lam : ℝ} (hn : k≤n) (ht : k≤t)
    (ha : a∈Icc 0 frameCap) (he : e∈Icc 0 frameCap) (hlam : lam≤103/100) :
    lam*(a+e)≤ secantCharge (Real.sqrt qCap) 1 n e+
      secantCharge (Real.sqrt qCap) 1 t a := by
  have h1 := secant_lower hn he
  have h2 := secant_lower ht ha
  have hm := mul_le_mul_of_nonneg_right hlam (add_nonneg ha.1 he.1)
  linarith

theorem N_lambda {d : ℝ} (hd : d∈Icc 0 frameCap) :
    369/500≤lambdaN d ∧ lambdaN d≤103/100 := by
  refine ⟨?_,(ShortSecantGain.negative_family_slopes hd).1⟩
  dsimp [lambdaN]
  linarith [hd.1]

theorem positive_coefficients {d l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t)
    (C : SignedCycle) (ab bt td de eh : Fin 4) (i : Fin 4) :
    (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).p=ps n l t i ∧
    (ActualCoreEBlocks.blocks C ab bt td de eh n k l b t i).q=qs b t i := by
  have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh n k l b t i
  have h2 := PositiveOrdinaryEnvelope.block_coefficients h C ab bt td i
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

theorem negative_coefficients {d u b t : ℝ}
    (h : NegativeOrdinaryParameters.Bounds d u b t)
    (C : SignedCycle) (ab bt td de eh : Fin 4) (i : Fin 4) :
    (ActualCoreEBlocks.blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t i).p=
      ps (tiltedWeight k (19/50) d) (lN d) t i ∧
    (ActualCoreEBlocks.blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t i).q=
      qs b t i := by
  have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh
    (tiltedWeight k (19/50) d) k (lN d) b t i
  have h2 := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

theorem nonnegative_removed {C : SignedCycle} {bt td de eh : Fin 4}
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T) :
    negativeRemoved C bt td de eh=deAngle C de+ehAngle C eh := by
  have hB : (if bt=3 then negativePart (delta C.theta B) else 0)=0 := by
    by_cases hb : bt=3
    · simp [hb,negativePart,max_eq_right (neg_nonpos.mpr (hBT hb))]
    · simp [hb]
  have hT : (if td=2 then negativePart (delta C.theta T) else 0)=0 := by
    by_cases ht : td=2
    · simp [ht,negativePart,max_eq_right (neg_nonpos.mpr (hTD ht))]
    · simp [ht]
  have hG' : negativePart (delta C.theta G)=0 := max_eq_right (neg_nonpos.mpr hG)
  rw [negativeRemoved,hB,hT,hG']
  ring

theorem nonnegative_T_lower {C : SignedCycle} {ab bt td de eh : Fin 4}
    {n l b t lam : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hBT : bt=3 → 0≤delta C.theta B)
    (hTD : td=2 → 0≤delta C.theta T)
    (hcoeff : PositiveOrdinaryParameters.Bounds (positiveRemoved C bt td) l n b t)
    (hlam : lam∈Icc (369/500) (103/100)) :
    min (V (Real.sqrt qCap) l k (positiveRemoved C bt td)) (lam*positiveRemoved C bt td)≤
      secantCharge (Real.sqrt qCap) 1 n (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 t (deAngle C de)+
      FlatEStress.increment C ab bt td de eh n k l b t (Real.sqrt qCap) := by
  have hb := budgets hab hbt htd hde heh n k l b t hvar hd he
  have hdom := FlatPrimaryParameters.positive hcoeff hb.2.1
  have hinc := actual_lower hab hbt htd hde heh hsmall hvar hd he
    ⟨hcoeff.H_lower,by linarith [hcoeff.H_upper]⟩
    ⟨hcoeff.D_lower,fun _ => hcoeff.D_upper⟩ hdom
    (positive_coefficients hcoeff C ab bt td de eh) hlam.1
  have hr := removed_nonneg (bt := bt) (td := td) hd he
  have hgain := pair_gain hcoeff.H_lower hcoeff.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hb.2.1.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hb.2.1.2⟩) hlam.2
  rw [nonnegative_removed hG hBT hTD] at hinc
  change _≤_+_+∑ i,_
  linarith

theorem negative_TD_lower {C : SignedCycle} {ab de eh : Fin 4} {u : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (3/10)) (hT : delta C.theta T= -u) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤
      secantCharge (Real.sqrt qCap) (cN (delta C.theta G)) 1 u+
      secantCharge (Real.sqrt qCap) 1 (tiltedWeight k (19/50) (delta C.theta G)) (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 (cN (delta C.theta G)/Real.cos u) (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k (19/50) (delta C.theta G)) k
        (lN (delta C.theta G)) (cN (delta C.theta G)) (cN (delta C.theta G)/Real.cos u)
        (Real.sqrt qCap) := by
  let d := delta C.theta G
  let s := negativeRemoved C 2 2 de eh
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hpos : positiveRemoved C 2 2=d := by
    simp [positiveRemoved,d,hT,positivePart,max_eq_left hG,max_eq_right (neg_nonpos.mpr hu.1.le)]
  have hneg : s=u+deAngle C de+ehAngle C eh := by
    simp [s,negativeRemoved,hT,negativePart,max_eq_right (neg_nonpos.mpr hG),max_eq_left hu.1.le]
  have hb := budgets hab (Or.inl rfl) (Or.inr rfl) hde heh
    (tiltedWeight k (19/50) d) k (lN d) (cN d) (cN d/Real.cos u) hvar hd he
  have hs : s∈Icc 0 frameCap := hb.2.1
  have hr := removed_nonneg (bt := 2) (td := 2) hd he
  have hus : u ≤ s := by rw [hneg]; linarith [hr.2.2.1.1,hr.2.2.2.1]
  have hc := NegativeOrdinaryParameters.familyTD hd' (Ioc_subset_Icc_self hu)
  have hdom := FlatPrimaryParameters.negativeTD hd' (Ioc_subset_Icc_self hu) hs hus
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hn : k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤2069/2000 :=
    ⟨hp.H_lower,by linarith [hp.H_upper]⟩
  have hinc := actual_lower hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hvar hd he hn
    ⟨hc.D_lower,by intro h; norm_num at h⟩
    (by simpa [hpos,s] using hdom)
    (negative_coefficients hc C ab 2 2 de eh) (N_lambda hd').1
  rw [hpos] at hinc
  have hegain := pair_gain hp.H_lower hc.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hs.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hs.2⟩) (N_lambda hd').2
  have hc0 : 0<cN d := (by norm_num [k] : (0:ℝ)<k).trans_le hp.B_lower
  have htGain := (PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd' ⟨hu.1,hu'.2⟩).le
  rw [← secantCharge_eq hc0 hu' 1] at htGain
  change _≤_+_+_+∑ i,_
  have hneg' : negativeRemoved C _ _ de eh=u+deAngle C de+ehAngle C eh := hneg
  dsimp only [d] at *
  rw [hneg'] at hinc
  linarith


theorem negative_BT_lower {C : SignedCycle} {ab de eh : Fin 4} {u : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (9/100)) (hB : delta C.theta B= -u) :
    min (V (Real.sqrt qCap) (lN (delta C.theta G)) k (delta C.theta G))
      (lambdaN (delta C.theta G)*delta C.theta G)≤
      secantCharge (Real.sqrt qCap) (cN (delta C.theta G)) (lN (delta C.theta G)) u+
      secantCharge (Real.sqrt qCap) 1 (tiltedWeight k (19/50) (delta C.theta G)) (ehAngle C eh)+
      secantCharge (Real.sqrt qCap) 1 (cN (delta C.theta G)) (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k (19/50) (delta C.theta G)) k
        (lN (delta C.theta G)) (cN (delta C.theta G)/Real.cos u) (cN (delta C.theta G))
        (Real.sqrt qCap) := by
  let d := delta C.theta G
  let s := negativeRemoved C 3 0 de eh
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hsmall G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hpos : positiveRemoved C 3 0=d := by
    simp [positiveRemoved,d,hB,positivePart,max_eq_left hG,max_eq_right (neg_nonpos.mpr hu.1.le)]
  have hneg : s=u+deAngle C de+ehAngle C eh := by
    simp [s,negativeRemoved,hB,negativePart,max_eq_right (neg_nonpos.mpr hG),max_eq_left hu.1.le]
  have hb := budgets hab (Or.inr rfl) (Or.inl rfl) hde heh
    (tiltedWeight k (19/50) d) k (lN d) (cN d/Real.cos u) (cN d) hvar hd he
  have hs : s∈Icc 0 frameCap := hb.2.1
  have hr := removed_nonneg (bt := 3) (td := 0) hd he
  have hus : u ≤ s := by rw [hneg]; linarith [hr.2.2.1.1,hr.2.2.2.1]
  have hc := NegativeOrdinaryParameters.familyBT hd' (Ioc_subset_Icc_self hu)
  have hdom := FlatPrimaryParameters.negativeBT hd' (Ioc_subset_Icc_self hu) hs hus
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hn : k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤2069/2000 :=
    ⟨hp.H_lower,by linarith [hp.H_upper]⟩
  have hinc := actual_lower hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hvar hd he hn
    ⟨hp.D_lower,fun _ => hp.D_upper⟩
    (by simpa [hpos,s] using hdom)
    (negative_coefficients hc C ab 3 0 de eh) (N_lambda hd').1
  rw [hpos] at hinc
  have hegain := pair_gain hp.H_lower hp.D_lower
    (show deAngle C de∈Icc 0 frameCap from ⟨hr.2.2.1.1,hr.2.2.1.2.trans hs.2⟩)
    (show ehAngle C eh∈Icc 0 frameCap from ⟨hr.2.2.2.1,hr.2.2.2.2.trans hs.2⟩) (N_lambda hd').2
  have hc0 : 0<cN d := (by norm_num [k] : (0:ℝ)<k).trans_le hp.B_lower
  have htGain := (ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd' hu).le
  rw [← secantCharge_eq hc0 hu' (lN d)] at htGain
  change _≤_+_+_+∑ i,_
  have hneg' : negativeRemoved C _ _ de eh=u+deAngle C de+ehAngle C eh := hneg
  dsimp only [d] at *
  rw [hneg'] at hinc
  linarith


end SquaresInCircles.Eight.FlatEAngularApplication
end
end
end

section
/-!
## Exact E-secant accounting at the original anchors

Each E gain is measured from the actual current H or
D zero-angle norm. Consequently a negative T gain and a negative E gain
at D add exactly, including when both multipliers are secants.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FlatEDecomposition
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope
open PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks FlatEStress FlatTStress

def oldDefect (C : SignedCycle) (ab bt td de eh : Fin 4) (flatT : Bool)
    (n k l b t R : ℝ) : ℝ :=
  if flatT then CoreENegativeStress.flatDefect C ab bt td de eh n k l b t R
  else CoreEStress.defect C ab bt td de eh n k l b t R

theorem old_as_anchors {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (flatT : Bool) (n k l b t R : ℝ) :
    oldDefect C ab bt td de eh flatT n k l b t R=
      demand C (SecondaryEStress.weights n k l b t)+CoreEStress.halfShift C ab bt td de eh n k l b t-
      R*CoreEStress.anchorNorms C ab bt td de eh n k l b t-
      circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t G)-
      (if flatT then work (CoreEStress.forces C ab bt td de eh n k l b t T) (C.point T)
       else circleSupport R (CoreEStress.forces C ab bt td de eh n k l b t T))-
      work (CoreEStress.forces C ab bt td de eh n k l b t E) (C.point E) := by
  cases flatT
  · simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
    rw [CoreEStress.defect,CoreEStress.sum_bounds C hab hbt htd hde heh]
    ring
  · exact CoreENegativeStress.flatDefect_as_anchors hab hbt htd hde heh n k l b t R

theorem DE_balance {C : SignedCycle} {de : Fin 4}
    (hde : de=2 ∨ de=3) (hsmall : |delta C.theta D|≤frameCap)
    (hd : primaryDE C de≤0) :
    deWeight C de*edgeWidth (delta C.theta D)+deWeight C de*PositiveAngularEnvelope.phi (ordinaryDE C de)/2-
      deWeight C de*psi (ordinaryDE C de)+(7/12)*Real.tan (deAngle C de)=
      edgeWidth (delta C.theta D)-edgeWidth (primaryDE C de)+1+
      PositiveAngularEnvelope.phi (ordinaryDE C de)/2-psi (ordinaryDE C de)+
      (1/Real.cos (deAngle C de)-1+(13/12)*Real.tan (deAngle C de)) := by
  rcases hde with rfl | rfl
  · simp [deWeight,deAngle,primaryDE,ordinaryDE,edgeWidth,pairWidth]
  · have hneg : delta C.theta D≤0 := by simpa [primaryDE] using hd
    have ha : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hneg,(neg_le_abs _).trans hsmall⟩
    have hw := edgeWidth_negative_formula ha
    have hc := transport_cos_pos hsmall
    simp only [neg_neg] at hw
    simp [deWeight,deAngle,primaryDE,ordinaryDE,hw,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring

theorem EH_balance {C : SignedCycle} {eh : Fin 4}
    (heh : eh=0 ∨ eh=1) (hsmall : |delta C.theta E|≤frameCap)
    (he : primaryEH C eh≤0) :
    ehWeight C eh*edgeWidth (delta C.theta E)+ehWeight C eh*PositiveAngularEnvelope.phi (ordinaryEH C eh)/2-
      ehWeight C eh*psi (ordinaryEH C eh)+(7/12)*Real.tan (ehAngle C eh)=
      edgeWidth (delta C.theta E)-edgeWidth (primaryEH C eh)+1+
      PositiveAngularEnvelope.phi (ordinaryEH C eh)/2-psi (ordinaryEH C eh)+
      (1/Real.cos (ehAngle C eh)-1+(13/12)*Real.tan (ehAngle C eh)) := by
  rcases heh with rfl | rfl
  · simp [ehWeight,ehAngle,primaryEH,ordinaryEH,edgeWidth,pairWidth]
  · have hneg : delta C.theta E≤0 := by simpa [primaryEH] using he
    have ha : -delta C.theta E∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hneg,(neg_le_abs _).trans hsmall⟩
    have hw := edgeWidth_negative_formula ha
    have hc := transport_cos_pos hsmall
    simp only [neg_neg] at hw
    simp [ehWeight,ehAngle,primaryEH,ordinaryEH,hw,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring

theorem E_work_charge {C : SignedCycle} {de eh : Fin 4}
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (ab bt td : Fin 4) (n k l b t : ℝ) :
    work (CoreEStress.forces C ab bt td de eh n k l b t E) (C.point E)+charge C de eh=
      edgeWidth (primaryDE C de)+edgeWidth (primaryEH C eh)-2 := by
  rw [CoreEStress.force_E hde heh]
  dsimp [work,ActualCoreEBlocks.charge,CoreECharge.pairDeficit]
  ring

theorem accounting {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (flatT : Bool) (n k l b t R : ℝ) :
    FlatEStress.defect C ab bt td de eh flatT n k l b t R=
      oldDefect C ab bt td de eh flatT n k l b t R-charge C de eh+
      secantCharge R 1 n (ehAngle C eh)+secantCharge R 1 t (deAngle C de)+
      FlatEStress.increment C ab bt td de eh n k l b t R-
      CoreEStress.increment C ab bt td de eh n k l b t R := by
  have hD := DE_balance hde (hsmall D) hd
  have hE := EH_balance heh (hsmall E) he
  have hw := E_work_charge (C := C) hde heh ab bt td n k l b t
  have hDemand : demand C (FlatEStress.weights C de eh n k l b t)-
      demand C (SecondaryEStress.weights n k l b t)=
      (deWeight C de-1)*edgeWidth (delta C.theta D)+
        (ehWeight C eh-1)*edgeWidth (delta C.theta E) := by
    simp [demand,FlatEStress.weights,SecondaryEStress.weights,Fin.sum_univ_succ,D,E]
    ring
  rw [FlatEStress.defect_as_anchors hab hbt htd hde heh,
    old_as_anchors hab hbt htd hde heh,
    FlatEStress.E_work hde heh hsmall hflat,
    FlatEStress.increment_eq hab hbt htd]
  dsimp [CoreEStress.increment,FlatEStress.halfShift,CoreEStress.halfShift,
    FlatEStress.zeroNorms,PositivePrimaryBaselines.zeroNorms,secantCharge]
  simp only [one_mul,pairNorm_symm 1 n,pairNorm_symm 1 t]
  dsimp only [deWeight,ehWeight] at *
  rw [pairNorm_symm (1/Real.cos (deAngle C de)) t]
  linarith [hDemand,hD,hE,hw]

theorem positive_TD {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 2 de eh false (tiltedWeight k η (delta C.theta G)) k l
      (tiltedWeight k η (delta C.theta T)) k R=
      tdBaseline R k l η (delta C.theta G) (delta C.theta T)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 k (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l
        (tiltedWeight k η (delta C.theta T)) k R := by
  rw [accounting hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.td_decomposition hab hde heh hk hη hsmall hx hz]
  ring

theorem positive_BT {C : SignedCycle} {ab de eh : Fin 4} {R k l η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hz : delta C.theta B∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 3 0 de eh false (tiltedWeight k η (delta C.theta G)) k l k
      (tiltedWeight k η (delta C.theta B)) R=
      btBaseline R k l η (delta C.theta G) (delta C.theta B)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta B)) (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l k
        (tiltedWeight k η (delta C.theta B)) R := by
  rw [accounting hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.bt_decomposition hab hde heh hk hη hsmall hx hz]
  ring

theorem secondary_T {C : SignedCycle} {ab de eh : Fin 4} {R k l c η : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 0 de eh false (tiltedWeight k η (delta C.theta G)) k l c c R=
      secondaryBaseline R k l c η (delta C.theta G)+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 c (deAngle C de)+
      FlatEStress.increment C ab 2 0 de eh (tiltedWeight k η (delta C.theta G)) k l c c R := by
  rw [accounting hab (Or.inl rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,Bool.false_eq_true,↓reduceIte]
  rw [CoreEStress.secondary_decomposition hab hde heh hk hη hsmall hx]
  ring

theorem negative_TD {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hT : delta C.theta T= -s) (hTflat : (C.point T).a=7/12)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 2 2 de eh true (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c 1 s+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 (c/Real.cos s) (deAngle C de)+
      FlatEStress.increment C ab 2 2 de eh (tiltedWeight k η (delta C.theta G)) k l c (c/Real.cos s) R := by
  rw [accounting hab (Or.inl rfl) (Or.inr rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,↓reduceIte]
  rw [CoreENegativeStress.negative_TD_decomposition hab hde heh hk hη hsmall hx hs hT hTflat]
  ring

theorem negative_BT {C : SignedCycle} {ab de eh : Fin 4} {R k l c η s : ℝ}
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hk : 0≤k) (hη : 0≤η) (hsmall : ∀ i,|delta C.theta i|≤frameCap)
    (hx : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hB : delta C.theta B= -s) (hTflat : (C.point T).a=7/12)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0) :
    FlatEStress.defect C ab 3 0 de eh true (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R=
      secondaryBaseline R k l c η (delta C.theta G)+secantCharge R c l s+
      secantCharge R 1 (tiltedWeight k η (delta C.theta G)) (ehAngle C eh)+
      secantCharge R 1 c (deAngle C de)+
      FlatEStress.increment C ab 3 0 de eh (tiltedWeight k η (delta C.theta G)) k l (c/Real.cos s) c R := by
  rw [accounting hab (Or.inr rfl) (Or.inl rfl) hde heh hsmall hflat hd he]
  simp only [oldDefect,↓reduceIte]
  rw [CoreENegativeStress.negative_BT_decomposition hab hde heh hk hη hsmall hx hs hB hTflat]
  ring

end SquaresInCircles.Eight.FlatEDecomposition
end
end
end

section
/-!
## Exclusion of flat E with both primary errors nonpositive

All five T stress regimes are connected to their
actual original weak witnesses. No coefficient-domain or angular-stress
conclusion is assumed by these geometric exclusion theorems.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FlatEExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks FlatEBlocks
open FlatEAngularApplication

theorem P_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveSplitComparison.familyPBaseline d+
      min (V (Real.sqrt qCap) (lP d) k d) ((103/100)*d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hv := hh.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hv
  have hm : -PositiveSplitComparison.familyPBaseline d<
      min (V (Real.sqrt qCap) (lP d) k d) ((103/100)*d) :=
    lt_min (by linarith) (by linarith [hh.2.1])
  linarith

theorem N_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hv := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hv
  have hm : -PositiveScalarTransfer.BN d<
      min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d) :=
    lt_min (by linarith) (by linarith [hh.2.2.2.2.1])
  linarith

theorem weights_nonneg {d l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t) :
    0≤n ∧ 0≤k ∧ 0≤l ∧ 0≤b ∧ 0≤t := by
  have hk : 0≤k := by norm_num [k]
  exact ⟨hk.trans h.H_lower,hk,by linarith [h.ell_lower],hk.trans h.B_lower,hk.trans h.D_lower⟩

theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hpos : positiveRemoved C 2 0=d := by simp [positiveRemoved,d,positivePart,max_eq_left hG]
  have hinc := nonnegative_T_lower hab (Or.inl rfl) (Or.inl rfl) hde heh hs hvar hd he
    hG (by intro h; norm_num at h) (by intro h; norm_num at h)
    (by simpa [hpos] using hp) (N_lambda hd')
  rw [hpos] at hinc
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.secondary_T hab hde heh (by norm_num [k])
    (by norm_num : (0:ℝ)≤19/50) hs hd' hflat hd he] at hnec
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let x := delta C.theta G
  let z := delta C.theta T
  let d := x+z
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hb := budgets hab (Or.inl rfl) (Or.inr rfl) hde heh 0 0 0 0 0 hvar hd he
  have hpos : positiveRemoved C 2 2=d := by
    simp [positiveRemoved,d,x,z,positivePart,max_eq_left hG,max_eq_left hT]
  have hd' : d∈Icc 0 frameCap := by simpa [hpos] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := PositiveOrdinaryParameters.familyP_td hd' hx hz
  have hinc := nonnegative_T_lower hab (Or.inl rfl) (Or.inr rfl) hde heh hs hvar hd he
    hG (by intro h; norm_num at h) (fun _ => hT)
    (by simpa [hpos] using hp)
    (show (103/100 : ℝ)∈Icc (369/500) (103/100) by norm_num)
  rw [hpos] at hinc
  have hη : 0≤etaP d := by
    have hh := coefficient_bounds hd'
    linarith [hh.2.2.2.2.2.2.1]
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.positive_TD hab hde heh (by norm_num [k]) hη hs
    (show delta C.theta G∈Icc 0 frameCap from ⟨hG,(le_abs_self _).trans (hs G)⟩)
    (show delta C.theta T∈Icc 0 frameCap from ⟨hT,(le_abs_self _).trans (hs T)⟩)
    hflat hd he] at hnec
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd' hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := P_strict hd'
  dsimp [d,x,z] at *
  linarith

theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let x := delta C.theta G
  let z := delta C.theta B
  let d := x+z
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hb := budgets hab (Or.inr rfl) (Or.inl rfl) hde heh 0 0 0 0 0 hvar hd he
  have hpos : positiveRemoved C 3 0=d := by
    simp [positiveRemoved,d,x,z,positivePart,max_eq_left hG,max_eq_left hB]
  have hd' : d∈Icc 0 frameCap := by simpa [hpos] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := PositiveOrdinaryParameters.familyP_bt hd' hx hz
  have hinc := nonnegative_T_lower hab (Or.inr rfl) (Or.inl rfl) hde heh hs hvar hd he
    hG (fun _ => hB) (by intro h; norm_num at h)
    (by simpa [hpos] using hp)
    (show (103/100 : ℝ)∈Icc (369/500) (103/100) by norm_num)
  rw [hpos] at hinc
  have hη : 0≤etaP d := by
    have hh := coefficient_bounds hd'
    linarith [hh.2.2.2.2.2.2.1]
  have hnec := FlatEStress.necessary_at_cap hq hC hn false (weights_nonneg hp) hf
  rw [FlatEDecomposition.positive_BT hab hde heh (by norm_num [k]) hη hs
    (show delta C.theta G∈Icc 0 frameCap from ⟨hG,(le_abs_self _).trans (hs G)⟩)
    (show delta C.theta B∈Icc 0 frameCap from ⟨hB,(le_abs_self _).trans (hs B)⟩)
    hflat hd he] at hnec
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd' hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := P_strict hd'
  dsimp [d,x,z] at *
  linarith

theorem flat_negative_TD_false {C : SignedCycle} {q u : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (3/10))
    (hT : delta C.theta T= -u) (hTflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hc := NegativeOrdinaryParameters.familyTD hd' (Ioc_subset_Icc_self hu)
  have hk : 0≤k := by norm_num [k]
  have hw : 0≤tiltedWeight k (19/50) d ∧ 0≤k ∧ 0≤lN d ∧
      0≤cN d ∧ 0≤cN d/Real.cos u :=
    ⟨hk.trans hp.H_lower,hk,by linarith [hp.ell_lower],hk.trans hc.B_lower,hk.trans hc.D_lower⟩
  have hnec := FlatEStress.necessary_at_cap hq hC hn true hw hf
  rw [FlatEDecomposition.negative_TD hab hde heh hk (by norm_num : (0:ℝ)≤19/50)
    hs hd' hu' hT hTflat hflat hd he] at hnec
  have hinc := negative_TD_lower hab hde heh hs hvar hd he hG hu hT
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q u : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hu : u∈Ioc 0 (9/100))
    (hB : delta C.theta B= -u) (hTflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let d := delta C.theta G
  have hs (i : Vertex) : |delta C.theta i|≤frameCap := hC.spread (next i) i
  have hd' : d∈Icc 0 frameCap := ⟨hG,(le_abs_self _).trans (hs G)⟩
  have hu' : u∈Icc 0 frameCap := ⟨hu.1.le,by norm_num [frameCap]; linarith [hu.2]⟩
  have hp := PositiveOrdinaryParameters.familyN hd'
  have hc := NegativeOrdinaryParameters.familyBT hd' (Ioc_subset_Icc_self hu)
  have hk : 0≤k := by norm_num [k]
  have hw : 0≤tiltedWeight k (19/50) d ∧ 0≤k ∧ 0≤lN d ∧
      0≤cN d/Real.cos u ∧ 0≤cN d :=
    ⟨hk.trans hp.H_lower,hk,by linarith [hp.ell_lower],hk.trans hc.B_lower,hk.trans hc.D_lower⟩
  have hnec := FlatEStress.necessary_at_cap hq hC hn true hw hf
  rw [FlatEDecomposition.negative_BT hab hde heh hk (by norm_num : (0:ℝ)≤19/50)
    hs hd' hu' hB hTflat hflat hd he] at hnec
  have hinc := negative_BT_lower hab hde heh hs hvar hd he hG hu hB
  have hstrict := N_strict hd'
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d+_ at hstrict
  dsimp [d] at *
  linarith

end SquaresInCircles.Eight.FlatEExclusion
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FlatEPreprocess
open Candidate ActualCoreEBlocks FlatEExclusion
open NegativeSecondaryEExclusion (BT_contact TD_contact)
open CoreENegativeExclusion (reselect_TD reselect_BT)

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hTs : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hTs]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hent := NegativeTEntry.negative_TD_entry (hC.sorted B) (hC.sorted T) (hC.sorted D)
    (hC.contained B) hTb (hC.contained D) (hC.core T) (hC.core D)
    hq hn.D_nonpos hs hBT hTD
  rcases hent with hsecondary | ⟨hcoreT,hTflat,hyT,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hn hflat hd he hvar hab hde heh hG
      ⟨hs.1,hshort.le⟩ hTs hTflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG (reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hBs : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hBs]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hBs] using hh))
  obtain ⟨hcoreT,hTflat,hyT,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hn hflat hd he hvar hab hde heh hG
    ⟨hs.1,hshort.le⟩ hBs hTflat hf

theorem preprocessed_flat_E_false {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hflat : (C.point E).a=7/12) (hd : primaryDE C de≤0) (he : primaryEH C eh≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact secondary_T_false hq hC hn hflat hd he hvar hab hde heh hG hf
  · by_cases ht : 0≤delta C.theta T
    · exact positive_TD_false hq hC hn hflat hd he hvar hab hde heh hG ht hf
    · exact negative_TD_false hq hC hn hflat hd he hvar hab hde heh hG hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact positive_BT_false hq hC hn hflat hd he hvar hab hde heh hG hb hf
    · have hb' := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hn hflat hd he hvar hab hde heh hG hTb hb'
        (halign hb') hf

end SquaresInCircles.Eight.FlatEPreprocess
end
end
end
