module

public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Owners.RelaxedSameBlock

/-!
# Eight squares: signed middle width for the small fixed stress

The weight lies in `[7/12,3/5]`.  Both original frame differences retain
their signs, including cancellation and a middle frame outside the other
two frames.  Only their three actual absolute difference bounds are used.

For a nonnegative total, the existing whole-interval positive surplus
applies.  For a negative total, concavity first leaves the zero-positive
and saturated-positive endpoints.  The saturated endpoint is a positive
first harmonic; its two endpoint reserves are rational consequences of
the already proved sine and cosine bounds at `7/10`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleOrderWidth
open PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open CorrelatedSameBlock

def width (l s : ℝ) : ℝ :=
  if 0≤ s then l*(PositiveAngularEnvelope.phi s-1) else 1-PositiveAngularEnvelope.phi (-s)

@[simp] theorem width_zero (l : ℝ) : width l 0=0 := by
  simp [width]

theorem width_of_nonneg {l s : ℝ} (hs : 0≤ s) :
    width l s=l*(PositiveAngularEnvelope.phi s-1) := by
  simp only [width,hs,↓reduceIte]

theorem width_of_nonpos {l s : ℝ} (hs : s≤0) :
    width l s=1-PositiveAngularEnvelope.phi (-s) := by
  by_cases hz : s=0
  · subst s
    simp
  · have hn : ¬0 ≤ s := not_le.mpr (lt_of_le_of_ne hs hz)
    simp only [width,hn,↓reduceIte]

theorem negative_endpoint_reserves {l : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5)) :
    0<l*(PositiveAngularEnvelope.phi frameCap-1)+Real.cos frameCap-1 ∧
    0<Real.cos frameCap+PositiveAngularEnvelope.phi frameCap-2 := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hphi := phi_cap_lower
  have hc := (transport_trig hh).1
  have hm := mul_nonneg (sub_nonneg.mpr hl.1)
    (sub_nonneg.mpr (one_le_phi hh))
  constructor
  · nlinarith
  · linarith

/-- With no positive part, the requested negative width is below the
ordinary cosine loss throughout the entire frame interval. -/
theorem negative_pure {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-PositiveAngularEnvelope.phi z≤Real.cos z-1 := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) (harmonic 2 1) := by
    apply harmonic_concave
    intro t ht
    obtain ⟨hc,_,hs,_,_⟩ := transport_trig ht
    linarith
  have hend : (2:ℝ)≤harmonic 2 1 frameCap := by
    have hphi := phi_cap_lower
    have hc := (transport_trig hh).1
    dsimp [harmonic,PositiveAngularEnvelope.phi] at *
    linarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hh hz
  have hzero : harmonic 2 1 0=2 := by norm_num [harmonic]
  rw [hzero,min_eq_left hend] at hmin
  dsimp [harmonic,PositiveAngularEnvelope.phi] at hmin ⊢
  linarith

/-- At the saturated positive endpoint, the remaining expression is a
first harmonic with nonnegative coefficients and positive endpoint
reserves.  The argument includes both zero and maximal total deficit. -/
theorem negative_saturated {l z : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (hz : z∈Icc 0 frameCap) :
    1-PositiveAngularEnvelope.phi z≤l*(PositiveAngularEnvelope.phi (frameCap-z)-1)+(Real.cos frameCap-1) := by
  let a : ℝ := l*PositiveAngularEnvelope.phi frameCap+1
  let b : ℝ := 1+l*(Real.sin frameCap-Real.cos frameCap)
  let k : ℝ := Real.cos frameCap-l-2
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hl0 : 0≤l := by linarith [hl.1]
  have ha : 0≤a := by
    have hm := mul_nonneg hl0 (show 0≤PositiveAngularEnvelope.phi frameCap by linarith [phi_cap_lower])
    dsimp [a]
    linarith
  have hb : 0≤b := by
    have hmS := mul_nonneg hl0 (transport_trig hh).2.2.1
    have hmC := mul_le_mul_of_nonneg_left (Real.cos_le_one frameCap) hl0
    dsimp [b]
    nlinarith [hl.2]
  have he (t : ℝ) :
      l*(PositiveAngularEnvelope.phi (frameCap-t)-1)+Real.cos frameCap+PositiveAngularEnvelope.phi t-2=
        k+a*Real.cos t+b*Real.sin t := by
    dsimp [a,b,k,PositiveAngularEnvelope.phi]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  obtain ⟨hleft0,hright0⟩ := negative_endpoint_reserves hl
  have hleft : 0<k+a*Real.cos 0+b*Real.sin 0 := by
    rw [← he 0]
    simp only [sub_zero,phi_zero]
    linarith
  have hright : 0<k+a*Real.cos frameCap+b*Real.sin frameCap := by
    rw [← he frameCap]
    simp only [sub_self,phi_zero,mul_zero,zero_add]
    linarith
  have hpos := harmonic_pos_of_endpoints ha hb (by norm_num : (0:ℝ)≤0)
    (show frameCap≤Real.pi/2 by dsimp [frameCap]; linarith [Real.pi_gt_three])
    hz hleft hright
  rw [← he z] at hpos
  linarith

/-- Concavity in the canceling positive part gives the negative-width
bound between the pure and saturated endpoints. -/
theorem negative_mixed {l P N : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) :
    1-PositiveAngularEnvelope.phi (N-P)≤l*(PositiveAngularEnvelope.phi P-1)+(Real.cos N-1) := by
  let z : ℝ := N-P
  have hz : z∈Icc 0 frameCap := by
    dsimp [z]
    constructor <;> linarith
  have hPz : P∈Icc 0 (frameCap-z) := by
    dsimp [z]
    exact ⟨hP,by linarith⟩
  have hconc := sameBlockLine_concave (R := 0) (p := l) (q := 1)
    (by linarith [hl.1] : 0≤l) (by norm_num : (0:ℝ)≤1) hz
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (frameCap-z) from ⟨le_rfl,by linarith [hz.2]⟩)
    (show frameCap-z∈Icc 0 (frameCap-z) from ⟨by linarith [hz.2],le_rfl⟩) hPz
  have hleft : 1-PositiveAngularEnvelope.phi z≤ mixedBlock 0 l 1 0 (z+0) := by
    simpa [mixedBlock] using negative_pure hz
  have hright : 1-PositiveAngularEnvelope.phi z≤
      mixedBlock 0 l 1 (frameCap-z) (z+(frameCap-z)) := by
    simpa only [mixedBlock,zero_mul,sub_zero,one_mul,
      show z+(frameCap-z)=frameCap by ring] using negative_saturated hl hz
  have hresult := (le_min hleft hright).trans hmin
  simpa only [mixedBlock,zero_mul,sub_zero,one_mul,
    show z+P=N by dsimp [z]; ring] using hresult

/-- The three pairwise frame bounds control both sign totals, even when
the two original angles have opposite signs. -/
theorem signed_parts_bounds {d v : ℝ} (hd : |d|≤frameCap)
    (hv : |v|≤frameCap) (hs : |d+v|≤frameCap) :
    positivePart d+positivePart v≤frameCap ∧
    negativePart d+negativePart v≤frameCap := by
  obtain ⟨hdL,hdU⟩ := abs_le.mp hd
  obtain ⟨hvL,hvU⟩ := abs_le.mp hv
  obtain ⟨hsL,hsU⟩ := abs_le.mp hs
  have hh : (0:ℝ)≤frameCap := by norm_num [frameCap]
  constructor <;> simp only [positivePart,negativePart,max_def] <;>
    split_ifs <;> linarith

/-- Exact signed middle-width compression at the fixed small weight.
No intermediate frame order, sign convention, or strict-owner choice
is needed. -/
theorem signed_width {l d v : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap) :
    width l (d+v)≤l*psi d+psi v := by
  let X : Block := ⟨l,1,d,v⟩
  have hl0 : 0≤l := by linarith [hl.1]
  have hl1 : l≤1 := by linarith [hl.2]
  have hp : X.p=l := by simp [X,Block.p,min_eq_left hl1]
  have hq : X.q=1 := by simp [X,Block.q,max_eq_right hl1]
  obtain ⟨hP,hN⟩ := signed_parts_bounds hd hv hs
  have hXP : X.P≤frameCap := hP
  have hXN : X.N≤frameCap := hN
  have hminor := X.minorant 0 (by rw [hp]; exact hl0) hXP hXN
  rw [hp,hq] at hminor
  have hminor' : l*(PositiveAngularEnvelope.phi X.P-1)+(Real.cos X.N-1)≤l*psi d+psi v := by
    simpa only [mixedBlock,Block.increment,zero_mul,sub_zero,one_mul,X] using hminor
  have htotal : X.P-X.N=d+v := X.signed_total
  by_cases hs0 : 0≤d+v
  · have hPN : X.N≤X.P := by linarith
    have hsur := RelaxedSameBlock.positive_surplus (R := 0) (p := l) (q := 1)
      (by norm_num : (0:ℝ)≤1) (by linarith [hl.1] : (29/50:ℝ)*1≤l)
      ⟨X.P_nonneg,hXP⟩ ⟨X.N_nonneg,hPN⟩
    simp only [U,mixedBlock,zero_mul,sub_zero,one_mul] at hsur
    rw [htotal] at hsur
    rw [width_of_nonneg hs0]
    exact hsur.trans hminor'
  · have hPN : X.P≤X.N := by linarith
    have hsur := negative_mixed hl X.P_nonneg hPN hXN
    have he : X.N-X.P= -(d+v) := by linarith
    rw [he] at hsur
    rw [width_of_nonpos (le_of_lt (not_le.mp hs0))]
    exact hsur.trans hminor'

end SquaresInCircles.Eight.MiddleOrderWidth
