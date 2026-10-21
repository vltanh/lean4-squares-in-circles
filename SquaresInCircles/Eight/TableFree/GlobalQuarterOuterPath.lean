module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterOuterScalar
public import SquaresInCircles.Eight.TableFree.GlobalZeroLowBridge

/-!
# The original zero--low-quarter path cannot end at a core state

The intermediate transverse coordinate remains signed.  If it is
positive, the original zero owner is 0 and the actual intermediate
circle supplies its charge.  If it is nonpositive, both original zero
owners have the same scalar charge.  Both original low quarter owners
then force a two-edge charge above `19/10` at a putative core target.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalQuarterOuter

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

/-- Both zero owners, with only their actual target-sign implication.
The intermediate signed tangent is retained in the conclusion. -/
theorem zero_signed_charge (s c : State) {v : ℝ}
    (hv : |v|≤frameCap) (hs : 0≤transverse s)
    (j : Fin 4) (hj : j=0 ∨ j=2) (haxis : s.Feasible c j v)
    (hcancel : j=2 → transverse c≤0) :
    0≤v+kappa*(s.b-transverse c-1) := by
  have hy := transverse_of_nonneg s hs
  have hsc := coordinates s
  have hcc := coordinates c
  by_cases hc : transverse c≤0
  · have hcy := transverse_nonpos_eq c hc
    have hproj : edgeWidth v≤s.b+c.a*Real.sin v+c.b*Real.cos v ∨
        edgeWidth v≤s.a*Real.sin v+s.b*Real.cos v+c.b := by
      rcases hj with rfl | rfl
      · left
        have hh : pairWidth v≤transverse s+c.a*Real.sin v-transverse c*Real.cos v := by
          simpa [State.Feasible,forwardMargin,transverse] using haxis
        simpa only [hy,hcy,edgeWidth,neg_mul,sub_neg_eq_add] using hh
      · right
        have hh : pairWidth v≤s.a*Real.sin v+transverse s*Real.cos v-transverse c := by
          simpa [State.Feasible,forwardMargin,transverse] using haxis
        simpa only [hy,hcy,edgeWidth,sub_neg_eq_add] using hh
    have hh := ZeroSignedCharge.nonnegative_zero
      ⟨hsc.1.le,hsc.2.1.le⟩ ⟨hcc.1.le,hcc.2.1.le⟩
      ⟨s.b_nonneg,hsc.2.2.2.2.le⟩ ⟨c.b_nonneg,hcc.2.2.2.2.le⟩ hv hproj
    simpa only [kappa,ZeroSignedCharge.kappa,hcy,sub_neg_eq_add] using hh
  · have hcpos : 0<transverse c := lt_of_not_ge hc
    have howner : j=0 := by
      rcases hj with hj | hj
      · exact hj
      · exact (hc (hcancel hj)).elim
    have hcy := transverse_of_nonneg c hcpos.le
    have hproj : width v≤s.b+c.a*Real.sin v-c.b*Real.cos v := by
      have hh : pairWidth v≤transverse s+c.a*Real.sin v-transverse c*Real.cos v := by
        simpa [State.Feasible,forwardMargin,transverse,howner] using haxis
      rw [hy,hcy,CommonQuarter.signed_width (by simpa only [frameCap] using hv)] at hh
      exact hh
    have hvpos : 0≤v := by
      by_contra! hn
      have hcos : 0≤Real.cos v := by linarith [(signed_trig hv).1]
      have hsin := sine_nonpos hv hn.le
      have h1 := mul_nonpos_of_nonneg_of_nonpos c.a_pos.le hsin
      have h2 := mul_nonneg c.b_nonneg hcos
      linarith [width_ge_one hv]
    have hv' : v∈Icc 0 frameCap := ⟨hvpos,(le_abs_self v).trans hv⟩
    have hcircle : (c.a+1/2)^2+(c.b+1/2)^2≤qCap := by
      simpa only [qCap,Q0] using state_circle c
    have hsupp := EndpointECharge.circle_chord_support hcircle hv'
    have hscalar := ZeroSignedCharge.chord_scalar hv'
    have hlocal : 1-s.b+c.b≤2*EndpointRotationPenalty.R*Real.sin (v/2)-Real.sin v := by
      dsimp [width] at hproj
      rw [abs_of_nonneg (transport_trig hv').2.2.1] at hproj
      linarith
    have hprod := mul_le_mul_of_nonneg_left hlocal (by norm_num [kappa] : 0≤kappa)
    rw [hcy]
    dsimp [kappa,ZeroSignedCharge.kappa] at *
    linarith

theorem low_zero_projection (c t : State) {d : ℝ}
    (hd : |d|≤frameCap) (ht : 0≤transverse t) :
    c.Feasible t 0 (Real.pi/2+d) ↔
      width d≤transverse c+t.a*Real.cos d+t.b*Real.sin d := by
  have hy := transverse_of_nonneg t ht
  simp only [State.Feasible,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,zero_add,sub_zero,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  change sign t.positive*t.b=t.b at hy
  rw [hy]
  dsimp [width,transverse]
  constructor <;> intro hh <;> linarith

/-- The original core target is excluded by its own marker formula;
both neighboring weak axes and the signed intermediate are preserved. -/
theorem core_target_path_charge (s c t : State) {v d : ℝ}
    (hcore : t.branch.type=0) (hv : |v|≤frameCap) (hd : |d|≤frameCap)
    (hs : 0≤transverse s) (ht : 0≤transverse t)
    (jZ jQ : Fin 4) (hZowner : jZ=0 ∨ jZ=2) (hQowner : jQ=0 ∨ jQ=1)
    (hzero : s.Feasible c jZ v) (hquarter : c.Feasible t jQ (Real.pi/2+d))
    (hcancel : jZ=2 → transverse c≤0) :
    (19/10:ℝ)<Real.pi/2+v+d+s.signedLabel-t.signedLabel := by
  have hzeroCharge := zero_signed_charge s c hv hs jZ hZowner hzero hcancel
  have hsource := GlobalOuterAnchor.marker_lower s
  have hsourceBound := (coordinates s).2.2.2.2
  rw [signed_of_nonneg s hs,signed_of_nonneg t ht]
  rcases hQowner with rfl | rfl
  · have hm := (low_zero_projection c t hd ht).1 hquarter
    have hqCharge := core_secondary_bound t hcore hd hm
    dsimp [kappa,k] at hzeroCharge hsource hqCharge
    linarith [Arithmetic.pi_hand_enclosure.1]
  · have hm := (quarter_one_margin c t hd).1 hquarter
    change width d≤t.a+c.a*Real.sin d+transverse c*Real.cos d at hm
    have hcc := coordinates c
    have hqCharge := core_primary_bound ⟨hcc.1.le,hcc.2.1.le⟩
      (core_bounds t hcore).1 hd hm
    have htarget := marker_lt_four_fifths t
    dsimp [kappa,k] at hzeroCharge hsource hqCharge
    linarith [Arithmetic.pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.GlobalQuarterOuter
