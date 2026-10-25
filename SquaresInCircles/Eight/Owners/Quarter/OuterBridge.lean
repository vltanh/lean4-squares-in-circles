module

public import SquaresInCircles.Eight.Owners.Outer.AnchorBridge
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Zero.SourceOuter
public import SquaresInCircles.Eight.Words.Zero.SignedCharge

/-!
# Eight squares: every original quarter owner selects an outer endpoint

The four local zero/quarter placements cover the surviving original
word.  A low owner selects the positive outer target; a high owner
selects the negative outer source.  The conclusion is applied to each
original weak axis individually and is independent of any restriction
on the other quarter owners.
-/

section
/-!
## Whole-interval scalar estimates for a core low-quarter target

The primary estimate is multiplied by its positive cosine.  Its
resulting elementary scalar is concave on the complete frame interval,
so only its two intrinsic endpoints enter.  The secondary estimate is
one direct cubic Taylor bound on each sign of the original error.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

def kappa : ℝ := 49/50

def primaryScalar (x : ℝ) : ℝ :=
  (x+163/1000)*Real.cos x-kappa/12-kappa*(183/200)*Real.sin x

def primaryScalarD (x : ℝ) : ℝ :=
  (1033/10000)*Real.cos x-(x+163/1000)*Real.sin x

def primaryScalarDD (x : ℝ) : ℝ :=
  -(11033/10000)*Real.sin x-(x+163/1000)*Real.cos x

theorem primaryScalar_derivative (x : ℝ) :
    HasDerivAt primaryScalar (primaryScalarD x) x := by
  have h := ((((hasDerivAt_id x).add_const (163/1000)).mul (Real.hasDerivAt_cos x)).sub_const
    (kappa/12)).sub ((Real.hasDerivAt_sin x).const_mul (kappa*(183/200)))
  convert h using 1
  · funext y
    simp only [primaryScalar,Pi.sub_apply,Pi.mul_apply,id]
  · simp only [primaryScalarD,kappa,id]
    ring

theorem primaryScalar_second_derivative (x : ℝ) :
    HasDerivAt primaryScalarD (primaryScalarDD x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (1033/10000)).sub
    (((hasDerivAt_id x).add_const (163/1000)).mul (Real.hasDerivAt_sin x))
  convert h using 1
  · funext y
    simp only [primaryScalarD,Pi.sub_apply,Pi.mul_apply,id]
  · simp only [primaryScalarDD,id]
    ring

theorem primaryScalar_concave : ConcaveOn ℝ (Icc 0 frameCap) primaryScalar := by
  apply concave_of_deriv2 (fun x _ => primaryScalar_derivative x)
    (fun x _ => primaryScalar_second_derivative x)
  intro x hx
  have tr := transport_trig hx
  have hprod := mul_nonneg (show 0≤x+163/1000 by linarith [hx.1])
    (show 0≤Real.cos x by linarith [tr.1])
  dsimp [primaryScalarDD]
  linarith [tr.2.2.1]

theorem primaryScalar_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<primaryScalar x := by
  apply concave_gt_of_endpoints primaryScalar_concave hx
    (by norm_num [primaryScalar,kappa])
  have hs := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  norm_num at hs hc
  dsimp [primaryScalar,kappa,frameCap]
  linarith

theorem angle_cos_le_sin {x : ℝ} (hx : x∈Icc 0 frameCap) :
    x*Real.cos x≤Real.sin x := by
  have hd (z : ℝ) : HasDerivAt (fun z : ℝ => Real.sin z-z*Real.cos z) (z*Real.sin z) z := by
    have h := (Real.hasDerivAt_sin z).sub ((hasDerivAt_id z).mul (Real.hasDerivAt_cos z))
    convert h using 1
    · funext y
      simp only [Pi.sub_apply,Pi.mul_apply,id]
    · show z*Real.sin z=Real.cos z-(1*Real.cos z+z*-Real.sin z)
      ring
  have hm : MonotoneOn (fun z : ℝ => Real.sin z-z*Real.cos z) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (hd z).continuousAt.continuousWithinAt
    · exact fun z _ => hd z
    · intro z hz
      exact mul_nonneg hz.1.le (transport_trig (Ioo_subset_Icc_self hz)).2.2.1
  have hh := hm (by norm_num [frameCap]) hx hx.1
  norm_num at hh
  linarith

/-- The actual primary projection, with an arbitrary signed source
transverse coordinate, forces this same linear lower charge. -/
theorem core_primary_bound {a A y d : ℝ}
    (ha : a∈Icc (447/800:ℝ) (283/200)) (hA : A≤7/12)
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤A+a*Real.sin d+y*Real.cos d) :
    (327/1000:ℝ)<d+kappa*y := by
  have hc : 0<Real.cos d := by linarith [(signed_trig hd).1]
  have hprod : 0<(d+kappa*y-327/1000)*Real.cos d := by
    by_cases hp : 0≤d
    · have hd' : d∈Icc 0 frameCap := ⟨hp,(le_abs_self d).trans hd⟩
      have tr := transport_trig hd'
      have haSin := mul_le_mul_of_nonneg_right ha.2 tr.2.2.1
      have hs := primaryScalar_positive hd'
      dsimp [GlobalOuterAnchor.width] at hm
      rw [abs_of_nonneg tr.2.2.1] at hm
      dsimp [primaryScalar,kappa] at hs ⊢
      nlinarith only [hm,hA,haSin,hs]
    · have hd' : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
      have tr := transport_trig hd'
      have haSin := mul_le_mul_of_nonneg_right ha.1 tr.2.2.1
      have htan := angle_cos_le_sin hd'
      have hlow : 19/25<Real.cos (-d) := by linarith [tr.1]
      have hwidth : GlobalOuterAnchor.width d=(1+Real.cos (-d)+Real.sin (-d))/2 := by
        dsimp [GlobalOuterAnchor.width]
        rw [← Real.cos_neg d,← abs_neg (Real.sin d),← Real.sin_neg d,
          abs_of_nonneg tr.2.2.1]
      rw [hwidth] at hm
      have hsinneg : Real.sin d= -Real.sin (-d) := by simp
      rw [hsinneg,← Real.cos_neg d] at hm
      dsimp [kappa]
      rw [← Real.cos_neg d]
      nlinarith only [hm,hA,haSin,htan,hlow,tr.2.2.1]
  have hh := (mul_pos_iff_of_pos_right hc).1 hprod
  linarith

def secondaryScalar (d : ℝ) : ℝ := d-(kappa/12)*Real.cos d+
  (kappa/2)*|Real.sin d|-kappa*(14/25)*Real.sin d

theorem secondaryScalar_lower {d : ℝ} (hd : |d|≤frameCap) :
    -(3/20:ℝ)<secondaryScalar d := by
  by_cases hp : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hp,(le_abs_self d).trans hd⟩
    have tr := transport_trig hd'
    have hs := Real.sin_le hp
    dsimp [secondaryScalar,kappa]
    rw [abs_of_nonneg tr.2.2.1]
    nlinarith [Real.cos_le_one d]
  · have hx : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hs := Real.sin_ge_sub_cube hx.1
    have hc := Real.cos_le_one (-d)
    have h3 := pow_le_pow_left₀ hx.1 hx.2 3
    have hsin := (transport_trig hx).2.2.1
    dsimp [frameCap] at h3
    norm_num at h3
    have hid : secondaryScalar d= -(-d)-(kappa/12)*Real.cos (-d)+
        kappa*(53/50)*Real.sin (-d) := by
      dsimp [secondaryScalar]
      have hsinneg : Real.sin d= -Real.sin (-d) := by simp
      rw [← Real.cos_neg d,hsinneg]
      rw [abs_neg,abs_of_nonneg hsin]
      ring
    rw [hid]
    dsimp [kappa]
    nlinarith only [hs,hc,h3,hx.1]

theorem core_marker_upper (s : State) (hs : s.branch.type=0) :
    unsigned s<1/5+(27/25)*s.b ∧ s.b≤14/25 := by
  have ha := primary_lower s
  have hchart := FrameCoreArc.state_core_chart s hs
  have hb := (FrameCoreArc.core_bounds hchart).2.2.2
  have hb' : s.b≤14/25 := by linarith [CoreAngleEndpoint.diagonal_bounds.2]
  refine ⟨?_,hb'⟩
  cases hbr : s.branch <;> simp [hbr,Branch.type] at hs
  all_goals
    dsimp [unsigned]
    rw [hbr]
    dsimp [FramePair.label]
    nlinarith [s.b_nonneg]

theorem core_secondary_bound (t : State) {y d : ℝ}
    (hcore : t.branch.type=0) (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤y+t.a*Real.cos d+t.b*Real.sin d) :
    -(581/1250:ℝ)<d+kappa*y-unsigned t := by
  have hc : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  have ha := mul_le_mul_of_nonneg_right (core_bounds t hcore).1 hc
  have hmark := core_marker_upper t hcore
  have hcoef : 0≤(27/25:ℝ)+kappa*Real.sin d := by
    dsimp [kappa]
    linarith [Real.neg_one_le_sin d]
  have hprod := mul_le_mul_of_nonneg_left hmark.2 hcoef
  have hscalar := secondaryScalar_lower hd
  dsimp [secondaryScalar,GlobalOuterAnchor.width,kappa] at *
  nlinarith only [ha,hmark.1,hprod,hscalar,hm]

end SquaresInCircles.Eight.GlobalQuarterOuter
end
end
end

section
/-!
## The zero–low-quarter path does not end at a core state

The transverse coordinate of the intermediate state stays signed. If it is positive, the zero owner
is `0` and the circle of the intermediate supplies its charge; if it is nonpositive, both zero
owners give the same scalar charge (`zero_signed_charge`). Both low quarter owners then force a
two-edge charge above `19/10` at a putative core target (`core_target_path_charge`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor

/-- For both zero owners, with the sign implication of owner `2`,
`0 ≤ v + kappa (s.b - transverse c - 1)`, where the tangent of the intermediate stays signed. -/
theorem zero_signed_charge (s c : State) {v : ℝ}
    (hv : |v|≤frameCap) (hs : 0≤transverse s)
    (j : Fin 4) (hj : j=0 ∨ j=2) (haxis : s.Feasible c j v)
    (hcancel : j=2 → transverse c≤0) :
    0≤v+kappa*(s.b-transverse c-1) := by
  have hy := transverse_of_nonneg s hs
  have hsc := coordinates s
  have hcc := coordinates c
  by_cases hc : transverse c≤0
  · have hcy : transverse c= -c.b := transverse_nonpos_eq c hc
    have hproj : edgeWidth v≤ s.b+c.a*Real.sin v+c.b*Real.cos v ∨
        edgeWidth v≤ s.a*Real.sin v+s.b*Real.cos v+c.b := by
      rcases hj with rfl | rfl
      · left
        have hh : pairWidth v≤transverse s+c.a*Real.sin v-transverse c*Real.cos v := by
          simpa [State.Feasible,forwardMargin,transverse] using haxis
        simpa only [hy,hcy,edgeWidth,neg_mul,sub_neg_eq_add] using hh
      · right
        have hh : pairWidth v≤ s.a*Real.sin v+transverse s*Real.cos v-transverse c := by
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
    have hproj : GlobalOuterAnchor.width v≤ s.b+c.a*Real.sin v-c.b*Real.cos v := by
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
      dsimp [GlobalOuterAnchor.width] at hproj
      rw [abs_of_nonneg (transport_trig hv').2.2.1] at hproj
      linarith
    have hprod := mul_le_mul_of_nonneg_left hlocal (by norm_num [kappa] : 0≤kappa)
    rw [hcy]
    dsimp [kappa,ZeroSignedCharge.kappa] at *
    linarith

theorem low_zero_projection (c t : State) {d : ℝ}
    (hd : |d|≤frameCap) (ht : 0≤transverse t) :
    c.Feasible t 0 (Real.pi/2+d) ↔
      GlobalOuterAnchor.width d≤transverse c+t.a*Real.cos d+t.b*Real.sin d := by
  have hy := transverse_of_nonneg t ht
  simp only [State.Feasible,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  change sign t.positive*t.b=t.b at hy
  rw [hy]
  dsimp [GlobalOuterAnchor.width,transverse]
  constructor <;> intro hh <;> linarith

/-- A core target is excluded by its own marker formula: the two-edge charge exceeds `19/10`, for
both neighbouring weak axes and a signed intermediate. -/
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
    change GlobalOuterAnchor.width d≤t.a+c.a*Real.sin d+transverse c*Real.cos d at hm
    have hcc := coordinates c
    have hqCharge := core_primary_bound ⟨hcc.1.le,hcc.2.1.le⟩
      (core_bounds t hcore).1 hd hm
    have htarget := marker_lt_four_fifths t
    dsimp [kappa,k] at hzeroCharge hsource hqCharge
    linarith [Arithmetic.pi_hand_enclosure.1]

end SquaresInCircles.Eight.GlobalQuarterOuter
end
end
end

section
/-!
## The complementary radial anchors beside a zero edge

A low quarter after a zero edge has an outer target (`zero_low_outer`), and reflection of the
two-edge formulas gives an outer source for a high quarter before a zero edge (`high_zero_outer`);
the latter includes the anchor E in the all-high branch. Both results hold at every radius in
`[5/2, Q0]`, for each feasible weak axis.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open FramePair QuarterWordGeometry GlobalOuterAnchor GlobalQuarterSign

theorem ceiling_zero_low_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  have hspos := GlobalZeroLow.ceiling_zero_low_source_positive C F i hi hj j howner haxis
  have htpos := GlobalQuarterSign.ceiling_target_positive C F (next i) hj j howner haxis
  have hs : 0≤transverse (stateOf C i) := by
    have hh := (lt_div_iff₀ (C.a_pos i)).1 hspos
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
  have ht : 0≤transverse (stateOf C (next (next i))) := by
    have hh := (lt_div_iff₀ (C.a_pos (next (next i)))).1 htpos
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
  have hc : (stateOf C (next (next i))).branch.type=0 :=
    (branchOf_core_iff C (next (next i))).2 hcore
  obtain ⟨z,hz⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have hzero : (forwardAxis z).Feasible (C.square i) (C.square (next i)) := by
    simpa only [hz] using C.feasible i
  have hzeroOwner := GlobalZeroSign.secondary C (by norm_num [Q0]) F i hi z hzero
  have hcancel : z=2 → transverse (stateOf C (next i))≤0 := by
    intro hz2
    have hh := GlobalZeroSign.ceiling_target_negative C F i hi (by simpa only [hz2] using hzero)
    have hh' := (div_lt_iff₀ (C.a_pos (next i))).1 hh
    simpa only [transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh'.le
  have hphaseL : pairAngle C i=difference F i := by
    simpa [hi] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=Real.pi/2+difference F (next i) := by
    simpa [hj,add_comm] using pair_angle_increment C F hgap (next i)
  have hmZ := stateOf_feasible C i z hzero
  have hmQ := stateOf_feasible C (next i) j haxis
  rw [hphaseL] at hmZ
  rw [hphaseR] at hmQ
  have hcharge := core_target_path_charge (stateOf C i) (stateOf C (next i))
    (stateOf C (next (next i))) hc
    (by simpa only [frameCap] using (difference_small F i).le)
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    hs ht z j hzeroOwner howner hmZ hmQ hcancel
  have hreturn := GlobalZeroLow.two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=Real.pi/2+difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  linarith

/-- At `Q0`, a high quarter before a zero edge has an outer source; reflection preserves the error
and the marker charge, and carries the zero-sign implication with its owner. -/
theorem ceiling_high_zero_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  by_contra hcore
  let hgap : ∀k,19/25<angleGap C.beta k := boundary_gap_lower C le_rfl
  let s := stateOf C i
  let c := stateOf C (next i)
  let t := stateOf C (next (next i))
  have hsneg := GlobalQuarterSign.ceiling_source_negative C F i hi j howner haxis
  have htneg := GlobalZeroLow.ceiling_high_zero_target_negative C F i hi hj j howner haxis
  have hs : 0≤transverse s.flip := by
    have hh := (div_lt_iff₀ (C.a_pos i)).1 hsneg
    have hh' : transverse s≤0 := by
      simpa only [s,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr hh'
  have ht : 0≤transverse t.flip := by
    have hh := (div_lt_iff₀ (C.a_pos (next (next i)))).1 htneg
    have hh' : transverse t≤0 := by
      simpa only [t,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
    simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonneg.mpr hh'
  have hc : s.flip.branch.type=0 := (branchOf_core_iff C i).2 hcore
  have hphaseL : pairAngle C i=Real.pi/2+difference F i := by
    simpa [hi,add_comm] using pair_angle_increment C F hgap i
  have hphaseR : pairAngle C (next i)=difference F (next i) := by
    simpa [hj] using pair_angle_increment C F hgap (next i)
  have hmQ : s.Feasible c j (Real.pi/2+difference F i) := by
    have hh := stateOf_feasible C i j haxis
    simpa only [hphaseL] using hh
  obtain ⟨z,hz⟩ := boundary_forward_complete C le_rfl (next i)
    (C.selected (next i)) (C.feasible (next i))
  have hzero : (forwardAxis z).Feasible (C.square (next i)) (C.square (next (next i))) := by
    simpa only [hz] using C.feasible (next i)
  have hmZ : c.Feasible t z (difference F (next i)) := by
    have hh := stateOf_feasible C (next i) z hzero
    simpa only [hphaseR] using hh
  have hzeroClass := GlobalZeroSign.classify C (by norm_num [Q0]) F (next i) hj z hzero
  obtain ⟨z',hzOwner,hzAxis,hzCancel⟩ : ∃z' : Fin 4,(z'=0 ∨ z'=2) ∧
      t.flip.Feasible c.flip z' (difference F (next i)) ∧
      (z'=2 → transverse c.flip≤0) := by
    rcases hzeroClass with ⟨hz0,hcpos⟩ | ⟨hz2,_⟩
    · refine ⟨2,Or.inr rfl,?_,?_⟩
      · apply (State.target_secondary_reverse t.flip c.flip (difference F (next i))).2
        simpa [State.flip,hz0] using hmZ
      · intro _
        have hh := (lt_div_iff₀ (C.a_pos (next i))).1 hcpos
        have hh' : 0≤transverse c := by
          simpa only [c,transverse,stateOf,signOf_spec,zero_mul,mul_zero] using hh.le
        simpa only [transverse,State.flip,sign_not,neg_mul] using neg_nonpos.mpr hh'
    · refine ⟨0,Or.inl rfl,?_,by intro hh; norm_num at hh⟩
      apply (State.target_secondary_reverse c t (difference F (next i))).1
      simpa only [hz2] using hmZ
  obtain ⟨q,hqOwner,hqAxis⟩ : ∃q : Fin 4,(q=0 ∨ q=1) ∧
      c.flip.Feasible s.flip q (Real.pi/2+difference F i) := by
    rcases howner with rfl | rfl
    · exact ⟨0,Or.inl rfl,(State.target_secondary_reverse s c _).1 hmQ⟩
    · refine ⟨1,Or.inr rfl,?_⟩
      apply (State.target_primary_reverse c.flip s.flip _).2
      simpa [State.flip] using hmQ
  have hcharge := core_target_path_charge t.flip c.flip s.flip hc
    (by simpa only [frameCap] using (difference_small F (next i)).le)
    (by simpa only [frameCap] using (difference_small F i).le)
    ht hs z' q hzOwner hqOwner hzAxis hqAxis hzCancel
  have hreturn := GlobalZeroLow.two_edge_charge_lt C F hgap i
  have hphase₁ : phaseValue F hgap i=Real.pi/2+difference F i := by
    linarith [phase_gap C F hgap i,pairAngle_gap C i]
  have hphase₂ : phaseValue F hgap (next i)=difference F (next i) := by
    linarith [phase_gap C F hgap (next i),pairAngle_gap C (next i)]
  rw [hphase₁,hphase₂] at hreturn
  simp only [State.flip_label] at hcharge
  dsimp [s,t] at hcharge
  linarith

theorem zero_low_outer {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=0)
    (hj : integerQuarterIncrement F.quarter (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_zero_low_outer D G i hi hj j howner
    (hR.preserves_all_axes (next i) (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

theorem high_zero_outer {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (F : QuarterLift C)
    (i : Vertex) (hi : integerQuarterIncrement F.quarter i=1)
    (hj : integerQuarterIncrement F.quarter (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let G : QuarterLift D := FramePhysicalTransport.quarterPushforward F hR
  have hh := ceiling_high_zero_outer D G i hi hj j howner
    (hR.preserves_all_axes i (forwardAxis j) haxis)
  simpa only [hR.same_kind] using hh

end SquaresInCircles.Eight.GlobalQuarterOuter
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterOuter

open Candidate

theorem frame_zero_low_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_low_outer C hq G i hinc hinc' j howner haxis

theorem frame_high_zero_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact high_zero_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  by_cases hnext : word (next i)=0
  · exact GlobalOuterAnchor.frame_low_zero_outer F hq i hi hnext j howner haxis
  · have hiD : i=D := by fin_cases i <;> simp_all [word,next,D]
    subst i
    simpa [T,D,E,next] using frame_zero_low_outer F hq T
      (by norm_num [word,T]) (by norm_num [word,T,next]) j howner
      (by simpa [T,D,E,next] using haxis)

theorem frame_high_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  by_cases hiE : i=E
  · subst i
    exact frame_high_zero_outer F hq E (by norm_num [word,E])
      (by norm_num [word,E,next]) j howner haxis
  · have hcases : i=G ∨ i=B ∨ i=D := by
      fin_cases i <;> simp_all [word,G,B,D,E]
    rcases hcases with rfl | rfl | rfl
    · simpa [H,G,next] using GlobalOuterAnchor.frame_zero_high_outer F hq H
        (by norm_num [word,H]) (by norm_num [word,H,next]) j howner
        (by simpa [H,G,next] using haxis)
    · simpa [A,B,next] using GlobalOuterAnchor.frame_zero_high_outer F hq A
        (by norm_num [word,A]) (by norm_num [word,A,next]) j howner
        (by simpa [A,B,next] using haxis)
    · simpa [T,D,next] using GlobalOuterAnchor.frame_zero_high_outer F hq T
        (by norm_num [word,T]) (by norm_num [word,T,next]) j howner
        (by simpa [T,D,next] using haxis)

/-- Complete original sign/radial classification, without choosing an
owner on any other quarter edge. -/
theorem frame_classify {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ C.kind (next i)=.outer ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.kind i=.outer ∧ C.tangent i<0) := by
  rcases GlobalQuarterSign.of_frame F hq i hi j haxis with ⟨hj,hs⟩ | ⟨hj,hs⟩
  · exact Or.inl ⟨hj,frame_low_outer F hq i hi j hj haxis,hs⟩
  · exact Or.inr ⟨hj,frame_high_outer F hq i hi j hj haxis,hs⟩

theorem frame_high_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer ∧ C.tangent i<0 := by
  rcases frame_classify F hq i hi j haxis with ⟨hbad,_⟩ | ⟨_,hh⟩
  · rcases hj with rfl | rfl <;> rcases hbad with hbad | hbad <;> norm_num at hbad
  · exact hh

end SquaresInCircles.Eight.GlobalQuarterOuter
end
end
end
