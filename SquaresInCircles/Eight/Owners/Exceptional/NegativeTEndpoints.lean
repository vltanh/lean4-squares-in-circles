module

public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTEnvelope
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTSortedGain
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTTaylor

/-!
# Eight squares: intrinsic secant endpoints and continuous continuation

The zero endpoint is the existing TD0 outside-strip
scalar. The other endpoint is one of the forty-four exact constructions.
Concavity of a linear gain plus the canonical negative charge covers the
whole intervening secant interval. The later positive-net interval uses
the actual J derivative or the BT linear gain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ExceptionalNegativeTEndpoints
open Candidate ExceptionalECoefficients ExceptionalContactStress
open ExceptionalEBalanced (endpointX endpointE endpoints_mem)
open ExceptionalNegativeTOrdinaryData ExceptionalNegativeTEnvelope
open ExceptionalNegativeTSortedGain
open CriticalNegativeTOrdinaryData (shortDomain short_small)
open PositiveAngularEnvelope OrdinaryAngleConcavity SingleAngleConcavity

def base (b : Band) (R t : ℝ) (face : Bool) : ℝ :=
  if face then ExceptionalContactSupport.atG R (k b t) (ell b t) (c b t) (eta b t) t
  else ExceptionalContactSupport.atE R (k b t) (ell b t) (c b t) (eta b t) t
def cap (td : Bool) : ℝ := if td then 3/10 else 9/100
def removed (td : Bool) (t : ℝ) : ℝ := min t (cap td)
def slope (td : Bool) (t : ℝ) : ℝ := if td then ExceptionalNegativeTScalarModel.g (removed td t) else 21/20

def endpointRow (b : Band) (td : Bool) (t : ℝ) (i : Fin 3) : ExceptionalNegativeTScalarModel.Row :=
  if td then
    match b with
    | .low => if t≤1/10 then .tdLowZero else .tdLowReturn
    | .middle => if t≤3/10 then .tdMiddleDiagonal else .tdMiddle i
    | .high => .tdHigh i
  else
    match b with
    | .low => if t≤9/100 then .btLowDiagonal else if t≤1/10 then .btLowZero i else .btLowReturn i
    | .middle => .btMiddle i
    | .high => .btHigh i

theorem endpointRow_data {b : Band} (td : Bool) {t : ℝ} (i : Fin 3)
    (ht : t∈domain b) (hout : t≤1/10 ∨ 4/25≤t) :
    ExceptionalNegativeTScalarModel.band (endpointRow b td t i)=b ∧
      ExceptionalNegativeTScalarModel.isTD (endpointRow b td t i)=td ∧
      t∈ExceptionalNegativeTScalarModel.domain (endpointRow b td t i) ∧
      (ExceptionalNegativeTScalarModel.diagonal (endpointRow b td t i)=true ∨
        ExceptionalNegativeTScalarModel.index (endpointRow b td t i)=i) := by
  cases td <;> cases b <;> simp only [endpointRow,Bool.false_eq_true,↓reduceIte] <;>
    (try split_ifs) <;>
    refine ⟨rfl,rfl,?_,by first | exact Or.inl rfl | exact Or.inr rfl⟩ <;>
    simp only [domain,frameCap,mem_Icc] at ht <;>
    simp only [ExceptionalNegativeTScalarModel.domain,ExceptionalNegativeTScalarModel.origin,
      ExceptionalNegativeTScalarModel.length,mem_Icc] <;>
    push_cast <;> rcases hout with hout | hout <;> constructor <;> linarith

theorem endpointRow_parameters {b : Band} (td : Bool) {t : ℝ} (i : Fin 3)
    (ht : t∈domain b) (hout : t≤1/10 ∨ 4/25≤t) :
    ExceptionalNegativeTScalarModel.removed (endpointRow b td t i) t=removed td t ∧
      ExceptionalNegativeTScalarModel.slope (endpointRow b td t i) t=slope td t ∧
      ExceptionalNegativeTScalarModel.correction (endpointRow b td t i) t=correction b td t := by
  have h := endpointRow_data td i ht hout
  have ha := (ExceptionalNegativeTScalarModel.angles h.2.2.1).2.2.2
  have hcap : (ExceptionalNegativeTScalarModel.cap (endpointRow b td t i):ℝ)=cap td := by
    rw [ExceptionalNegativeTScalarModel.cap,h.2.1]
    cases td <;> norm_num [cap]
  rw [hcap] at ha
  refine ⟨ha,?_,?_⟩
  · simp [ExceptionalNegativeTScalarModel.slope,slope,h.2.1,ha,removed]
  · simp [ExceptionalNegativeTScalarModel.correction,correction,h.1,h.2.1]

theorem H_nu_upper (face : Bool) {b : Band} {t : ℝ} (ht : t∈domain b) :
    canonicalNu b t face 0≤53/50 := by
  obtain ⟨hx,he⟩ := endpoints_mem face (angle ht).1
  have hk := (ranges ht).1
  have hx0 := tilt_pos ht hx
  have he0 := tilt_pos ht he
  have hxU : tilt (eta b t) (endpointX face t)≤53/50 := by
    by_cases hb : b=.low
    · subst b; linarith [(low_tilt ht hx).2]
    · exact (balanced_tilt hb ht hx).2.le
  have heU : tilt (eta b t) (endpointE face t)≤53/50 := by
    by_cases hb : b=.low
    · subst b; linarith [(low_tilt ht he).2]
    · exact (balanced_tilt hb ht he).2.le
  have hmul := mul_le_mul_of_nonneg_right hk.2 hx0.le
  change max (tilt (eta b t) (endpointE face t)) (k b t*tilt (eta b t) (endpointX face t))≤53/50
  exact max_le heU (by linarith)

theorem charge_le_canonical (s : ExceptionalNegativeTScalarModel.Case) {R t v : ℝ}
    (ht : t∈domain (ExceptionalNegativeTScalarModel.band s.row)) (i : Fin 3) :
    ExceptionalNegativeTScalarModel.charge s R t v i≤
      canonical (ExceptionalNegativeTScalarModel.band s.row) R t s.atG i v := by
  let b := ExceptionalNegativeTScalarModel.band s.row
  have hNu : canonicalNu b t s.atG i≤ExceptionalNegativeTScalarModel.nu s.row t i := by
    fin_cases i
    · exact H_nu_upper s.atG ht
    · rfl
    · rfl
  have hm := mul_le_mul_of_nonpos_right hNu (show Real.cos v-1≤0 by linarith [Real.cos_le_one v])
  have hnorm (d : ℝ) :
      pairNorm (canonicalP b t s.atG i) (canonicalQ b t s.atG i) d=
        pairNorm (ExceptionalNegativeTScalarModel.first s t (Real.sin t) (Real.cos t) ⟨i.val,by omega⟩)
          (ExceptionalNegativeTScalarModel.second s t (Real.sin t) (Real.cos t) ⟨i.val,by omega⟩) d := by
    simp only [canonicalP,canonicalQ,p,q,CriticalNegativeTOrdinaryData.small,
      CriticalNegativeTOrdinaryData.large]
    rw [ExceptionalEBalanced.norm_sorted]
    fin_cases i <;> cases h : s.atG <;>
      simp [CriticalNegativeTOrdinaryData.alpha,
        CriticalNegativeTOrdinaryData.beta,CriticalNegativeTOrdinaryData.bWeight,
        ExceptionalNegativeTScalarModel.first,ExceptionalNegativeTScalarModel.second,
        endpointX,endpointE,h,ExceptionalContactStress.tilt,pairNorm_symm,b]
  dsimp [ExceptionalNegativeTScalarModel.charge,canonical,Vnu]
  rw [hnorm (-v),hnorm 0]
  linarith

theorem far_endpoint (face td : Bool) {b : Band} {R t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hout : t≤1/10 ∨ 4/25≤t) (i : Fin 3) :
    0<base b R t face+correction b td t+c b t*slope td t*removed td t+
      canonical b R t face i (t-removed td t) := by
  let r := endpointRow b td t i
  let s : ExceptionalNegativeTScalarModel.Case := ⟨r,face⟩
  have hd := endpointRow_data td i ht hout
  have hp := endpointRow_parameters td i ht hout
  have hc := ExceptionalNegativeTTaylor.endpoint_positive s hd.2.2.1 hR hQU
  have hbase : ExceptionalNegativeTScalarModel.baseline s R t=base b R t face := by
    simp [s,r,ExceptionalNegativeTScalarModel.baseline,base,hd.1]
  have hcharge : ExceptionalNegativeTScalarModel.charge s R t
      (ExceptionalNegativeTScalarModel.angle r t) (ExceptionalNegativeTScalarModel.index r)≤
        canonical b R t face i (t-removed td t) := by
    rcases hd.2.2.2 with hdiag | hi
    · have hz : ExceptionalNegativeTScalarModel.angle r t=0 := by
        simp [ExceptionalNegativeTScalarModel.angle,ExceptionalNegativeTScalarModel.removed,r,hdiag]
      have hzero : t-removed td t=0 := by
        rw [← hp.1]
        simpa [ExceptionalNegativeTScalarModel.angle] using hz
      simp [hz,hzero,ExceptionalNegativeTScalarModel.charge,canonical_zero,Vnu]
    · rw [hi]
      have hh := charge_le_canonical s (R := R) (v := ExceptionalNegativeTScalarModel.angle r t)
        (by simpa [s,r,hd.1] using ht) i
      simpa [s,r,ExceptionalNegativeTScalarModel.angle,hp.1,hd.1] using hh
  rw [hbase] at hc
  simp only [s,r,hp.1,hp.2.1,hp.2.2,hd.1] at hc
  linarith

theorem canonical_eq_pure (face : Bool) {b : Band} {R t v : ℝ} (ht : t∈domain b) (i : Fin 3) :
    canonical b R t face i v=
      pure (ExceptionalContactBlocks.single ⟨i.val,by omega⟩) R
        (ExceptionalContactBlocks.small (k b t) (ell b t) (c b t) (eta b t)
          (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩)
        (ExceptionalContactBlocks.large (k b t) (ell b t) (c b t) (eta b t)
          (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩)
        (ExceptionalContactBlocks.nu (k b t) (ell b t) (c b t) (eta b t)
          (endpointX face t) (endpointE face t) ⟨i.val,by omega⟩) v := by
  rw [canonical,(old_coefficients face b t i).1,(old_coefficients face b t i).2.1,
    (old_coefficients face b t i).2.2]
  have hlc := (coefficient_order ht).2.2.1
  fin_cases i
  · rfl
  · rfl
  · simp only [ExceptionalContactBlocks.single,SingleAngleConcavity.pure,ExceptionalContactBlocks.nu,
      ExceptionalContactBlocks.large,ExceptionalContactBlocks.alpha,ExceptionalContactBlocks.beta]
    simp [max_eq_right hlc,Vnu,V]

theorem zero_endpoint (face td : Bool) {b : Band} {R t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hout : t≤1/10 ∨ 4/25≤t) (i : Fin 3) :
    0<base b R t face+correction b td t+canonical b R t face i t := by
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hcorr : 0≤correction b td t := by unfold correction; split_ifs <;> positivity
  obtain ⟨hx,he⟩ := endpoints_mem face (angle ht).1
  by_cases hb : b=.low
  · subst b
    have hout' : t∈ExceptionalELowExclusion.intervals := by
      rcases hout with hout | hout
      · exact Or.inl ⟨ht.1,hout⟩
      · exact Or.inr ⟨hout,ht.2⟩
    have hend := ExceptionalELowExclusion.scalar_endpoints hR hQL hQU hout'
    have hdom := (ExceptionalELowEnvelope.pure_dominates hR hQL hcap ht hx he ⟨i.val,by omega⟩).1
    rw [← canonical_eq_pure face ht i] at hdom
    cases face <;> simp only [base,ite_true,ite_false,Bool.false_eq_true] <;> linarith [hend.1,hend.2]
  · have hend := ExceptionalEBalanced.scalar_endpoints hb ht hR hQU
    have hmin := SoleBalancedEnvelope.minimumFour_le (ExceptionalEScalarData.charge R b t) ⟨i.val,by omega⟩
    have hdom := ExceptionalEBalanced.charge_le_pure (R := R) face hb ht ⟨i.val,by omega⟩
    rw [← canonical_eq_pure face ht i] at hdom
    cases face <;> simp only [base,ite_true,ite_false,Bool.false_eq_true] <;> linarith [hend.1,hend.2]

theorem removed_bounds (td : Bool) {b : Band} {t : ℝ} (ht : t∈domain b) :
    removed td t∈Icc 0 (cap td) ∧ removed td t≤t ∧ cap td≤frameCap := by
  have hc : 0≤cap td ∧ cap td≤frameCap := by cases td <;> norm_num [cap,frameCap]
  exact ⟨⟨le_min (angle ht).1 hc.1,min_le_right _ _⟩,min_le_left _ _,hc.2⟩

theorem negative_net (face td : Bool) {b : Band} {R t s : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hout : t≤1/10 ∨ 4/25≤t) (hs : s∈shortDomain td) (hst : s≤t) :
    0<base b R t face+correction b td t+lowerGain b td t s+
      minimumThree (fun i => canonical b R t face i (t-s)) := by
  have hr := removed_bounds td ht
  have hs' : s∈Icc 0 (removed td t) :=
    ⟨(short_small hs).1,le_min hst (by cases td <;> simpa [shortDomain,cap] using hs.2)⟩
  have hcap := hQU.trans uniform_radius_order.2.2.1.le
  have hlinear : c b t*slope td t*s≤lowerGain b td t s := by
    cases td
    · simp only [slope,lowerGain,Bool.false_eq_true,↓reduceIte]
      exact le_of_eq (by ring)
    · have ha : removed true t∈Icc 0 (3/10:ℝ) := by simpa [cap] using hr.1
      have hh := mul_le_mul_of_nonneg_left (J_linear ha hs') (ranges ht).2.2.2.1.le
      simpa [slope,lowerGain,mul_assoc,mul_left_comm,mul_comm] using hh
  have hpos (i : Fin 3) : 0<base b R t face+correction b td t+c b t*slope td t*s+
      canonical b R t face i (t-s) := by
    have hc := concave_affine_argument (canonical_concave face hR hcap ht i)
      (a := -1) (b := t) (l := 0) (u := removed td t)
      (fun v hv => by constructor <;> linarith [hv.1,hv.2,hr.2.1,(angle ht).2])
    have hl : ConcaveOn ℝ (Icc 0 (removed td t)) (fun v : ℝ => c b t*slope td t*v) := by
      refine ⟨convex_Icc _ _,?_⟩
      intro x hx y hy a d ha hd had
      simp only [smul_eq_mul]
      ring_nf
      exact le_rfl
    have hconc := (hl.add hc).add_const (base b R t face+correction b td t)
    have hleft := zero_endpoint face td hR hQL hQU ht hout i
    have hright := far_endpoint face td hR hQU ht hout i
    have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hr.1.1)
      (right_mem_Icc.mpr hr.1.1) hs'
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,mul_zero,sub_zero,zero_add] at hmin
    rcases min_le_iff.mp hmin with h | h <;> linarith
  have hm := lt_minimumThree (fun i => by linarith [hpos i] : ∀i,
      -(base b R t face+correction b td t+c b t*slope td t*s)<canonical b R t face i (t-s))
  linarith

theorem positive_net (face td : Bool) {b : Band} {R t s : ℝ}
    (hR : 0≤R) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hout : t≤1/10 ∨ 4/25≤t) (hs : s∈shortDomain td) (hts : t≤ s) :
    0<base b R t face+correction b td t+lowerGain b td t s-positiveCost b*(s-t) := by
  have hs' : s∈Icc 0 (cap td) := by cases td <;> simpa [shortDomain,cap] using hs
  have htcap : t≤cap td := hts.trans hs'.2
  have hremoved : removed td t=t := min_eq_left htcap
  have hend := far_endpoint face td hR hQU ht hout 0
  rw [hremoved,sub_self,canonical_zero,add_zero] at hend
  have hlen : 0≤ s-t := sub_nonneg.mpr hts
  have hcost := (cost_bounds b).2.1
  cases td
  · have hcL : (17253/20000:ℝ)≤c b t := by
      by_cases hb : b=.low
      · subst b; exact (low_bounds ht).1.trans (low_bounds ht).2.2.1
      · linarith [(balanced_bounds hb ht).2.2.2.1]
    have hm := mul_le_mul_of_nonneg_right hcL hlen
    simp only [lowerGain,slope,Bool.false_eq_true,ite_false] at hend ⊢
    nlinarith
  · have ht' : t∈Icc 0 (3/10:ℝ) := ⟨(angle ht).1,by simpa [cap] using htcap⟩
    have hs'' : s∈Icc t (3/10:ℝ) := ⟨hts,by simpa [cap] using hs'.2⟩
    have hg := late_growth ht ht' hs''
    have hJ := mul_le_mul_of_nonneg_left (J_linear ht' ⟨ht'.1,le_rfl⟩) (ranges ht).2.2.2.1.le
    simp only [slope,ite_true,hremoved] at hend
    simp only [lowerGain,ite_true]
    nlinarith

theorem total_positive (face td : Bool) {b : Band} {R t s : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qTrial) (ht : t∈domain b)
    (hout : t≤1/10 ∨ 4/25≤t) (hs : s∈shortDomain td) :
    0<base b R t face+correction b td t+lowerGain b td t s+lowerEnvelope b R t face s := by
  by_cases hst : s≤t
  · simpa [lowerEnvelope,hst] using negative_net face td hR hQL hQU ht hout hs hst
  · simpa [lowerEnvelope,hst,sub_eq_add_neg] using
      positive_net face td hR hQU ht hout hs (lt_of_not_ge hst).le

end SquaresInCircles.Eight.ExceptionalNegativeTEndpoints
