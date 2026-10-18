module

public import SquaresInCircles.Eight.Arithmetic.StateCoverage
public import SquaresInCircles.Eight.Candidate.Geometry
public import SquaresInCircles.Eight.Frames

/-!
# Complete affine-table coverage and the cyclic charged bound

The state cover chooses one label per vertex before any separating axis is
selected. Angle chains cover every original axis permitted by the stage.
Their finite predicate is independent of the continuous row Claims.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Arithmetic

instance : Inhabited ArctanEndpoint := ⟨⟨0,⟨0,0⟩,⟨0,0⟩⟩⟩
instance : Inhabited AffineTableRow := ⟨⟨0,0,0,.one,0,true,⟨0,0⟩,0,.endpoints,1,0⟩⟩

def QInterval.inter (I J : QInterval) : QInterval := ⟨max I.lo J.lo,min I.hi J.hi⟩
theorem QInterval.mem_inter {I J : QInterval} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) :
    (I.inter J).Mem x := by
  constructor
  · rcases le_total I.lo J.lo with h | h
    · simpa [QInterval.inter,max_eq_right h] using hJ.1
    · simpa [QInterval.inter,max_eq_left h] using hI.1
  · rcases le_total I.hi J.hi with h | h
    · simpa [QInterval.inter,min_eq_left h] using hI.2
    · simpa [QInterval.inter,min_eq_right h] using hJ.2

def ForwardAxis.ofIndex (i : Fin 4) : ForwardAxis := ![.one,.two,.three,.four] i
@[simp] theorem ForwardAxis.index_ofIndex (i : Fin 4) : (ForwardAxis.ofIndex i).index=i := by
  fin_cases i <;> rfl

theorem forwardMargin_congr_products (axis : ForwardAxis) {σ τ σ' τ' a b A B φ : ℝ}
    (hs : σ*b=σ'*b) (ht : τ*B=τ'*B) :
    forwardMargin axis σ τ a b A B φ=forwardMargin axis σ' τ' a b A B φ := by
  cases axis <;> simp only [forwardMargin,hs,ht]

structure AffineCover where
  endpoints : List (ArctanEndpoint × ArctanEndpoint)
  states : StateChains
  angleRows : ℕ→ℕ→ForwardAxis→Bool→List ℕ

namespace AffineCover

def endpointAt (K : AffineCover) (k : ℕ) : ArctanEndpoint × ArctanEndpoint :=
  K.endpoints.getD k default
def alphaBox (K : AffineCover) (M : AffineTableMeta) (k : ℕ) : QInterval :=
  if (arcAt M k).positive then
    ⟨(K.endpointAt k).1.output.lo,(K.endpointAt k).2.output.hi⟩
  else ⟨-(K.endpointAt k).2.output.hi,-(K.endpointAt k).1.output.lo⟩
def piBox : QInterval :=
  ⟨3141592653589793238/1000000000000000000,3141592653589793239/1000000000000000000⟩
def phaseBox (K : AffineCover) (M : AffineTableMeta) (s t : ℕ) : QInterval :=
  (⟨19/25,710/113-114/25⟩ : QInterval).sub (K.alphaBox M s) |>.add (K.alphaBox M t)
def baseBox (M : AffineTableMeta) (i : Vertex) : QInterval :=
  (QInterval.point ((M.word i : ℚ)/2)).mul piBox
def required (K : AffineCover) (M : AffineTableMeta) (s t : ℕ) (positiveHalf : Bool) : QInterval :=
  let i := (arcAt M s).role
  let phase := K.phaseBox M s t
  let base := baseBox M i
  let raw := if positiveHalf then phase.sub base else base.sub phase
  let difference := if positiveHalf then M.differenceRange i else (M.differenceRange i).neg
  (raw.inter difference).inter ⟨0,7/10⟩

def EndpointsValid (K : AffineCover) (M : AffineTableMeta) : Prop :=
  ∀ k : Fin M.arcs.length,
    (K.endpointAt k).1.NumericValid ∧ (K.endpointAt k).2.NumericValid ∧
    (K.endpointAt k).1.input=(arcAt M k).tangent.lo ∧
    (K.endpointAt k).2.input=(arcAt M k).tangent.hi

def AngleValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  ∀ s t : Fin M.arcs.length,
    (arcAt M t).role=(arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis∈M.allowedAxes (arcAt M s).role → ∀ r : Bool,
      Every (fun k => k<rows.length ∧
        (rows.getD k default).source=s.val ∧ (rows.getD k default).target=t.val ∧
        (rows.getD k default).edge=(arcAt M s).role ∧ (rows.getD k default).axis=axis ∧
        (rows.getD k default).quarter=M.word (arcAt M s).role ∧
        (rows.getD k default).positiveHalf=r ∧
        M.target (arcAt M s).role≤(rows.getD k default).lowerTarget)
        (K.angleRows s t axis r) ∧
      ClosedChain (K.required M s t r).lo (K.required M s t r).hi
        ((K.angleRows s t axis r).map (fun k => (rows.getD k default).angle))

def NumericValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  K.EndpointsValid M ∧ K.states.NumericValid M ∧ K.AngleValid M rows

instance (K : AffineCover) (M : AffineTableMeta) : Decidable (K.EndpointsValid M) := by
  unfold EndpointsValid; infer_instance
instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (K.AngleValid M rows) := by unfold AngleValid; infer_instance
instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (K.NumericValid M rows) := by unfold NumericValid; infer_instance

theorem alpha_mem {K : AffineCover} {M : AffineTableMeta} (hK : K.EndpointsValid M)
    (k : Fin M.arcs.length) {a b : ℝ} (hab : (arcAt M k).Contains M.radius a b) :
    (K.alphaBox M k).Mem (Real.arctan ((arcAt M k).sign*b/a)) := by
  have hlo := (hK k).1.sound
  have hhi := (hK k).2.1.sound
  rw [(hK k).2.2.1] at hlo
  rw [(hK k).2.2.2] at hhi
  have hl := Real.arctan_mono hab.2.2.2.1.1
  have hu := Real.arctan_mono hab.2.2.2.1.2
  cases hs : (arcAt M k).positive with
  | true =>
      simpa [alphaBox,ArcData.sign,hs] using And.intro (hlo.1.trans hl) (hu.trans hhi.2)
  | false =>
      have hx : -(1:ℝ)*b/a=-(b/a) := by ring
      simp only [alphaBox,hs,if_false,ArcData.sign,hx,Real.arctan_neg,QInterval.Mem]
      push_cast
      exact ⟨by linarith [hu,hhi.2],by linarith [hl,hlo.1]⟩

theorem frame_gap_upper {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C) (i : Vertex) :
    angleGap C.beta i < (710/113-114/25 : ℝ) := by
  have hsum := angleGap_sum C.beta
  have h0 := F.gap_lower 0
  have h1 := F.gap_lower 1
  have h2 := F.gap_lower 2
  have h3 := F.gap_lower 3
  have h4 := F.gap_lower 4
  have h5 := F.gap_lower 5
  have h6 := F.gap_lower 6
  have hpi := two_pi_lt_710_over_113
  simp only [Fin.sum_univ_succ] at hsum
  fin_cases i <;> nlinarith

theorem required_mem {K : AffineCover} {M : AffineTableMeta}
    (hK : K.EndpointsValid M) (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role=i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i=C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i)=C.sigma (next i)*C.b (next i))
    {r : Bool} {u : ℝ} (hu : u=|Candidate.delta F.theta i|)
    (hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u) :
    (K.required M s t r).Mem u := by
  have hαs := K.alpha_mem hK s hs
  have hαt := K.alpha_mem hK t ht
  rw [hσ] at hαs
  rw [hτ] at hαt
  change (K.alphaBox M s).Mem (C.alpha i) at hαs
  change (K.alphaBox M t).Mem (C.alpha (next i)) at hαt
  have hgap : (⟨19/25,710/113-114/25⟩:QInterval).Mem (angleGap C.beta i) :=
    ⟨(F.gap_lower i).le,(frame_gap_upper F i).le⟩
  have hphase := QInterval.mem_add (QInterval.mem_sub hgap hαs) hαt
  have hφ : (K.phaseBox M s t).Mem (Candidate.phi F.theta i) := by
    convert hphase using 1
    · rfl
    · rw [F.physical_angle]
      ring
  have hpi : piBox.Mem Real.pi := ⟨pi_hand_enclosure.1.le,pi_hand_enclosure.2.le⟩
  -- The singleton constructor takes a rational; its membership theorem
  -- performs the coercion to the real coordinate. Do not coerce first.
  have hb := QInterval.mem_mul (QInterval.mem_point ((M.word i:ℚ)/2)) hpi
  have hbase : (baseBox M i).Mem ((M.word i:ℝ)*Real.pi/2) := by
    convert hb using 1 <;> push_cast <;> ring
  have hph : Candidate.phi F.theta i=(M.word i:ℝ)*Real.pi/2+Candidate.delta F.theta i := by
    rw [hword]
    rfl
  have hsmall : (⟨0,7/10⟩:QInterval).Mem u := by
    rw [hu]
    exact ⟨abs_nonneg _,(F.delta_small i).le⟩
  cases hr : r with
  | true =>
      have hδ : Candidate.delta F.theta i=u := by simpa [hr,AnglePolynomial.signQ] using hdu
      have hraw := QInterval.mem_sub hφ hbase
      have hraw' : ((K.phaseBox M s t).sub (baseBox M i)).Mem u := by
        convert hraw using 1 <;> rw [hph,hδ] <;> ring
      have hdiff' : (M.differenceRange i).Mem u := by simpa [hδ] using hdiff i
      simpa [required,hr,hsi] using QInterval.mem_inter (QInterval.mem_inter hraw' hdiff') hsmall
  | false =>
      have hδ : Candidate.delta F.theta i= -u := by simpa [hr,AnglePolynomial.signQ] using hdu
      have hraw := QInterval.mem_sub hbase hφ
      have hraw' : ((baseBox M i).sub (K.phaseBox M s t)).Mem u := by
        convert hraw using 1 <;> rw [hph,hδ] <;> ring
      have hdiff' : (M.differenceRange i).neg.Mem u := by
        simpa [hδ] using QInterval.mem_neg (hdiff i)
      simpa [required,hr,hsi] using QInterval.mem_inter (QInterval.mem_inter hraw' hdiff') hsmall

theorem row_cover {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : K.AngleValid M rows) {s t : Fin M.arcs.length}
    (hst : (arcAt M t).role=(arcAt M s).role+1)
    {axis : ForwardAxis} (haxis : axis∈M.allowedAxes (arcAt M s).role)
    {r : Bool} {u : ℝ} (hu : (K.required M s t r).Mem u) :
    ∃ row ∈ rows,
      row.source=s.val ∧ row.target=t.val ∧ row.edge=(arcAt M s).role ∧
      row.axis=axis ∧ row.quarter=M.word (arcAt M s).role ∧
      row.positiveHalf=r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role≤row.lowerTarget := by
  have hh := hK s t hst axis haxis r
  obtain ⟨I,hI,hIu⟩ := hh.2.covers hu
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hI
  have hp := hh.1.of_mem hk
  exact ⟨rows.getD k default,list_getD_mem hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,
    hp.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hIu,hp.2.2.2.2.2.2.2⟩

/-- Closed state and angle covers supply a genuine cyclic charged bound. -/
noncomputable def chargedBound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : K.NumericValid M rows) (hrows : ∀ r∈rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Candidate.Frame C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i) :
    Candidate.ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hK.2.1 C hcuts i
  refine {label:=fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i),pair_bound:=?_}
  intro i j hj
  let axis := ForwardAxis.ofIndex j
  let d := Candidate.delta F.theta i
  let r : Bool := decide (0≤d)
  let u := |d|
  have hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u := by
    dsimp [r,u,d]
    by_cases hd : 0≤Candidate.delta F.theta i <;>
      simp [hd,AnglePolynomial.signQ,abs_of_nonneg,abs_of_neg]
  have hu := K.required_mem hK.1 C F hword hdiff (hrole i) (hcontains i)
    (hcontains (next i)) (hproducts i) (hproducts (next i)) (r:=r) (u:=u) rfl hdu
  have hallowed : axis∈M.allowedAxes (arcAt M (selected i)).role := by
    simpa [axis,hrole] using haxes i j hj
  obtain ⟨row,hrow,hs,ht,he,ha,hk,hr,hru,hγ⟩ := K.row_cover hK.2.2
    (by rw [hrole,hrole]; rfl) hallowed hu
  have hsdata : row.sourceArc M=arcAt M (selected i) := by simp [AffineTableRow.sourceArc,arcAt,hs]
  have htdata : row.targetArc M=arcAt M (selected (next i)) := by simp [AffineTableRow.targetArc,arcAt,ht]
  have he' : row.edge=i := he.trans (hrole i)
  have hphi : row.phi u=Candidate.phi F.theta i := by
    rw [AffineTableRow.phi,hk,hrole]
    rw [show row.sign=(AnglePolynomial.signQ r:ℝ) by cases r <;> simp [AffineTableRow.sign,hr,AnglePolynomial.signQ]]
    rw [← hdu,hword]
    rfl
  have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
    ⟨by simpa [hsdata] using hcontains i,by simpa [htdata] using hcontains (next i),hru⟩
  have hactual := (F.margin_nonneg_iff i j).mp hj
  have horiginal : 0≤forwardMargin axis (C.sigma i) (C.sigma (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
    simpa [forwardMargin_actual,axis,Candidate.margin] using hactual
  have hselected : 0≤forwardMargin row.axis (row.sourceArc M).sign (row.targetArc M).sign
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
    rw [ha,hsdata,htdata,hphi,
      forwardMargin_congr_products axis (hproducts i) (hproducts (next i))]
    exact horiginal
  have hp := hrows row hrow _ _ _ _ _ hdom hselected
  have htarget : (M.target i:ℝ)≤row.lowerTarget := by simpa [hrole] using (show (M.target (arcAt M (selected i)).role:ℝ)≤row.lowerTarget by exact_mod_cast hγ)
  have hh := htarget.trans_lt hp
  simpa [chargedCost,frameCharge,Candidate.h,hsdata,htdata,he',hphi,hcharge,
    sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

end AffineCover
end SquaresInCircles.Eight.Arithmetic
