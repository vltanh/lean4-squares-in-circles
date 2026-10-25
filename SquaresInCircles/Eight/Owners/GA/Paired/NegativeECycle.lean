module

public import SquaresInCircles.Eight.Owners.GA.ETransport
public import SquaresInCircles.Eight.Owners.GA.EZero
public import SquaresInCircles.Eight.Owners.GA.Paired.NegativeEConcavity
public import SquaresInCircles.Eight.Owners.Negative.CoreEEntry

/-!
# Eight squares: two negative E primaries reduce to one in a high-GA source domain

`reduce` turns two negative E primaries DE3 and EH1 of a core E into one. If EH0 or DE2 is
feasible, E is reselected at the same state. Otherwise the intrinsic concavity endpoint takes the
place of E in the seven-cycle (`Endpoint.toMove`): its frame stays between the frames of H and D,
both variations are unchanged, and the moved cycle is again a source domain (`Result.source`). The
zero-tangent endpoint is excluded by the reflected BT theorem, and at each of the two other
endpoints an aligned secondary is selected.
-/

section
/-!
## Actual intrinsic endpoint for the two negative core-E primaries

E first reaches its exact EH cap at the original
frame.  The whole-interval concavity alternative then constructs a
sorted true-core endpoint at the same q, retaining the original D/H
states and both actual primary separators.  The only terminal events
are alignment with H, alignment with D, and zero E tangent.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedNegativeE
open PrimaryCap

structure Endpoint (q : ℝ) (D H : SignedPoint) (v : ℝ) where
  point : SignedPoint
  x : ℝ
  range : x∈Icc 0 v
  sorted : point.Sorted
  contained : point.Contained q
  core : point.Core
  nonpos : point.y≤0
  flat : point.a=7/12
  DE3 : quarterFeasible D point (-(v-x)) 3
  EH1 : quarterFeasible point H (-x) 1
  terminal : x=0 ∨ x=v ∨ point.y=0

theorem DE_margin {P v x : ℝ} (D : SignedPoint)
    (hx : v-x∈Icc 0 (7/10:ℝ)) :
    quarterProjection D (point P x) (-(v-x)) 3-edgeWidth (-(v-x))=
      D.a-requiredD P v x := by
  rw [edgeWidth_negative_formula hx]
  simp only [quarterProjection,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons,point,
    Real.sin_neg,Real.cos_neg,requiredD,K]
  ring

/-- All geometry of an exact cap point is checked at the original q. -/
def atParameter {q P v x : ℝ} {D H : SignedPoint}
    (hqL : qLow≤q) (hP : 1/2<P ∧ P<183/200) (hH : H.a=P+1/2)
    (hv : v∈Icc 0 (7/10:ℝ)) (hx : x∈Icc 0 v)
    (hcap : 1/2≤value P x) (hD : requiredD P v x≤D.a)
    (he : x=0 ∨ x=v ∨ value P x=1/2) : Endpoint q D H v := by
  have hxwide : x∈Icc 0 (7/10:ℝ) := ⟨hx.1,hx.2.trans hv.2⟩
  have hu := value_le_position ⟨by linarith [hP.1],hP.2.le⟩ hxwide
  have habs : |-(value P x-1/2)|≤1/2 := by
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤value P x-1/2)]
    linarith [hP.2]
  refine {
    point := PrimaryCap.point P x
    x := x
    range := hx
    sorted := SignedPoint.flat_sorted habs
    contained := SignedPoint.flat_contained hqL habs
    core := SignedPoint.flat_on_core habs
    nonpos := by dsimp [PrimaryCap.point]; linarith
    flat := rfl
    DE3 := ?_
    EH1 := (actual_primary_contact hH hxwide).ge
    terminal := ?_ }
  · apply sub_nonneg.mp
    rw [DE_margin D (show v-x∈Icc 0 (7/10:ℝ) by
      constructor <;> linarith [hx.1,hx.2,hv.2])]
    exact sub_nonneg.mpr hD
  · rcases he with he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (by simp [PrimaryCap.point,he]))

theorem actual_parameters {q t : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEc : E.Core) (hEy : E.y≤0)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (hHy : 0≤H.y) (hq : q≤qCap) (ht : t∈Ioc 0 frameCap)
    (hEH : quarterFeasible E H (-t) 1)
    (hnot : ¬quarterFeasible E H (-t) 0) :
    E.a=7/12 ∧ (1/2<H.a-1/2 ∧ H.a-1/2<183/200) := by
  have hf := (NegativeCoreE.genuine_negative_flat hEs hEy hEc hHs hHy hHc hq
    ht hEH hnot).1
  have hcos := transport_cos_pos (by rw [abs_of_pos ht.1]; exact ht.2)
  have hsin : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by have := ht.2; simp only [frameCap] at this; linarith [Real.pi_gt_three])
  have hyprod := mul_nonpos_of_nonpos_of_nonneg hEy hcos.le
  have hraw : edgeWidth (-t)≤H.a-(7/12)*Real.sin t+E.y*Real.cos t := by
    have h := hEH
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,
      Real.sin_neg,Real.cos_neg,hf] at h
    linarith
  have hupper := (SignedPoint.coordinate_bounds hHs hHcore hHc hq).2.1
  exact ⟨hf,by constructor <;> linarith [edgeWidth_ge_one (-t)]⟩

/-- The initial E need not already be on EH contact.  Increasing its
negative tangent to the cap weakly improves the original DE3 margin. -/
theorem endpoint {q v t : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hP : 1/2<H.a-1/2 ∧ H.a-1/2<183/200)
    (hflat : E.a=7/12) (hEy : E.y≤0)
    (hv : v∈Ioc 0 (7/10:ℝ)) (ht : t∈Ioo 0 v)
    (hDE : quarterFeasible D E (-(v-t)) 3)
    (hEH : quarterFeasible E H (-t) 1) : Nonempty (Endpoint q D H v) := by
  set P := H.a-1/2 with hPdef
  have hHP : H.a=P+1/2 := by rw [hPdef]; ring
  have htwide : t∈Icc 0 (7/10:ℝ) := ⟨ht.1.le,ht.2.le.trans hv.2⟩
  have hswide : v-t∈Icc 0 (7/10:ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hv.2]⟩
  have hcos := transport_cos_pos (by rw [abs_of_pos ht.1]; exact htwide.2)
  have hcapIdentity := value_contact_identity P t hcos.ne'
  have hrawEH : edgeWidth (-t)≤H.a-(7/12)*Real.sin t+E.y*Real.cos t := by
    have h := hEH
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,
      Real.sin_neg,Real.cos_neg,hflat] at h
    linarith
  rw [edgeWidth_negative_formula htwide] at hrawEH
  have hproduct : 0≤(value P t-1/2+E.y)*Real.cos t := by
    simp only [K] at hcapIdentity
    linarith
  have hcapTangent : -E.y≤value P t-1/2 := by
    have hh := (mul_nonneg_iff_of_pos_right hcos).1 hproduct
    linarith
  have hcap : 1/2≤value P t := by linarith
  have hrawDE : edgeWidth (-(v-t))≤
      D.a-(7/12)*Real.sin (v-t)-E.y*Real.cos (v-t) := by
    have h := hDE
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,Matrix.tail_cons,
      Matrix.head_cons,Real.sin_neg,Real.cos_neg,hflat] at h
    linarith
  rw [edgeWidth_negative_formula hswide] at hrawDE
  have hcosS := transport_cos_pos (by
    rw [abs_of_nonneg hswide.1]; exact hswide.2)
  have hgain := mul_nonneg (show 0≤value P t-1/2+E.y by linarith) hcosS.le
  have hrequired : requiredD P v t≤D.a := by
    simp only [requiredD,K]
    linarith
  by_cases hzero : value P t=1/2
  · exact ⟨atParameter hqL hP hHP ⟨hv.1.le,hv.2⟩
      ⟨ht.1.le,ht.2.le⟩ hcap hrequired (Or.inr (Or.inr hzero))⟩
  obtain ⟨z,⟨hz,hzval⟩,hunique⟩ := exists_unique_zero_tangent hP.1 hP.2
  have htz : t≤z := (cap_feasible_iff_before hP hz hzval htwide).1 hcap
  have htz' : t<z := by
    by_contra! hh
    have he : t=z := le_antisymm htz hh
    exact hzero (by simpa only [he] using hzval)
  have hm : t∈Ioo 0 (min v z) := ⟨ht.1,lt_min ht.2 htz'⟩
  rcases endpoint_decrease hP hv hz hzval hm with hleft | hright
  · have h0 : (0:ℝ)∈Icc 0 v := ⟨le_rfl,hv.1.le⟩
    have hcap0 : 1/2≤value P 0 := by simpa only [value_zero] using hP.1.le
    exact ⟨atParameter hqL hP hHP ⟨hv.1.le,hv.2⟩ h0
      hcap0 (hleft.le.trans hrequired) (Or.inl rfl)⟩
  · have hrange : min v z∈Icc 0 v :=
      ⟨le_min hv.1.le hz.1.le,min_le_left _ _⟩
    have hwide : min v z∈Icc 0 (7/10:ℝ) :=
      ⟨hrange.1,hrange.2.trans hv.2⟩
    have hcapR := (cap_feasible_iff_before hP hz hzval hwide).2 (min_le_right _ _)
    have hterminal : min v z=0 ∨ min v z=v ∨ value P (min v z)=1/2 := by
      rcases le_total v z with hh | hh
      · exact Or.inr (Or.inl (min_eq_left hh))
      · exact Or.inr (Or.inr (by simpa only [min_eq_right hh] using hzval))
    exact ⟨atParameter hqL hP hHP ⟨hv.1.le,hv.2⟩ hrange
      hcapR (hright.le.trans hrequired) hterminal⟩

end SquaresInCircles.Eight.GlobalGA.PairedNegativeE
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedNegativeE
open Candidate SignedCycle ETransport

def Endpoint.toMove {q : ℝ} {C : SignedCycle}
    (O : Endpoint q (C.point D) (C.point H) (C.theta D-C.theta H))
    (hDE : delta C.theta D<0) (hEH : delta C.theta E<0) : Move q C where
  point := O.point
  theta := C.theta H+O.x
  sorted := O.sorted
  contained := O.contained
  core := O.core
  flat := O.flat
  nonpos := O.nonpos
  frame_range := by
    have hHD : C.theta H≤C.theta D := by linarith [O.range.1,O.range.2]
    refine ⟨H,D,?_⟩
    rw [min_eq_left hHD,max_eq_right hHD]
    constructor <;> linarith [O.range.1,O.range.2]
  de := 3
  eh := 1
  de_allowed := Or.inr rfl
  eh_allowed := Or.inr rfl
  DE := by convert O.DE3 using 1; ring
  EH := by convert O.EH1 using 1; ring
  positive_nonincrease := by
    have hd : C.theta E<C.theta D := by simpa [delta,next,D,E] using hDE
    have he : C.theta H<C.theta E := by simpa [delta,next,E,H] using hEH
    have hDEold : positivePart (C.theta E-C.theta D)=0 :=
      max_eq_right (sub_nonpos.mpr hd.le)
    have hEHold : positivePart (C.theta H-C.theta E)=0 :=
      max_eq_right (sub_nonpos.mpr he.le)
    have hDEnew : positivePart (C.theta H+O.x-C.theta D)=0 :=
      max_eq_right (by linarith [O.range.2])
    have hEHnew : positivePart (C.theta H-(C.theta H+O.x))=0 :=
      max_eq_right (by linarith [O.range.1])
    have heq : positiveVariation (Function.update C.theta E (C.theta H+O.x))=
        positiveVariation C.theta := by
      have h1 : positivePart (C.theta 0+O.x-C.theta 5)=0 := hDEnew
      have h2 : positivePart (-O.x)=0 := by
        rw [show -O.x=C.theta H-(C.theta H+O.x) by ring]
        exact hEHnew
      have h3 : positivePart (C.theta 6-C.theta 5)=0 := hDEold
      have h4 : positivePart (C.theta 0-C.theta 6)=0 := hEHold
      simp [positiveVariation,Fin.sum_univ_succ,delta,next,H,D,E,Function.update_apply]
      rw [h1,h2,h3,h4]
    exact heq.le

structure Result (q : ℝ) (C : SignedCycle) where
  move : Move q C
  single :
    (move.de=3 ∧ move.eh=0 ∧ delta move.cycle.theta D<0) ∨
    (move.de=2 ∧ move.eh=1 ∧ delta move.cycle.theta E<0)

def Result.source {q : ℝ} {C : SignedCycle} (R : Result q C)
    (I : SourceDomain q C) (hq : q≤qCap) : SourceDomain q R.move.cycle :=
  R.move.source I hq

/-- No new point, endpoint event or feasible descendant is assumed: the intrinsic local theorem
gives them, realized with the neighboring data of the cycle. -/
theorem reduce {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hEc : (C.point E).Core)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 1)
    (hDEneg : delta C.theta D<0) (hEHneg : delta C.theta E<0) :
    Nonempty (Result q C) := by
  have hDE' : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  have hEH' : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  by_cases hEH0 : C.Feasible E 0
  · have hEH0' : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH0
    have hf := (NegativeCoreE.secondary_flat (I.necessary.sorted E) I.E_nonpos hEc
      (I.necessary.sorted H) (I.necessary.contained H) hqU hEH0').1
    let O := ETransport.identity I hEc hf 3 0 (Or.inr rfl) (Or.inl rfl) hDE hEH0
    refine ⟨⟨O,Or.inl ⟨rfl,rfl,?_⟩⟩⟩
    simpa [O,ETransport.identity,Move.cycle,replacePoint] using hDEneg
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hD : C.theta E<C.theta D := by simpa [delta,next,D,E] using hDEneg
  have hH : C.theta H<C.theta E := by simpa [delta,next,E,H] using hEHneg
  have ht : C.theta E-C.theta H∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hH,(le_abs_self _).trans (I.necessary.spread E H)⟩
  obtain ⟨hflat,hP⟩ := actual_parameters (I.necessary.sorted E) hEc I.E_nonpos
    (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H)
    I.H_positive.le hqU ht (by simpa only [neg_sub] using hEH')
    (by simpa only [neg_sub] using hnot)
  by_cases hDE2 : C.Feasible D 2
  · let O := ETransport.identity I hEc hflat 2 1 (Or.inl rfl) (Or.inr rfl) hDE2 hEH
    refine ⟨⟨O,Or.inr ⟨rfl,rfl,?_⟩⟩⟩
    simpa [O,ETransport.identity,Move.cycle,replacePoint] using hEHneg
  have hv : C.theta D-C.theta H∈Ioc 0 (7/10:ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D H)⟩
  obtain ⟨P⟩ := endpoint hqL hP hflat I.E_nonpos hv
    (show C.theta E-C.theta H∈Ioo 0 (C.theta D-C.theta H) by
      constructor <;> linarith)
    (by convert hDE' using 1; ring)
    (by simpa only [neg_sub] using hEH')
  let O := P.toMove hDEneg hEHneg
  have hzero : P.point.y≠0 := by
    intro hz
    have hq : q∈Icc (5/2:ℝ) Q0 :=
      ⟨(show (5/2:ℝ)≤qLow by norm_num [qLow]).trans hqL,by simpa only [qCap,Q0] using hqU⟩
    have hh := (O.source I hqU).E_negative hq
    change P.point.y<0 at hh
    linarith
  rcases P.terminal with hx | hx | hy
  · have hsecondary : quarterFeasible O.point (C.point H) (C.theta H-O.theta) 0 := by
      have hp : quarterFeasible P.point (C.point H) 0 1 := by simpa [hx] using P.EH1
      have hs := (quarter_low_tie P.point (C.point H)).2 hp
      simpa [O,Endpoint.toMove,hx] using hs
    let O' : Move q C := { O with eh:=0,eh_allowed:=Or.inl rfl,EH:=hsecondary }
    refine ⟨⟨O',Or.inl ⟨rfl,rfl,?_⟩⟩⟩
    change C.theta H+P.x-C.theta D<0
    rw [hx]
    linarith [hv.1]
  · have hsecondary : quarterFeasible (C.point D) O.point (O.theta-C.theta D) 2 := by
      have hp : quarterFeasible (C.point D) P.point 0 3 := by simpa [hx] using P.DE3
      have hs := (quarter_high_tie (C.point D) P.point).2 hp
      have heq : O.theta-C.theta D=0 := by
        dsimp [O,Endpoint.toMove]
        rw [hx]
        ring
      rw [heq]
      exact hs
    let O' : Move q C := { O with de:=2,de_allowed:=Or.inl rfl,DE:=hsecondary }
    refine ⟨⟨O',Or.inr ⟨rfl,rfl,?_⟩⟩⟩
    change C.theta H-(C.theta H+P.x)<0
    rw [hx]
    linarith [hv.1]
  · exact (hzero hy).elim

end SquaresInCircles.Eight.GlobalGA.PairedNegativeE
end
end
end
