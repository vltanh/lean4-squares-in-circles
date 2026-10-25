module

public import SquaresInCircles.Eight.Owners.Primary.PairClassification

/-!
# Eight squares: composing the two pair moves

The output of the pair move of G replaces G in the signed cycle (`GPairOutput.cycle`), with its
owners as witnesses (`GPairOutput.witnesses`): the cycle still satisfies `Necessary`, the sign
implications of the zero owners hold, the anchors keep their points and frames, and neither
signed variation of the frames grows (`GPairOutput.necessary`, `zero_signs`, `anchors`,
`variations`), since the new frame stays at its value or between the frames of H and A
(`spread_replace_clamped`, `clamped_pair_variations`). The same holds for T. The two moves
compose (`compose_primary_pair_outputs`): after both, the cycle satisfies `Necessary`, lies on the
boundary, has a strict spread, keeps the anchors of `C`, E included, has variations at most those
of `C`, and has witnesses with the sign implications. Its cyclic order is not part of this; it is
proved from the geometry (`SignedCycle.normal_necessary_ordered`). When a hard axis is already
feasible, the move leaves G or T in place (`hardG`, `hardT`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

private theorem abs_sub_le_between {a b t x r : ℝ}
    (ht : t∈Icc (min a b) (max a b))
    (ha : |a-x|≤r) (hb : |b-x|≤r) : |t-x|≤r := by
  have h₁ := abs_le.mp ha
  have h₂ := abs_le.mp hb
  apply abs_le.mpr
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab,max_eq_right hab,mem_Icc] at ht
    constructor <;> linarith
  · simp only [min_eq_right hab,max_eq_left hab,mem_Icc] at ht
    constructor <;> linarith

private theorem abs_sub_lt_between {a b t x r : ℝ}
    (ht : t∈Icc (min a b) (max a b))
    (ha : |a-x|<r) (hb : |b-x|<r) : |t-x|<r := by
  have h₁ := abs_lt.mp ha
  have h₂ := abs_lt.mp hb
  apply abs_lt.mpr
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab,max_eq_right hab,mem_Icc] at ht
    constructor <;> linarith
  · simp only [min_eq_right hab,max_eq_left hab,mem_Icc] at ht
    constructor <;> linarith

/-- A frame `t` between the frames `a` and `b` of its neighbours has positive and negative steps
no larger than those of any frame `x`: clamping can only remove cancellation. -/
theorem clamped_pair_variations {a b t x : ℝ}
    (ht : t∈Icc (min a b) (max a b)) :
    positivePart (t-a)+positivePart (b-t)≤
        positivePart (x-a)+positivePart (b-x) ∧
      negativePart (t-a)+negativePart (b-t)≤
        negativePart (x-a)+negativePart (b-x) := by
  have hp := positivePart_add_le (x-a) (b-x)
  have hn := negativePart_add_le (x-a) (b-x)
  rw [show x-a+(b-x)=b-a by ring] at hp hn
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab,max_eq_right hab,mem_Icc] at ht
    have h₁ : 0≤t-a := by linarith
    have h₂ : 0≤b-t := by linarith
    have he : positivePart (t-a)+positivePart (b-t)=positivePart (b-a) := by
      simp only [positivePart,max_eq_left h₁,max_eq_left h₂,
        max_eq_left (by linarith : 0≤b-a)]
      ring
    have hn0 : negativePart (t-a)+negativePart (b-t)=0 := by
      simp only [negativePart,max_eq_right (neg_nonpos.mpr h₁),
        max_eq_right (neg_nonpos.mpr h₂),add_zero]
    exact ⟨he.trans_le hp,by
      rw [hn0]
      exact add_nonneg (negativePart_nonneg _) (negativePart_nonneg _)⟩
  · simp only [min_eq_right hab,max_eq_left hab,mem_Icc] at ht
    have h₁ : t-a≤0 := by linarith
    have h₂ : b-t≤0 := by linarith
    have hp0 : positivePart (t-a)+positivePart (b-t)=0 := by
      simp only [positivePart,max_eq_right h₁,max_eq_right h₂,add_zero]
    have he : negativePart (t-a)+negativePart (b-t)=negativePart (b-a) := by
      simp only [negativePart,max_eq_left (neg_nonneg.mpr h₁),
        max_eq_left (neg_nonneg.mpr h₂),
        max_eq_left (by linarith : 0≤ -(b-a))]
      ring
    exact ⟨by
      rw [hp0]
      exact add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),he.trans_le hn⟩

namespace SignedCycle

/-- The spread survives a replacement whose frame stays at the frame of `v` or between the frames
of `a` and `b`. -/
theorem spread_replace_clamped {C : SignedCycle} {v a b : Vertex}
    {p : SignedPoint} {t : ℝ} (h : C.Spread)
    (ht : t=C.theta v ∨ t∈Icc (min (C.theta a) (C.theta b))
      (max (C.theta a) (C.theta b))) :
    (replacePoint C v p t).Spread := by
  have hbound (j : Vertex) : |t-C.theta j|≤frameCap := by
    rcases ht with he | hi
    · rw [he]; exact h v j
    · exact abs_sub_le_between hi (h a j) (h b j)
  intro i j
  by_cases hi : i=v
  · by_cases hj : j=v
    · norm_num [replacePoint,hi,hj,frameCap]
    · simpa [replacePoint,hi,hj] using hbound j
  · by_cases hj : j=v
    · simpa [replacePoint,hi,hj,abs_sub_comm] using hbound i
    · simpa [replacePoint,hi,hj] using h i j

theorem strictSpread_replace_clamped {C : SignedCycle} {v a b : Vertex}
    {p : SignedPoint} {t : ℝ} (h : C.StrictSpread)
    (ht : t=C.theta v ∨ t∈Icc (min (C.theta a) (C.theta b))
      (max (C.theta a) (C.theta b))) :
    (replacePoint C v p t).StrictSpread := by
  have hbound (j : Vertex) : |t-C.theta j|<frameCap := by
    rcases ht with he | hi
    · rw [he]; exact h v j
    · exact abs_sub_lt_between hi (h a j) (h b j)
  intro i j
  by_cases hi : i=v
  · by_cases hj : j=v
    · norm_num [replacePoint,hi,hj,frameCap]
    · simpa [replacePoint,hi,hj] using hbound j
  · by_cases hj : j=v
    · simpa [replacePoint,hi,hj,abs_sub_comm] using hbound i
    · simpa [replacePoint,hi,hj] using h i j

theorem necessary_replace_clamped {C : SignedCycle} {q : ℝ} {v a b : Vertex}
    {p : SignedPoint} {t : ℝ} (h : C.Necessary q)
    (hs : p.Sorted) (hc : p.Contained q) (hcore : p.AvoidsCore)
    (ht : t=C.theta v ∨ t∈Icc (min (C.theta a) (C.theta b))
      (max (C.theta a) (C.theta b))) :
    (replacePoint C v p t).Necessary q := {
  sorted i := by
    by_cases hi : i=v
    · simpa [replacePoint,hi] using hs
    · simpa [replacePoint,hi] using h.sorted i
  contained i := by
    by_cases hi : i=v
    · simpa [replacePoint,hi] using hc
    · simpa [replacePoint,hi] using h.contained i
  core i := by
    by_cases hi : i=v
    · simpa [replacePoint,hi] using hcore
    · simpa [replacePoint,hi] using h.core i
  spread := spread_replace_clamped h.spread ht }

theorem radial_replace {C : SignedCycle} {q : ℝ} {v : Vertex}
    {p : SignedPoint} {t : ℝ} (h : ∀ i,(C.point i).Boundary q)
    (hp : p.Boundary q) : ∀ i,((replacePoint C v p t).point i).Boundary q := by
  intro i
  by_cases hi : i=v
  · simpa [replacePoint,hi] using hp
  · simpa [replacePoint,hi] using h i

end SignedCycle

namespace GPairOutput

def cycle {q : ℝ} (C : SignedCycle)
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    SignedCycle := replacePoint C G O.point O.theta

def witnesses {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    (O.cycle C).Witnesses where
  owner := ![O.hgOwner,O.gaOwner,w.owner A,w.owner B,w.owner T,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · simpa [cycle,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        replacePoint,word,delta,next,H,G,A,zeroFeasible] using sub_nonneg.mpr O.HG
    · simpa [cycle,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        replacePoint,word,delta,next,H,G,A,quarterFeasible] using sub_nonneg.mpr O.GA
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,A,B] using w.feasible A
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,B,T] using w.feasible B
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,T,D] using w.feasible T
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,D,E] using w.feasible D
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,E] using w.feasible E
  allowed i := by
    fin_cases i
    · rcases O.hg_allowed with he | he <;> simp [he,SignedCycle.normalOwners,H]
    · rcases O.ga_allowed with he | he <;> simp [he,SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [E] using w.allowed E

theorem zero_signs {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (h : C.ZeroSignImplications w)
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    (O.cycle C).ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hO : O.hgOwner=2 := by simpa [witnesses,H] using hj
    simpa [cycle,replacePoint,G] using O.canceling_normal hO
  · intro hj
    have hT : w.owner T=0 := by simpa [witnesses,T] using hj
    simpa [cycle,replacePoint,G,T] using h.TD_canceling hT

theorem necessary {q : ℝ} {C : SignedCycle} (h : C.Necessary q)
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    (O.cycle C).Necessary q :=
  SignedCycle.necessary_replace_clamped h O.sorted O.contained O.avoids O.frame_range

theorem variations {q : ℝ} {C : SignedCycle}
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    positiveVariation (O.cycle C).theta≤positiveVariation C.theta ∧
      negativeVariation (O.cycle C).theta≤negativeVariation C.theta := by
  rcases O.frame_range with he | hh
  · simp [cycle,replacePoint,he]
  · have hp := clamped_pair_variations (x := C.theta G) hh
    simp [positiveVariation,negativeVariation,Fin.sum_univ_succ,delta,next,
      cycle,replacePoint,H,G,A,Function.update_apply] at hp ⊢
    constructor <;> linarith [hp.1,hp.2]

theorem anchors {q : ℝ} {C : SignedCycle}
    (O : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A)) :
    AnchorsUnchanged C (O.cycle C) :=
  replacement_anchors_unchanged C (Or.inl rfl) O.point O.theta

end GPairOutput

namespace TPairOutput

def cycle {q : ℝ} (C : SignedCycle)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    SignedCycle := replacePoint C T O.point O.theta

def witnesses {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    (O.cycle C).Witnesses where
  owner := ![w.owner H,w.owner G,w.owner A,O.btOwner,O.tdOwner,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,G,T] using w.feasible H
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,G,A,T] using w.feasible G
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,A,B,T] using w.feasible A
    · simpa [cycle,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        replacePoint,word,delta,next,B,T,D,quarterFeasible] using sub_nonneg.mpr O.BT
    · simpa [cycle,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        replacePoint,word,delta,next,B,T,D,zeroFeasible] using sub_nonneg.mpr O.TD
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,T,D,E] using w.feasible D
    · simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
        SignedCycle.edge,word,delta,next,H,T,E] using w.feasible E
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · simpa [G] using w.allowed G
    · simpa [A] using w.allowed A
    · rcases O.bt_allowed with he | he <;> simp [he,SignedCycle.normalOwners,B]
    · rcases O.td_allowed with he | he <;> simp [he,SignedCycle.normalOwners,T]
    · simpa [D] using w.allowed D
    · simpa [E] using w.allowed E

theorem zero_signs {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (h : C.ZeroSignImplications w)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    (O.cycle C).ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hH : w.owner H=2 := by simpa [witnesses,H] using hj
    simpa [cycle,replacePoint,G,T] using h.HG_canceling hH
  · intro hj
    have hO : O.tdOwner=0 := by simpa [witnesses,T] using hj
    simpa [cycle,replacePoint,T] using O.canceling_normal hO

theorem necessary {q : ℝ} {C : SignedCycle} (h : C.Necessary q)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    (O.cycle C).Necessary q :=
  SignedCycle.necessary_replace_clamped h O.sorted O.contained O.avoids O.frame_range

theorem variations {q : ℝ} {C : SignedCycle}
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    positiveVariation (O.cycle C).theta≤positiveVariation C.theta ∧
      negativeVariation (O.cycle C).theta≤negativeVariation C.theta := by
  rcases O.frame_range with he | hh
  · simp [cycle,replacePoint,he]
  · have hp := clamped_pair_variations (x := C.theta T) hh
    simp [positiveVariation,negativeVariation,Fin.sum_univ_succ,delta,next,
      cycle,replacePoint,B,T,D,Function.update_apply] at hp ⊢
    constructor <;> linarith [hp.1,hp.2]

theorem anchors {q : ℝ} {C : SignedCycle}
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    AnchorsUnchanged C (O.cycle C) :=
  replacement_anchors_unchanged C (Or.inr rfl) O.point O.theta

end TPairOutput

/-- The two pair moves compose: the cycle after both satisfies `Necessary`, lies on the boundary,
has a strict spread, the anchors of `C`, variations at most those of `C`, and witnesses with the
sign implications. Its order is proved separately, from the geometry. -/
theorem compose_primary_pair_outputs {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hr : ∀ i,(C.point i).Boundary q)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hstrict : C.StrictSpread)
    (OG : GPairOutput q (C.point H) (C.point A) (C.theta H) (C.theta G) (C.theta A))
    (OT : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    let D := replacePoint (replacePoint C G OG.point OG.theta) T OT.point OT.theta
    D.Necessary q ∧ (∀ i,(D.point i).Boundary q) ∧
      D.StrictSpread ∧ AnchorsUnchanged C D ∧
      positiveVariation D.theta≤positiveVariation C.theta ∧
      negativeVariation D.theta≤negativeVariation C.theta ∧
      ∃ wD : D.Witnesses, D.ZeroSignImplications wD := by
  let CG := OG.cycle C
  have hnG : CG.Necessary q := OG.necessary hn
  have hrG : ∀ i,(CG.point i).Boundary q :=
    SignedCycle.radial_replace hr OG.boundary
  have hsG : CG.StrictSpread :=
    SignedCycle.strictSpread_replace_clamped (v := G) (a := H) (b := A) hstrict OG.frame_range
  let OT' : TPairOutput q (CG.point B) (CG.point D)
      (CG.theta B) (CG.theta T) (CG.theta D) := OT
  have hnT := OT'.necessary hnG
  have hrT := SignedCycle.radial_replace (v := T) (t := OT'.theta) hrG OT'.boundary
  have hsT := SignedCycle.strictSpread_replace_clamped (v := T) (a := B) (b := D)
    (p := OT'.point) hsG OT'.frame_range
  have ha := OG.anchors.trans OT'.anchors
  have hp := (OT'.variations.1).trans OG.variations.1
  have hm := (OT'.variations.2).trans OG.variations.2
  let wG := OG.witnesses w
  let wD := OT'.witnesses wG
  have hzD := OT'.zero_signs wG (OG.zero_signs w hz)
  exact ⟨hnT,hrT,hsT,ha,hp,hm,wD,hzD⟩

namespace SignedCycle.BoundaryInput

/-- When G–A is already separated along the axis zero, the pair move of G that leaves G in place;
nothing is assumed of the axis one. -/
def hardG {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hGA : I.cycle.Feasible G 0) :
    GPairOutput q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A) where
  point := I.cycle.point G
  theta := I.cycle.theta G
  hgOwner := I.witnesses.owner H
  gaOwner := 0
  hg_allowed := by simpa [SignedCycle.normalOwners,H] using I.witnesses.allowed H
  ga_allowed := Or.inl rfl
  sorted := I.necessary.sorted G
  contained := I.necessary.contained G
  avoids := I.necessary.core G
  boundary := I.radial G
  HG := by
    have h := I.witnesses.feasible H
    change 0≤I.cycle.slack H (I.witnesses.owner H) at h
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,H,G,zeroFeasible]
      using sub_nonneg.mp h
  GA := by
    change 0≤I.cycle.slack G 0 at hGA
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,G,A,quarterFeasible]
      using sub_nonneg.mp hGA
  canceling_normal := I.zero_signs.HG_canceling
  frame_range := Or.inl rfl
  terminal := Or.inl rfl

/-- When B–T is already separated along the axis two, the pair move of T that leaves its point
and frame in place. -/
def hardT {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hBT : I.cycle.Feasible B 2) :
    TPairOutput q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D) where
  point := I.cycle.point T
  theta := I.cycle.theta T
  btOwner := 2
  tdOwner := I.witnesses.owner T
  bt_allowed := Or.inl rfl
  td_allowed := by simpa [SignedCycle.normalOwners,T] using I.witnesses.allowed T
  sorted := I.necessary.sorted T
  contained := I.necessary.contained T
  avoids := I.necessary.core T
  boundary := I.radial T
  BT := by
    change 0≤I.cycle.slack B 2 at hBT
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,B,T,quarterFeasible]
      using sub_nonneg.mp hBT
  TD := by
    have h := I.witnesses.feasible T
    change 0≤I.cycle.slack T (I.witnesses.owner T) at h
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,T,D,zeroFeasible]
      using sub_nonneg.mp h
  canceling_normal := I.zero_signs.TD_canceling
  frame_range := Or.inl rfl
  terminal := Or.inl rfl

end SignedCycle.BoundaryInput
end SquaresInCircles.Eight
