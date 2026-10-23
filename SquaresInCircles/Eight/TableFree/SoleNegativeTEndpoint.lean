module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTOriginalBlocks
public import SquaresInCircles.Eight.TableFree.SoleNegativeTContinuation
public import SquaresInCircles.Eight.TableFree.SolePositiveTEndpoint
public import SquaresInCircles.Eight.TableFree.FlatTStress

/-!
# Negative-T endpoint supports on the unchanged source cycle

Uncompiled source. The flat T coordinate is the one captured from the
original negative primary. H/A/B use their original circle supports;
D uses the sorted support at the same q. The sorted-baseline reserve
is inserted only after the fixed-coordinate G/E split has reached an
endpoint. No packing at an auxiliary scalar endpoint is asserted.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTEndpoint
open Candidate SignedStress SecondaryEStress SoleResiduals
open SoleTScalarModel SolePositiveTSplitModel SoleNegativeTCoefficients
open SoleNegativeTOrdinaryData SoleNegativeTOriginalBlocks
open ActualCoreEBlocks ActualOrdinaryBlocks PositiveAngularEnvelope

def faceForces (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (n (face f atG) t 0) (k f t 0) (ell f t 0)
    (SoleNegativeTSplit.btWeight f td t s) (SoleNegativeTSplit.tdWeight f td t s)
    (p (face f atG) t 0) (lambda f)

def blockSupport (B : Block) (R : ℝ) : ℝ :=
  R*pairNorm B.alpha B.beta (B.u+B.v)-(B.alpha*phi B.u+B.beta*phi B.v)/2

def anchorSupport (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  blockSupport (blocks C ab f atG td t s 0) (Real.sqrt q)+
  blockSupport (blocks C ab f atG td t s 1) (Real.sqrt q)+
  blockSupport (blocks C ab f atG td t s 2) (Real.sqrt q)+
  ActualSortedSupport.support q
    (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)))
    (dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f)))

def correction (f : Family) (atG : Bool) (q t : ℝ) : ℝ :=
  ActualSortedSupport.full q (p (face f atG) t 0) (c f t 0)-
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0)

def gain (f : Family) (atG td : Bool) (q t s : ℝ) : ℝ :=
  if td then c f t 0*((1/Real.cos s-1)/2+(13/12)*Real.tan s)-
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0/Real.cos s)+
    ActualSortedSupport.support q (p (face f atG) t 0) (c f t 0)
  else FlatTStress.secantCharge (Real.sqrt q) (c f t 0) (ell f t 0) s

theorem face_forces_eq (C : SignedCycle) (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ) :
    SoleNegativeTSplit.forceData C ab f td t s (x (face f atG) t 0) (e (face f atG) t 0)=
      faceForces C ab f atG td t s := rfl

theorem circle_supports {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (C : SignedCycle) (f : Family) (atG td : Bool) (R t s : ℝ) :
    signedSupport R 1 (faceForces C ab f atG td t s H)=
      blockSupport (blocks C ab f atG td t s 0) R ∧
    signedSupport R 1 (faceForces C ab f atG td t s A)=
      blockSupport (blocks C ab f atG td t s 1) R ∧
    signedSupport R (-1) (faceForces C ab f atG td t s B)=
      blockSupport (blocks C ab f atG td t s 2) R := by
  refine ⟨?_,?_,?_⟩
  · rw [faceForces,SoleEStress.force_H (SolePositiveTSplitSupport.ehOwner_cases f),
      rotatedPair_signedSupport]
    simp [blockSupport,blocks,SoleEStress.blocks,pairNorm_symm]
    ring
  · rw [faceForces,SoleEStress.force_A hab,rotatedPair_signedSupport]
    simp [blockSupport,blocks,SoleEStress.blocks,pairNorm_symm]
    ring
  · rw [faceForces,SoleEStress.force_B hab (SolePositiveTOriginalBlocks.btOwner_cases td),
      reflected_rotatedPair_signedSupport]
    simp [blockSupport,blocks,SoleEStress.blocks,pairNorm_symm]
    ring

theorem D_force {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) (t s : ℝ)
    (hflat : td=false → delta C.theta T=0) :
    faceForces C ab f atG td t s D=
      (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)),
        -(dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f)))) := by
  rw [faceForces,SoleEStress.force_D (SolePositiveTOriginalBlocks.tdOwner_cases td)
    (SolePositiveTSplitSupport.deOwner_cases f)]
  cases td <;> simp_all [tdOwner,rotatedPair,dCoefficient]
  <;> ext <;> ring

theorem T_work {C : SignedCycle} (ab : Fin 4) (f : Family) (atG td : Bool) {t s : ℝ}
    (hs : s∈Icc 0 frameCap) (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12) :
    work (faceForces C ab f atG td t s T) (C.point T)= -(7/12)*c f t 0*Real.tan s := by
  have hcos : Real.cos s≠0 := ne_of_gt (by linarith [(transport_trig hs).1])
  rw [faceForces,SoleEStress.force_T]
  cases td
  · exact negative_BT_work hcos (by simpa [tPrimary] using hsource) hcore
  · exact negative_TD_work hcos (by simpa [tPrimary] using hsource) hcore

theorem fixedWork_le {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12)
    (hflat : td=false → delta C.theta T=0) :
    SoleNegativeTSplit.fixedWork C ab f td t s (x (face f atG) t 0) (e (face f atG) t 0)≤
      anchorSupport C ab f atG td q t s-(7/12)*c f t 0*Real.tan s := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by
    simpa [Real.sq_sqrt hq0] using hC.contained
  have hH := work_le_signed_support (Real.sqrt_nonneg q) (hc H) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.H_nonneg]) (faceForces C ab f atG td t s H)
  have hA := work_le_signed_support (Real.sqrt_nonneg q) (hc A) (Or.inl rfl)
    (by simp [abs_of_nonneg hn.A_nonneg]) (faceForces C ab f atG td t s A)
  have hB := work_le_signed_support (Real.sqrt_nonneg q) (hc B) (Or.inr rfl)
    (by simp [abs_of_nonpos hn.B_nonpos]) (faceForces C ab f atG td t s B)
  obtain ⟨hHs,hAs,hBs⟩ := circle_supports hab C f atG td (Real.sqrt q) t s
  rw [hHs] at hH
  rw [hAs] at hA
  rw [hBs] at hB
  have hp := p_ge_one atG ht
  have hcg := d_coefficient_ge td ht hs
  have hpc := p_half_c atG ht
  have hsmall := (ordinary_small (de:=deOwner f) (eh:=ehOwner f)
    (fun i => hC.spread (next i) i)).1
  have hD := ActualSortedSupport.actual_negative_support hq0 (hC.sorted D) hn.D_nonpos
    (hC.contained D) (SoleNegativeTDSupport.force_sum_positive
      (show 0<p (face f atG) t 0 by linarith)
      (show p (face f atG) t 0/2≤dCoefficient f td t s by linarith) hsmall).le
  have hDw : work (faceForces C ab f atG td t s D) (C.point D)≤
      ActualSortedSupport.support q
        (p (face f atG) t 0*Real.cos (ordinaryDE C (deOwner f)))
        (dCoefficient f td t s+p (face f atG) t 0*Real.sin (ordinaryDE C (deOwner f))) := by
    rw [D_force ab f atG td t s hflat]
    simpa [work] using hD
  have hT := T_work ab f atG td (short_small hs) hsource hcore
  simp only [SoleNegativeTSplit.fixedWork,face_forces_eq]
  dsimp [anchorSupport]
  linarith

theorem secantCharge_eq {q c s : ℝ} (hc : 0<c) (hs : s∈Icc 0 frameCap) (a : ℝ) :
    FlatTStress.secantCharge (Real.sqrt q) c a s=c*GlobalGA.secantGain q (a/c) s := by
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [GlobalGA.secantGain_eq_secant_expression q (a/c) hcos]
  have hN : pairNorm a (c/Real.cos s) 0=c*Real.sqrt ((1/Real.cos s)^2+(a/c)^2) := by
    simpa only [div_eq_mul_inv,one_mul,add_comm] using FlatTStress.zero_norm_scale hc a (1/Real.cos s)
  have hZ : pairNorm a c 0=c*Real.sqrt (1+(a/c)^2) := by
    simpa only [mul_one,one_pow,add_comm] using FlatTStress.zero_norm_scale hc a 1
  dsimp [FlatTStress.secantCharge]
  rw [hN,hZ]
  ring

theorem gain_strict {f : Family} (atG td : Bool) {q t s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f)
    (hs : s∈shortDomain td) (hs0 : 0<s) : (21/20)*c f t 0*s<gain f atG td q t s := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hp := p_ge_one atG ht
  cases td
  · have hs' : s∈Ioc 0 (9/100:ℝ) := ⟨hs0,by simpa [shortDomain] using hs.2⟩
    have hr : 117/200≤ell f t 0/c f t 0 := (le_div_iff₀ hc).2 (B_ratio atG ht)
    have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
    have hh := mul_lt_mul_of_pos_left (SoleNegativeTGain.BT_strict hq0 hQU hr hs') hc
    simpa only [gain,if_false,secantCharge_eq hc (short_small hs),mul_assoc,mul_left_comm,mul_comm] using hh
  · have hs' : s∈Ioc 0 (3/10:ℝ) := ⟨hs0,by simpa [shortDomain] using hs.2⟩
    exact SoleNegativeTDSupport.TD_gain hQL hQU (by linarith) hc hs'

theorem correction_lower {f : Family} (atG : Bool) {q t : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap) (ht : t∈domain f) :
    SoleNegativeTContinuation.correction f atG t≤correction f atG q t := by
  have hp := p_ge_one atG ht
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  by_cases hf : f=.ehMiddle ∨ f=.ehHigh
  · have hdom := correction_domain atG ht hf
    simpa only [SoleNegativeTContinuation.correction,if_pos hf,correction] using
      SoleNegativeTDSupport.sorted_correction hQL hQU (by linarith) hc.le hdom.1 hdom.2
  · have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
    have hh := ActualSortedSupport.support_le_full hq0
      (show 0≤p (face f atG) t 0+c f t 0 by linarith)
    simp only [SoleNegativeTContinuation.correction,if_neg hf,correction]
    linarith

theorem decomposition {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) (q M : ℝ)
    {t s : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hsource : tPrimary C td= -s) (hflat : td=false → delta C.theta T=0)
    (ha : ∀ i,|delta C.theta i|≤frameCap) :
    SoleNegativeTSplit.variableDemand C f td t s (x (face f atG) t 0) (e (face f atG) t 0)-
      anchorSupport C ab f atG td q t s+(7/12)*c f t 0*Real.tan s-
      k f t 0*sigma (Real.sqrt q) (g f t)*Real.sin (x (face f atG) t 0)-
      SolePositiveTEndpoint.eWork (face f atG) (Real.sqrt q) M t 0=
    SolePositiveTOrdinaryData.baseline (face f atG) (Real.sqrt q) (M+1/2) t 0+
      correction f atG q t+gain f atG td q t s+ordinary C ab f atG td q t s := by
  have hx := (split_angles (face f atG) ht (zero_mem ht)).2.1
  have he := (split_angles (face f atG) ht (zero_mem ht)).2.2
  have hWx := edgeWidth_positive_formula hx
  have hWe := edgeWidth_positive_formula he
  have hWs := edgeWidth_negative_formula (short_small hs)
  have hcos : Real.cos s≠0 := ne_of_gt (by linarith [(transport_trig (short_small hs)).1])
  cases htd : td
  · have hδ : delta C.theta B= -s := by simpa [tPrimary,htd] using hsource
    have hT := hflat htd
    rcases hab with rfl | rfl <;> cases f <;>
      simp [SoleNegativeTSplit.variableDemand,anchorSupport,blockSupport,blocks,
        SoleEStress.blocks,ordinary,contribution,SoleNegativeTDSupport.increment,
        Block.increment,correction,gain,FlatTStress.secantCharge,
        SolePositiveTOrdinaryData.baseline,SolePositiveTEndpoint.eWork,
        ActualSortedSupport.full,eTerm,primaryCoefficient,primarySupport,sigma,
        SoleEndpointSupport.highWork,SoleTScalarModel.first,SoleTScalarModel.second,
        Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,
        SoleNegativeTSplit.btWeight,SoleNegativeTSplit.tdWeight,dCoefficient,
        ordinaryDE,ordinaryEH,nWeight,n,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,face,htd,
        hδ,hT,hWx,hWe,hWs,width_eq (ha H),width_eq (ha A),width_eq (ha D),width_eq (ha E),
        phi,psi_zero,Real.tan_eq_sin_div_cos,pairNorm_symm] <;>
      field_simp [hcos] <;> ring
  · have hδ : delta C.theta T= -s := by simpa [tPrimary,htd] using hsource
    rcases hab with rfl | rfl <;> cases f <;>
      simp [SoleNegativeTSplit.variableDemand,anchorSupport,blockSupport,blocks,
        SoleEStress.blocks,ordinary,contribution,SoleNegativeTDSupport.increment,
        Block.increment,correction,gain,FlatTStress.secantCharge,
        SolePositiveTOrdinaryData.baseline,SolePositiveTEndpoint.eWork,
        ActualSortedSupport.full,eTerm,primaryCoefficient,primarySupport,sigma,
        SoleEndpointSupport.highWork,SoleTScalarModel.first,SoleTScalarModel.second,
        Fin.sum_univ_succ,btOwner,tdOwner,deOwner,ehOwner,
        SoleNegativeTSplit.btWeight,SoleNegativeTSplit.tdWeight,dCoefficient,
        ordinaryDE,ordinaryEH,nWeight,n,m,deWeight,ehWeight,p,lambda,tiltedE,isDE,face,htd,
        hδ,hWx,hWe,hWs,width_eq (ha H),width_eq (ha A),width_eq (ha B),width_eq (ha D),width_eq (ha E),
        phi,psi_zero,Real.tan_eq_sin_div_cos,pairNorm_symm] <;>
      field_simp [hcos] <;> ring

theorem value_lower {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (ht : t∈domain f) (hs : s∈shortDomain td)
    (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hsource : tPrimary C td= -s) (hcore : (C.point T).a=7/12)
    (hflat : td=false → delta C.theta T=0) :
    SoleNegativeTContinuation.baseline f atG q t+correction f atG q t+
      gain f atG td q t s+ordinary C ab f atG td q t s≤
      SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s (x (face f atG) t 0) := by
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hx : x (face f atG) t 0∈Icc 0 t := by
    cases atG <;> simp [x,face] <;> exact (angle ht).1
  have he : t-x (face f atG) t 0=e (face f atG) t 0 := by cases atG <;> simp [x,e,face]
  have hwork := fixedWork_le atG td hab hQL ht hs hC hn hsource hcore hflat
  have hE := SolePositiveTEndpoint.E_support (face f atG) (Real.sqrt_nonneg q) ht (zero_mem ht)
    (hC.sorted E) (by simpa [Real.sq_sqrt hq0] using hC.contained E)
    (M:=axisCoordinate q)
  have hid := decomposition atG td q (axisCoordinate q) hab ht hs hsource hflat
    (fun i => hC.spread (next i) i)
  have haxis : axisCoordinate q+1/2=Real.sqrt (q-1/4) := by simp [axisCoordinate]
  rw [haxis] at hid
  rw [SoleNegativeTSplit.value_eq_stress td (Real.sqrt q) (axisCoordinate q) hab ht hx hn,he]
  dsimp [SoleNegativeTSplit.stress,SoleNegativeTContinuation.baseline]
  linarith

theorem endpoint_positive {C : SignedCycle} {ab : Fin 4} {f : Family} (atG td : Bool) {q t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hQL : qLow≤q) (hQU : q≤qTrial)
    (ht : t∈domain f) (hs : s∈shortDomain td) (hs0 : 0<s)
    (hC : C.Necessary q) (hn : C.NormalAnchors) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f)
    (hsource : tPrimary C td= -s) (htotal : delta C.theta G+ePrimary C f=t)
    (hcore : (C.point T).a=7/12) (hflat : td=false → delta C.theta T=0) :
    0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s
      (x (face f atG) t 0) := by
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hs3 : s∈Icc 0 (3/10:ℝ) := by
    cases td <;> norm_num [shortDomain] at hs ⊢ <;> exact ⟨hs.1,by linarith [hs.2]⟩
  have hJ := correction_lower atG hQL hcap ht
  have hgain := gain_strict atG td hQL hcap ht hs hs0
  have hvalue := value_lower atG td hab hQL ht hs hC hn hsource hcore hflat
  rcases le_total s t with hst | hts
  · have hpure (i : Fin 4) (hi : Used f i) :
        -SoleNegativeTContinuation.baseline f atG q t-SoleNegativeTContinuation.correction f atG t-
          (21/20)*c f t 0*s≤oldV f atG (Real.sqrt q) t (t-s) i := by
      have hh := SoleNegativeTContinuation.negative_positive atG hQL hQU ht hs3 hst i hi
      dsimp [SoleNegativeTContinuation.interpolation] at hh
      linarith
    have hordinary := negative_original atG td hab hQL hcap ht hs hst ha hflat hvar hG hE hsource htotal hpure
    linarith
  · have hp := SoleNegativeTContinuation.positive_surplus_positive atG hQU ht hs3 hts
    have hordinary := positive_original atG td hab hQL hcap ht hs hts ha hflat hvar hG hE hsource htotal
    linarith

end SquaresInCircles.Eight.TableFree.SoleNegativeTEndpoint
