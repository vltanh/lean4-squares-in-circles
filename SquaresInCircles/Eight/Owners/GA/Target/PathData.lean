module

public import SquaresInCircles.Eight.Owners.GA.Target.Core
public import SquaresInCircles.Eight.Owners.GA.Target.OuterSupport
public import SquaresInCircles.Eight.Owners.GA.Target.ZeroErrors

/-!
# Eight squares: the high GA axis and the three-edge force collection

The two zero projections keep their owner and rotating endpoint. The assumption that the target is
large rules out GA2 and a nonpositive GA3 directly, before any support reduction
(`original_GA_domain`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary FrameCircleArc GlobalZeroSign GlobalOuterAnchor

def pathCharge (h b : State) (v u w : ℝ) : ℝ :=
  Real.pi/2+v+u+w+unsigned h+unsigned b

theorem original_GA_domain (g a : State) (p : Bool) {u : ℝ}
    (hu : |u|≤frameCap) (hg : transverse g≤0) (ha : (1/2:ℝ)≤transverse a)
    (hGA : g.Feasible a (rightOwner p) (Real.pi/2+u)) :
    p=true ∧ 0<u ∧ GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u := by
  have hay : transverse a=a.b := transverse_of_nonneg a (by linarith)
  have hab : (1/2:ℝ)≤a.b := by simpa only [hay] using ha
  have hm := (right_margin g a p hu hg).1 hGA
  have hp : p=true := by
    cases hp : p
    · have hnorm := GlobalQuarterSign.state_norm_sq g
      have hproj := FrameCoreArc.projection_lt (a:=g.b) (b:=g.a)
        (by norm_num : (0:ℝ)<283/200) (by nlinarith) u
      simp only [rightProjection,hp,Bool.false_eq_true,ite_false,hay] at hm
      have hw := width_ge_one hu
      linarith
    · rfl
  rw [hp] at hm
  simp only [rightProjection,ite_true,hay] at hm
  have hpos : 0<u := by
    by_contra! hn
    have hz : -u∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs u).trans hu⟩
    have ht := CommonQuarter.positive_trig (x:=-u) (by simpa only [frameCap] using hz)
    have hcos : 0≤Real.cos (-u) := by linarith [ht.1]
    have hA : 1≤a.a+1/2 := by linarith [primary_lower a]
    have hB : 1≤a.b+1/2 := by linarith
    have hsine := mul_le_mul_of_nonneg_right hA ht.2.2.1
    have hcosine := mul_le_mul_of_nonneg_right hB hcos
    have he : GlobalOuterAnchor.width u=(1+Real.cos (-u)+Real.sin (-u))/2 := by
      have heq : u=-(-u) := by ring
      conv_lhs => rw [heq]
      rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    have hsin : Real.sin u=-Real.sin (-u) := by simp
    have hcos' : Real.cos u=Real.cos (-u) := by simp
    rw [he,hsin,hcos'] at hm
    have hsum := ht.2.2.2.2.2
    have hga := (coordinates g).2.1
    nlinarith
  exact ⟨hp,hpos,hm⟩

theorem zero_error_separator (h g : State) (p : Bool) {v : ℝ}
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v) :
    zeroError (if p then h else g) v≤v+m*(h.b+g.b-1) := by
  cases p <;> dsimp [GlobalEH.zeroProjection,zeroError,m] at * <;> nlinarith

theorem path_floor (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hb : b.branch.type≠0)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+u+2*m-m*g.b-m*a.b+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hH := marker_floor h hh
  have hB := marker_floor b hb
  have hzH := zero_error_separator h g p hHG
  have hzA := zero_error_separator a b r hAB
  dsimp [pathCharge]
  linarith

theorem outer_domain (g a : State) (hg : g.branch.type≠0) (ha : a.branch.type≠0)
    (hb : (1/2:ℝ)≤a.b) {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) : Outer.Domain u := by
  have hchartA := state_outer_chart a ha
  have hchartG := state_outer_chart g hg
  have hhalf : (1/2:ℝ)∈Icc 0 c0 := ⟨by norm_num,by linarith [c0_bounds.1]⟩
  have haA := A_antitone hhalf hchartA.2 hb
  rw [Outer.A_half,←hchartA.1] at haA
  have hgA := (A_bounds hchartG.2).2
  rw [←hchartG.1] at hgA
  have ht := transport_trig hu
  have hA := mul_le_mul_of_nonneg_right haA ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right hb (by linarith [ht.1] : 0≤Real.cos u)
  dsimp [GlobalOuterAnchor.width] at hGA
  rw [abs_of_nonneg ht.2.2.1] at hGA
  refine ⟨hu,?_⟩
  dsimp [Outer.K,Outer.P]
  nlinarith

theorem outer_force (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hg : g.branch.type≠0)
    (ha : a.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hu : u∈Icc 0 frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+u+m*(2-Outer.Y u)+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hd := outer_domain g a hg ha haB hu hGA
  have hp := Outer.weight_pos hd
  have hfloor := path_floor (u:=u) h g a b p r hh hb hHG hAB
  have hG := state_support g (Outer.weight u) m
  have hA := Outer.target_support a ha haB hd
  have hsep := mul_le_mul_of_nonneg_left hGA hp.le
  have hopt := Outer.optimizing_identity hd
  have ht := transport_trig hu
  have hw : GlobalOuterAnchor.width u=(1+Real.cos u+Real.sin u)/2 := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg ht.2.2.1]
  have hcollect : Outer.weight u*GlobalOuterAnchor.width u+(Outer.weight u+m)/2-
      (Outer.weight u*(Outer.S-1/2)*Real.sin u+(m-Outer.weight u*Real.cos u)/2)=
        Outer.weight u*Outer.K u := by
    rw [hw]
    dsimp [Outer.K,Outer.P]
    ring
  nlinarith only [hfloor,hG,hA,hsep,hopt,hcollect]

theorem core_force (h g a b : State) (p r : Bool) {v u w : ℝ}
    (hh : h.branch.type≠0) (hb : b.branch.type≠0) (haB : (1/2:ℝ)≤a.b)
    (hu : u∈Icc 0 frameCap)
    (hHG : GlobalOuterAnchor.width v≤GlobalEH.zeroProjection h g p v)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u)
    (hAB : GlobalOuterAnchor.width w≤GlobalEH.zeroProjection a b r w) :
    Real.pi/2+Core.base+Core.error a u+
      zeroError (if p then h else g) v+zeroError (if r then a else b) w≤
        pathCharge h b v u w := by
  have hfloor := path_floor (u:=u) h g a b p r hh hb hHG hAB
  have hsep := Core.error_separator g a hu hGA
  have hG := state_support g Core.weight m
  have hB := mul_le_mul_of_nonneg_left haB
    (by norm_num [Core.weight,m] : 0≤Core.weight-m)
  dsimp [Core.base,Core.weight,m] at *
  linarith

end SquaresInCircles.Eight.GlobalGA.Target
