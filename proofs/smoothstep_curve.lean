/-
This spiral uses a smoothstep-based curvature function,
providing a $G^\infty$ continuous transition from tangent to circular arc.

The heading angle is given by:

$$\theta(l) = \frac{1}{R} \int_0^l F(\tfrac{v}{L})\,dv$$

where:
- $F(z) = \dfrac{\int_0^z G(t)\,dt}{\int_0^1 G(t)\,dt}$
- $G(t) = e^{\left(1-\tfrac{1}{t(1-t)}\right)}$
- $l$ = arc length along the curve
- $L$ = total length of the transition curve
- $R$ = radius of the circular arc

The Cartesian coordinates of the spiral are then:
$$x(l) = \int_0^l \cos\!\big(\theta(v)\big)\,dv,
\quad
y(l) = \int_0^l \sin\!\big(\theta(v)\big)\,dv$$
with initial conditions $x(0)=0,\ y(0)=0,\ \theta(0)=0$.

The curvature is:
$$\kappa(s) = R F\left(\frac{s}{L}\right)$$
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Filter
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Filter.Tendsto
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

noncomputable
section SmoothstepCore

open scoped ContDiff Topology
open MeasureTheory

-- Fundamental: the primitive z ↦ ∫_{0..z} f is C^∞ on [0,1] if f is C^∞ on [0,1]
lemma primitive_is_C_inf_on_unitInterval
  (f : ℝ → ℝ) (hfinf : ContDiffOn ℝ ∞ f unitInterval) :
  ContDiffOn ℝ ∞ (fun z => ∫ t in (0)..z, f t) unitInterval := by
  classical
  have h_deriv_within : ∀ x ∈ unitInterval,
      HasDerivWithinAt (fun z => ∫ t in (0)..z, f t) (f x) unitInterval x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hint : IntervalIntegrable f volume 0 x := by
      have hcont' : ContinuousOn f (Set.Icc 0 x) :=
        hfinf.continuousOn.mono (Set.Icc_subset_Icc le_rfl hx.2)
      simpa using
        (ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
          (u := f) (a := 0) (b := x) (h := hx0) hcont')
    haveI : Fact (x ∈ Set.Icc (0 : ℝ) 1) := ⟨hx.1, hx.2⟩
    haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
      simpa [unitInterval] using
        (inferInstance : intervalIntegral.FTCFilter x (𝓝[Set.Icc (0 : ℝ) 1] x)
          (𝓝[Set.Icc (0 : ℝ) 1] x))
    have hmeas : StronglyMeasurableAtFilter f (𝓝[unitInterval] x) volume := by
      have hmeasSet : MeasurableSet unitInterval := by
        simp [unitInterval, isClosed_Icc.measurableSet]
      exact hfinf.continuousOn.stronglyMeasurableAtFilter_nhdsWithin (hs := hmeasSet) x
    simpa using
      (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := x)
        (f := f) hint hmeas (hfinf.continuousOn.continuousWithinAt hx))
  have hUD : UniqueDiffOn ℝ unitInterval := by
    simpa [unitInterval] using uniqueDiffOn_Icc_zero_one
  have h_diff : DifferentiableOn ℝ (fun z => ∫ t in (0)..z, f t) unitInterval :=
    fun x hx => (h_deriv_within x hx).differentiableWithinAt
  have h_deriv_eq : ∀ x ∈ unitInterval,
      derivWithin (fun z => ∫ t in (0)..z, f t) unitInterval x = f x := by
    intro x hx
    have hsx : UniqueDiffWithinAt ℝ unitInterval x := by
      simpa [unitInterval] using (uniqueDiffOn_Icc_zero_one x ⟨hx.1, hx.2⟩)
    simpa using (HasDerivWithinAt.derivWithin (h_deriv_within x hx) hsx)
  have hC : ContDiffOn ℝ ∞
      (fun z => derivWithin (fun z => ∫ t in (0)..z, f t) unitInterval z)
      unitInterval :=
    (contDiffOn_congr (s := unitInterval)
      (f₁ := fun z => derivWithin (fun z => ∫ t in (0)..z, f t) unitInterval z)
      (f := f) h_deriv_eq).mpr hfinf
  have hcrit := (contDiffOn_infty_iff_derivWithin (𝕜 := ℝ)
    (s₂ := unitInterval) (f₂ := fun z => ∫ t in (0)..z, f t) hUD)
  exact hcrit.mpr ⟨h_diff, hC⟩

-- Helper: rewrite uIoc integral as intervalIntegral on [0,1]
lemma uIoc_to_intervalIntegral_on_unit
  (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ unitInterval) :
  (∫ t in Set.uIoc 0 z, f t) = ∫ t in (0)..z, f t := by
  have hz0 : (0 : ℝ) ≤ z := hz.1
  -- intervalIntegral gives ∫(0..z) = ∫_{Ioc 0 z}
  have h := (intervalIntegral.integral_of_le (μ := volume)
    (f := f) (a := (0 : ℝ)) (b := z) hz0)
  -- rewrite uIoc to Ioc using 0 ≤ z, then flip sides
  simpa [Set.uIoc, hz0] using h.symm

-- Generic normalized primitive and curvature based on a bump-like G
namespace Smooth

def FNum (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

def FDen (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

def F (G : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z ≤ 0 then 0 else if 1 ≤ z then 1 else FNum G z / FDen G

lemma FNum_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (FNum G) unitInterval := by
  classical
  let P : ℝ → ℝ := fun z => ∫ t in (0)..z, G t
  have hP : ContDiffOn ℝ ∞ P unitInterval :=
    primitive_is_C_inf_on_unitInterval G hG
  have h_congr : ∀ z ∈ unitInterval, FNum G z = P z := by
    intro z hz; simpa [FNum, P] using uIoc_to_intervalIntegral_on_unit G hz
  exact ContDiffOn.congr_mono hP h_congr fun ⦃a⦄ a ↦ a

lemma FDen_pos
  {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  0 < FDen G := by
  have hposI' : 0 < ∫ x in (0)..(1), G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hint hpos (by norm_num)
  have hposI : 0 < ∫ x in Set.Ioc 0 1, G x := by
    simpa [intervalIntegral.integral_of_le (μ := volume)
      (f:=G) (a:=0) (b:=1) (by norm_num : (0:ℝ) ≤ 1)] using hposI'
  simpa [FDen, Set.uIoc, le_rfl] using hposI

lemma FDen_ne_zero {G : ℝ → ℝ}
  (h : 0 < FDen G) : FDen G ≠ 0 := h.ne'

lemma F_eq_ratio_on_unit {G : ℝ → ℝ} {z : ℝ} (hz : z ∈ unitInterval)
  (hden : FDen G ≠ 0) : F G z = FNum G z / FDen G := by
  rcases hz with ⟨hz0, hz1⟩
  by_cases h0 : z = 0
  · subst h0; simp [F, FNum, FDen, Set.uIoc]
  by_cases h1 : z = 1
  · subst h1
    have hdenIoc : (∫ t in Set.Ioc 0 1, G t) ≠ 0 := by
      simpa [FDen, Set.uIoc, le_rfl] using hden
    simp [F, FNum, FDen, Set.uIoc, hdenIoc]
  simp [F, not_le.mpr (lt_of_le_of_ne hz0 (by simpa [eq_comm] using h0)),
    not_le.mpr (lt_of_le_of_ne hz1 (by simpa using h1))]

lemma F_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) (hden : FDen G ≠ 0) :
  ContDiffOn ℝ ∞ (F G) unitInterval := by
  have hNum := FNum_contDiffOn (G := G) hG
  have h : ContDiffOn ℝ ∞ (fun x => FNum G x / FDen G) unitInterval :=
    ContDiffOn.div_const hNum (FDen G)
  exact (contDiffOn_congr (s := unitInterval) (f₁ := F G)
    (f := fun x => FNum G x / FDen G)
    (by intro x hx; simpa using (F_eq_ratio_on_unit (G := G) hx hden))).mpr h

def kappa (G : ℝ → ℝ) (s R L : ℝ) : ℝ := R * F G (s / L)

lemma kappa_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hden : FDen G ≠ 0) (R L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappa G s R L) (Set.Icc 0 L) := by
  -- map Set.Icc 0 L to unitInterval via s ↦ s / L
  have hmap : ∀ {s}, s ∈ Set.Icc 0 L → s / L ∈ unitInterval := by
    intro s hs; rcases hs with ⟨hs0, hsL⟩
    exact ⟨div_nonneg hs0 (le_of_lt hL), by
      have hLne : L ≠ 0 := ne_of_gt hL
      simpa [div_self hLne] using div_le_div_of_nonneg_right hsL (le_of_lt hL)⟩
  have hF : ContDiffOn ℝ ∞ (F G) unitInterval := F_contDiffOn (G := G) hG hden
  have hcomp : ContDiffOn ℝ ∞ (fun s => F G (s / L)) (Set.Icc 0 L) :=
    (hF.comp (contDiffOn_id.div_const (c := L)) (by intro s hs; exact hmap hs))
  simpa [kappa] using contDiffOn_const.mul hcomp

end Smooth

end SmoothstepCore

noncomputable
section smoothstep_curve_1

open scoped ContDiff Topology

def denom_fn (t : ℝ) : ℝ := t * (1 - t)

lemma denom_is_C_inf : ContDiffOn ℝ ∞ denom_fn unitInterval := by
  exact contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)

lemma denom_contDiff : ContDiff ℝ ∞ denom_fn := by
  simpa using (contDiff_id.mul (contDiff_const.sub contDiff_id))

lemma denom_contDiffOn : ContDiffOn ℝ ∞ denom_fn unitInterval := by
  simpa using denom_is_C_inf

lemma denom_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < denom_fn t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

lemma exp_is_C_inf : ContDiffOn ℝ ∞ (fun t => Real.exp t) unitInterval := by
  exact Real.contDiff_exp.contDiffOn

def bump_core (t : ℝ) : ℝ := Real.exp (-1 / (t * (1 - t)))

lemma denom_ne_zero_on_Ioo : ∀ t ∈ Set.Ioo 0 1, denom_fn t ≠ 0 := by
  intro t ht
  exact (denom_pos_on_Ioo t ht).ne'

-- Outside (0,1), the denominator is nonpositive
lemma denom_nonpos_of_not_mem_Ioo {t : ℝ} (ht : t ∉ Set.Ioo (0:ℝ) 1) :
  denom_fn t ≤ 0 := by
  have hcases : t ≤ 0 ∨ 1 ≤ t := by
    have : ¬ (0 < t ∧ t < 1) := by simpa [Set.mem_Ioo] using ht
    rcases not_and_or.mp this with hnot0 | hnot1
    · exact Or.inl (le_of_not_gt hnot0)
    · exact Or.inr (le_of_not_gt hnot1)
  cases hcases with
  | inl hle0 =>
    exact mul_nonpos_of_nonpos_of_nonneg hle0 (sub_nonneg.mpr (le_trans hle0 (by norm_num)))
  | inr h1le =>
    exact mul_nonpos_of_nonneg_of_nonpos (le_trans (show (0:ℝ) ≤ 1 by norm_num) h1le)
      (sub_nonpos.mpr h1le)

lemma bump_core_is_C_inf : ContDiffOn ℝ ∞ bump_core (Set.Ioo 0 1) := by
  exact Real.contDiff_exp.comp_contDiffOn <| by
    simpa [denom_fn] using ContDiffOn.div
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (-1 : ℝ)) (Set.Ioo (0 : ℝ) 1))
      (denom_is_C_inf.mono (Set.Ioo_subset_Icc_self))
      denom_ne_zero_on_Ioo

lemma expNegInvGlue_comp_denom_fn_eq_indicator_bump :
  (fun t => expNegInvGlue (denom_fn t))
  = Set.indicator (Set.Ioo (0:ℝ) 1) bump_core := by
  funext t
  by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
  · have h₁ : expNegInvGlue (denom_fn t) = Real.exp (-(denom_fn t)⁻¹) := by
      simp [expNegInvGlue, not_le.mpr (denom_pos_on_Ioo t ht)]
    have h₂ : Real.exp (-(denom_fn t)⁻¹) = Real.exp (-1 / (t * (1 - t))) := by
      simp [denom_fn, div_eq_mul_inv, neg_mul, one_mul]
    have h := h₁.trans h₂
    simpa [Set.indicator_of_mem ht, bump_core] using h
  · have hnonpos : denom_fn t ≤ 0 := denom_nonpos_of_not_mem_Ioo ht
    simp [expNegInvGlue.zero_of_nonpos hnonpos, Set.indicator_of_notMem ht]

def G (t : ℝ) : ℝ := expNegInvGlue (denom_fn t)

lemma expNegInvGlue_comp_is_C_inf_on_D :
  ContDiffOn ℝ ∞ (fun t => expNegInvGlue (denom_fn t)) unitInterval := by
  simpa using (expNegInvGlue.contDiff.comp denom_contDiff).contDiffOn

-- G is C^∞ continuous on [0, 1]
lemma G_is_C_inf : ContDiffOn ℝ ∞ G unitInterval := by
  exact expNegInvGlue_comp_is_C_inf_on_D

open MeasureTheory Smooth

lemma FDen_G_pos : 0 < FDen G := by
  have hfi : IntervalIntegrable G volume 0 1 := by
    simpa using (ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
      (u := G) (a := 0) (b := 1) (h := by norm_num) G_is_C_inf.continuousOn)
  have hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x := by
    intro x hx; exact expNegInvGlue.pos_of_pos (denom_pos_on_Ioo x hx)
  have hposI' : 0 < ∫ x in (0)..(1), G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hfi hpos (by norm_num)
  have hposI : 0 < ∫ x in Set.Ioc 0 1, G x := by
    simpa [intervalIntegral.integral_of_le (μ := volume)
      (f:=G) (a:=0) (b:=1) (by norm_num : (0:ℝ) ≤ 1)] using hposI'
  simpa [FDen, Set.uIoc, le_rfl] using hposI

lemma FDen_G_ne_zero : FDen G ≠ 0 := (FDen_G_pos).ne'

def F1 : ℝ → ℝ := F G

lemma F1_is_C_inf : ContDiffOn ℝ ∞ F1 unitInterval := by
  simpa [F1] using (F_contDiffOn (G := G) G_is_C_inf FDen_G_ne_zero)

lemma G_NeZero : (fun (t : ℝ) => G t) ≠ 0 := by
  intro hzero
  have hIoo : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by constructor <;> norm_num
  have hpos : 0 < G (1 / 2 : ℝ) := by
    simpa [G] using
    (expNegInvGlue.pos_of_pos (denom_pos_on_Ioo _ hIoo))
  exact (ne_of_gt hpos) (by simpa using congrArg (fun f => f (1 / 2 : ℝ)) hzero)

-- F is C^∞ continuous on [0, 1]
lemma F_is_C_inf : ContDiffOn ℝ ∞ F1 unitInterval := F1_is_C_inf

def κ_smooth (s R L) :=
  R * Real.smoothTransition (s / L)

lemma κ_smooth_is_C_inf : ContDiffOn ℝ ∞ (fun s ↦ κ_smooth s R L) (Set.Icc 0 L) := by
  simpa [κ_smooth] using contDiffOn_const.mul
    (Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_id.div_const (c := L)))

lemma κ_smooth_at_zero : κ_smooth 0 R L = 0 := by
  simp [κ_smooth, Real.smoothTransition.zero]

lemma κ_smooth_at_L (hL : L ≠ 0) : κ_smooth L R L = R := by
  simp [κ_smooth, div_self hL, Real.smoothTransition.one]

def κ (s R L : ℝ) : ℝ :=
  kappa G s R L

-- My curvature function is C^∞ continuous on [0, L]
theorem κ_is_C_inf_on_Icc (R L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => κ s R L) (Set.Icc 0 L) := by
  simpa [κ] using (kappa_contDiffOn (G := G) G_is_C_inf FDen_G_ne_zero R L hL)

theorem κ_at_zero : κ 0 R L = 0 := by
  simp [κ, kappa, F]

theorem κ_at_L (hL : L ≠ 0) : κ L R L = R := by
  simp [κ, kappa, F, div_self hL]

end smoothstep_curve_1

/-
This spiral also uses a smoothstep-based curvature function,
providing a $G^\infty$ continuous transition from tangent to circular arc.

The advantage of this over the previous smoothstep curve is that its first derivative
has a smaller apex, therefore the angular jerk and snap is smaller, thus requiring a shorter
transition length for the same deflection angle.

The heading angle is given by:
$$
\theta(l) = R \int_0^l F(\tfrac{v}{L})\,dv
$$

where:
- $F(z) = \dfrac{\int_0^z G(t-1)\,dt}{\int_0^1 G(t-1)\,dt}$
- $G(t) = e^{-\tfrac{1}{1-t^2}}$
- $l$ = arc length along the curve
- $L$ = total length of the transition curve
- $R$ = radius of the circular arc

The Cartesian coordinates of the spiral are then:
$$
x(l) = \int_0^l \cos\!\big(\theta(v)\big)\,dv,
\quad
y(l) = \int_0^l \sin\!\big(\theta(v)\big)\,dv
$$

with initial conditions $x(0)=0,\ y(0)=0,\ \theta(0)=0$.

The curvature is:
$$\kappa(s) = \frac{R}{2} F\left(\frac{2s}{L}\right)$$
-/

noncomputable
section smoothstep_curve_2

open scoped ContDiff Topology
open Smooth
open MeasureTheory

-- Shifted bump: G₂(t) = exp(-1/(1-(t-1)^2)) on |t-1|<1, 0 otherwise
def denom2 (t : ℝ) : ℝ := 1 - (t - 1)^2

lemma denom2_contDiff : ContDiff ℝ ∞ denom2 := by
  simpa [denom2] using (contDiff_const.sub ((contDiff_id.sub contDiff_const).pow 2))

lemma denom2_contDiffOn : ContDiffOn ℝ ∞ denom2 unitInterval := by
  simpa using denom2_contDiff.contDiffOn

def G2 (t : ℝ) : ℝ := expNegInvGlue (denom2 t)

lemma G2_is_C_inf : ContDiffOn ℝ ∞ G2 unitInterval := by
  simpa [G2] using (expNegInvGlue.contDiff.comp denom2_contDiff).contDiffOn

-- Normalized primitive F₂ from G₂
def F2 : ℝ → ℝ := F G2

-- positivity of denom2 on (0,1)
lemma denom2_pos_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 1) : 0 < denom2 x := by
  have habs : |x - 1| < 1 := by
    have h1 : -1 < x - 1 := by linarith [hx.1]
    have h2 : x - 1 < 1 := by linarith [hx.2]
    exact abs_lt.mpr ⟨by simpa [neg_one_mul] using h1, h2⟩
  have hsq : (x - 1)^2 < 1 := by
    have := (sq_lt_one_iff_abs_lt_one (a := x - 1)).mpr habs
    simpa [pow_two] using this
  have : 1 - (x - 1)^2 > 0 := sub_pos.mpr hsq
  simpa [denom2] using this

lemma FDen_G2_pos : 0 < FDen G2 := by
  have hfi : IntervalIntegrable G2 volume 0 1 := by
    simpa using (ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
      (u := G2) (a := 0) (b := 1) (h := by norm_num) G2_is_C_inf.continuousOn)
  have hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G2 x := by
    intro x hx; exact expNegInvGlue.pos_of_pos (denom2_pos_on_Ioo hx)
  have hposI' : 0 < ∫ x in (0)..(1), G2 x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G2) hfi hpos (by norm_num)
  have hposI : 0 < ∫ x in Set.Ioc 0 1, G2 x := by
    simpa [intervalIntegral.integral_of_le (μ := volume)
      (f:=G2) (a:=0) (b:=1) (by norm_num : (0:ℝ) ≤ 1)] using hposI'
  simpa [FDen, Set.uIoc, le_rfl] using hposI

lemma FDen_G2_ne_zero : FDen G2 ≠ 0 := (FDen_G2_pos).ne'

lemma F2_is_C_inf : ContDiffOn ℝ ∞ F2 unitInterval := by
  simpa [F2] using (F_contDiffOn (G := G2) G2_is_C_inf FDen_G2_ne_zero)

-- Curvature κ₂(s; R, L) = R * F₂(s/L)
def κ₂ (s R L : ℝ) : ℝ := kappa G2 s R L

theorem κ₂_is_C_inf_on_Icc (R L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => κ₂ s R L) (Set.Icc 0 L) := by
  simpa [κ₂] using (kappa_contDiffOn (G := G2) G2_is_C_inf FDen_G2_ne_zero R L hL)

theorem κ₂_at_zero : κ₂ 0 R L = 0 := by
  simp [κ₂, kappa, F]

theorem κ₂_at_L (hL : L ≠ 0) : κ₂ L R L = R := by
  simp [κ₂, kappa, F, div_self hL]

end smoothstep_curve_2
