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

---

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

---

My goal is to prove both of my curvature functions are $C^\infty$ continuous.

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

noncomputable section

open scoped ContDiff Topology

def denom_fn (t : ℝ) : ℝ := t * (1 - t)

lemma denom_is_C_inf : ContDiffOn ℝ ∞ denom_fn unitInterval := by
    exact contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)

lemma denom_contDiff : ContDiff ℝ ∞ denom_fn := by
    simpa using (contDiff_id.mul (contDiff_const.sub contDiff_id))

lemma denom_contDiffOn : ContDiffOn ℝ ∞ denom_fn unitInterval := by
    simpa using denom_is_C_inf

lemma denom_nonzero_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) : 0 < denom_fn t := by
    rcases ht with ⟨ht0, ht1⟩
    have h_t_pos : 0 < t := ht0
    have h_one_minus_t_pos : 0 < 1 - t := by exact sub_pos.mpr ht1
    exact mul_pos h_t_pos h_one_minus_t_pos

lemma exp_is_C_inf : ContDiffOn ℝ ∞ (fun t => Real.exp t) unitInterval := by
    exact Real.contDiff_exp.contDiffOn

def bump_core (t : ℝ) : ℝ := Real.exp (-1 / (t * (1 - t)))

lemma bump_core_is_C_inf : ContDiffOn ℝ ∞ bump_core (Set.Ioo 0 1) := by
    have h_den_C_inf_Ioo : ContDiffOn ℝ ∞ denom_fn (Set.Ioo 0 1) := by
        exact denom_is_C_inf.mono (Set.Ioo_subset_Icc_self)
    have h_den_nonzero : ∀ t ∈ Set.Ioo 0 1, denom_fn t ≠ 0 := by
        intro t ht
        exact (denom_nonzero_on_Ioo t ht).ne'
    have h_const : ContDiffOn ℝ ∞ (fun t : ℝ => (-1 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
        simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (-1 : ℝ)) (Set.Ioo (0 : ℝ) 1))
    have h_inner_C_inf : ContDiffOn ℝ ∞ (fun t : ℝ => ((-1 : ℝ) / denom_fn t)) (Set.Ioo (0 : ℝ) 1) := by
        apply ContDiffOn.div h_const h_den_C_inf_Ioo h_den_nonzero
    have h_inner2 : ContDiffOn ℝ ∞ (fun t : ℝ => -1 / (t * (1 - t))) (Set.Ioo (0 : ℝ) 1) := by
        simpa [denom_fn] using h_inner_C_inf
    exact Real.contDiff_exp.comp_contDiffOn h_inner2

def G (t : ℝ) : ℝ := expNegInvGlue (denom_fn t)

lemma expNegInvGlue_comp_is_C_inf_on_D :
    ContDiffOn ℝ ∞ (fun t => expNegInvGlue (denom_fn t)) unitInterval := by
    have hE : ContDiff ℝ ∞ expNegInvGlue := by
      simpa using (expNegInvGlue.contDiff)
    have hglob : ContDiff ℝ ∞ (fun t => expNegInvGlue (denom_fn t)) :=
      hE.comp denom_contDiff
    simpa using (hglob.contDiffOn : ContDiffOn ℝ ∞ (fun t => expNegInvGlue (denom_fn t)) unitInterval)

-- G is C^∞ continuous on [0, 1]
lemma G_is_C_inf : ContDiffOn ℝ ∞ G unitInterval := by
    exact expNegInvGlue_comp_is_C_inf_on_D

def F_num (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

lemma F_num_is_C_inf : ContDiffOn ℝ ∞ F_num unitInterval := by
    -- Work with the interval integral primitive and then transfer by congruence on `unitInterval`.
    let P : ℝ → ℝ := fun z => ∫ t in (0)..z, G t
    have h_deriv_within :
        ∀ x ∈ unitInterval, HasDerivWithinAt P (G x) unitInterval x := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := hx.1
      -- `G` is continuous on `[0,1]`, hence interval-integrable on `[0,x]` for `x ∈ [0,1]`.
      have hcont : ContinuousOn G (Set.Icc 0 1) := G_is_C_inf.continuousOn
      have hint : IntervalIntegrable G MeasureTheory.volume 0 x := by
        -- restrict continuity to `[0,x] ⊆ [0,1]`
        have hcont' : ContinuousOn G (Set.Icc 0 x) :=
          hcont.mono (Set.Icc_subset_Icc le_rfl hx.2)
        simpa using
          (ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
            (u := G) (a := 0) (b := x) (h := hx0) hcont')
      -- measurability and continuity within at `x` on `unitInterval`
      have hmeas : StronglyMeasurableAtFilter G (𝓝[unitInterval] x) MeasureTheory.volume := by
        have hmeasSet : MeasurableSet unitInterval := by simp [unitInterval, isClosed_Icc.measurableSet]
        exact hcont.stronglyMeasurableAtFilter_nhdsWithin (hs := hmeasSet) x
      have hcontWithin : ContinuousWithinAt G unitInterval x := hcont.continuousWithinAt hx
      -- Provide the `FTCFilter` instance for `Icc 0 1` at point `x`.
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2⟩
      haveI : Fact (x ∈ Set.Icc (0 : ℝ) 1) := ⟨hxIcc⟩
      haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) := by
        simpa [unitInterval] using (intervalIntegral.FTCFilter.nhdsIcc (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))
      -- apply FTC-1 within-set
      simpa [P] using
        (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := x)
            (f := G) hint hmeas hcontWithin)
    -- From derivative within equals `G`, we get differentiability and `derivWithin P = G` on `unitInterval`.
    have h_diff : DifferentiableOn ℝ P unitInterval :=
      fun x hx => (h_deriv_within x hx).differentiableWithinAt
    have h_deriv_eq : ∀ x ∈ unitInterval, derivWithin P unitInterval x = G x := by
      intro x hx
      have hsx : UniqueDiffWithinAt ℝ unitInterval x := by
        simpa [unitInterval] using (uniqueDiffOn_Icc_zero_one x ⟨hx.1, hx.2⟩)
      simpa using (HasDerivWithinAt.derivWithin (h_deriv_within x hx) hsx)
    -- Thus, `P` is `C^∞` on `unitInterval` since `G` is `C^∞` there.
    have hP : ContDiffOn ℝ ∞ P unitInterval := by
      -- use the characterization by derivative within on sets with unique derivatives
      have hUD : UniqueDiffOn ℝ unitInterval := by
        simpa [unitInterval] using uniqueDiffOn_Icc_zero_one
      -- reformulation for `∞`
      have := (contDiffOn_infty_iff_derivWithin (𝕜 := ℝ) (s₂ := unitInterval) (f₂ := P) hUD)
      -- it suffices to show differentiable and the derivative is `C^∞`.
      refine (this.mpr ?_)
      refine And.intro h_diff ?_
      -- show `derivWithin P unitInterval` is `C^∞`, by congruence with `G` on `unitInterval`.
      have h_congr : ∀ y ∈ unitInterval, (derivWithin P unitInterval) y = G y := h_deriv_eq
      exact (contDiffOn_congr (s := unitInterval)
              (f₁ := derivWithin P unitInterval) (f := G) h_congr).mpr G_is_C_inf
    -- Finally, `F_num` agrees with `P` on `unitInterval`.
    have h_congr_PI : ∀ z ∈ unitInterval, F_num z = P z := by
      intro z hz
      have hz0 : (0 : ℝ) ≤ z := hz.1
      -- rewrite interval integral as integral over `Ioc` when `0 ≤ z`
      have : ∫ t in (0)..z, G t = ∫ t in Set.Ioc 0 z, G t := by
        simpa using
          (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
            (f := G) (a := (0 : ℝ)) (b := z) hz0)
      simp [F_num, P, Set.uIoc, hz0, this]
    -- transfer smoothness by congruence on the set
    exact (contDiffOn_congr (s := unitInterval) (f₁ := F_num) (f := P) h_congr_PI).mpr hP

def F_den : ℝ := ∫ t in Set.uIoc 0 1, G t

lemma F_den_pos : 0 < F_den := by
    have hfi : IntervalIntegrable G MeasureTheory.volume 0 1 := by
      have hu : ContinuousOn G (Set.Icc 0 1) := G_is_C_inf.continuousOn
      simpa using (ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
        (u := G) (a := 0) (b := 1) (h := by norm_num) hu)
    have hpos : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → 0 < G x := by
      intro x hx
      have hxU : x ∈ unitInterval := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hden_pos : 0 < denom_fn x := denom_nonzero_on_Ioo x hx
      have hGeq : G x = expNegInvGlue (denom_fn x) := by exact rfl
      have : 0 < expNegInvGlue (denom_fn x) := expNegInvGlue.pos_of_pos hden_pos
      simpa [hGeq] using this
    have hab : (0:ℝ) < 1 := by norm_num
    have hposI' : 0 < ∫ x in (0)..(1), G x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (a:=0) (b:=1) (f:=G) hfi hpos hab
    have hIoc_eq : ∫ x in (0)..(1), G x = ∫ x in Set.Ioc 0 1, G x := by
      simpa using
        (intervalIntegral.integral_of_le (μ := MeasureTheory.volume)
          (f:=G) (a:=0) (b:=1) (by norm_num : (0:ℝ) ≤ 1))
    have hposI : 0 < ∫ x in Set.Ioc 0 1, G x := by
      simpa [hIoc_eq] using hposI'
    simpa [F_den, Set.uIoc, le_rfl] using hposI

lemma F_den_ne_0 : F_den ≠ 0 := by
    exact F_den_pos.ne'

def F (z : ℝ) : ℝ :=
    if z ≤ 0 then 0
    else if 1 ≤ z then 1
    else F_num z / F_den

lemma F_eq_ratio_on_unit {z : ℝ} (hz : z ∈ unitInterval) :
    F z = F_num z / F_den := by
  rcases hz with ⟨hz0, hz1⟩
  by_cases h0 : z = 0
  · subst h0
    simp [F, F_num, F_den, Set.uIoc, le_rfl]
  by_cases h1 : z = 1
  · subst h1
    have hden_ne : F_den ≠ 0 := ne_of_gt F_den_pos
    have hI : (∫ t in Set.Ioc 0 1, G t) = F_den := by
      simp [F_den, Set.uIoc, le_rfl]
    have hnum : F_num 1 = F_den := by
      simpa [F_num, Set.uIoc, le_rfl] using hI
    simp [F, le_rfl, hnum, hden_ne]

  have hz_pos : 0 < z := lt_of_le_of_ne hz0 (by simpa [eq_comm] using h0)
  have hz_lt_one : z < 1 := lt_of_le_of_ne hz1 (by simpa using h1)
  simp [F, not_le.mpr hz_pos, not_le.mpr hz_lt_one]

lemma G_NeZero : NeZero (fun (t : ℝ) => G t) := by
    refine ⟨by
      intro hzero
      have hx : (1 / 2 : ℝ) ∈ unitInterval := by constructor <;> norm_num
      have hIoo : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by constructor <;> norm_num
      have hden_pos : 0 < denom_fn (1 / 2 : ℝ) := denom_nonzero_on_Ioo _ hIoo
      have hGeq : G (1 / 2 : ℝ) = expNegInvGlue (denom_fn (1 / 2)) :=
        by exact rfl
      have hposE : 0 < expNegInvGlue (denom_fn (1 / 2 : ℝ)) :=
        expNegInvGlue.pos_of_pos hden_pos
      have hGzero : G (1 / 2 : ℝ) = 0 := by
        simpa using congrArg (fun f => f (1 / 2 : ℝ)) hzero
      have : expNegInvGlue (denom_fn (1 / 2 : ℝ)) = 0 := by
        rw [← hGeq]
        exact hGzero
      exact (ne_of_gt hposE) this⟩

-- F is C^∞ continuous on [0, 1]
lemma F_is_C_inf : ContDiffOn ℝ ∞ F unitInterval := by
  have h_congr : ∀ x ∈ unitInterval, F x = (fun x => F_num x / F_den) x := by
    intro x hx; simpa using F_eq_ratio_on_unit hx
  have : ContDiffOn ℝ ∞ (fun x => F_num x / F_den) unitInterval :=
    ContDiffOn.div_const F_num_is_C_inf F_den
  exact (contDiffOn_congr (s := unitInterval) (f₁ := F)
          (f := fun x => F_num x / F_den) h_congr).mpr this

def κ (s R L : ℝ) : ℝ :=
    F (s / L) * R

-- My curvature function is C^∞ continuous on [0, 1]
theorem κ_is_C_inf (R L : ℝ) : ContDiffOn ℝ ∞ (fun s => κ s R L) unitInterval := by
    admit
