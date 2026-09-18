import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Motivation for this project

The theorems within this file explain the motivation behind the smoothstep curve.
-/

namespace Motivation

/-- Join two constant-curvature segments at `join`. -/
noncomputable def constantCurvatureJoin (κ₁ κ₂ join : ℝ) : ℝ → ℝ :=
  fun s => if s ≤ join then κ₁ else κ₂

/-- A straight (`κ = 0`) joined directly to a non-straight circular arc has a
curvature discontinuity. -/
theorem straight_circle_curvature_jumps
    {straightCurvature circleCurvature join : ℝ}
    (hcircle : circleCurvature ≠ 0) (hstraight : straightCurvature = 0):
    ¬ContinuousAt (constantCurvatureJoin straightCurvature circleCurvature join) join := by
  subst straightCurvature
  intro h
  have hright : Filter.Tendsto (constantCurvatureJoin 0 circleCurvature join)
    (nhdsWithin join (Set.Ioi join)) (nhds 0) := by
      simpa [constantCurvatureJoin] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hconst : Filter.Tendsto (constantCurvatureJoin 0 circleCurvature join)
    (nhdsWithin join (Set.Ioi join)) (nhds circleCurvature) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [constantCurvatureJoin, not_le.mpr (Set.mem_Ioi.mp hs)]
  exact hcircle (tendsto_nhds_unique hconst hright)


/-- A clothoid leaving a constant-curvature segment: its curvature is affine
after the join and constant before it. -/
noncomputable def clothoidFromConstant (κ₀ rate join : ℝ) : ℝ → ℝ :=
  fun s => if s ≤ join then κ₀ else κ₀ + rate * (s - join)

/-- At a nondegenerate clothoid join, curvature is continuous but its rate of
change `dκ/ds` is not. -/
theorem clothoid_curvature_continuous_but_rate_jumps
    {κ₀ rate join : ℝ} (hrate : rate ≠ 0) :
    ContinuousAt (clothoidFromConstant κ₀ rate join) join ∧
      ¬ContinuousAt (deriv (clothoidFromConstant κ₀ rate join)) join := by
  set f := clothoidFromConstant κ₀ rate join with hf
  -- derivative is `0` to the left of the join, `rate` to the right
  have hleft : ∀ s < join, deriv f s = 0 := by
    intro s hs
    have : f =ᶠ[nhds s] fun _ => κ₀ := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      simp [hf, clothoidFromConstant, le_of_lt (Set.mem_Iio.mp ht)]
    rw [this.deriv_eq, deriv_const]
  have hright : ∀ s, join < s → deriv f s = rate := by
    intro s hs
    have : f =ᶠ[nhds s] fun t => κ₀ + rate * (t - join) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      simp [hf, clothoidFromConstant, not_le.mpr (Set.mem_Ioi.mp ht)]
    rw [this.deriv_eq]
    simp
  refine ⟨?_, ?_⟩
  · -- continuity: both branches agree at the join, so `f` is continuous there
    have : f = fun s => if s ≤ join then κ₀ else κ₀ + rate * (s - join) := rfl
    rw [this]
    apply Continuous.continuousAt
    apply Continuous.if_le (continuous_const) (by fun_prop) continuous_id continuous_const
    intro s hs; simp at hs; subst hs; simp
  · intro h
    -- one-sided limits of `deriv f` at the join
    have hL : Filter.Tendsto (deriv f) (nhdsWithin join (Set.Iio join)) (nhds 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hleft s hs).symm
    have hR : Filter.Tendsto (deriv f) (nhdsWithin join (Set.Ioi join)) (nhds rate) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hright s hs).symm
    have hL' := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio join))
    have hR' := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi join))
    have e1 := tendsto_nhds_unique hL hL'
    have e2 := tendsto_nhds_unique hR hR'
    exact hrate (e2.trans e1.symm)

open Polynomial

/-- Splice a polynomial curvature profile between constant-curvature segments.
The endpoint values are chosen from the polynomial itself, so the curvature
profile is continuous at both joins. -/
noncomputable def polynomialTransition (p : Polynomial ℝ) (start finish : ℝ) : ℝ → ℝ :=
  fun s =>
    if s ≤ start then p.eval start
    else if finish ≤ s then p.eval finish
    else p.eval s

/-- Iterated derivatives of a polynomial function are given by the formal iterated derivative. -/
lemma iteratedDeriv_polynomial_eval (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) = fun x => (derivative^[k] p).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact Polynomial.deriv _

/-- A polynomial transition between distinct endpoint curvatures cannot match
constant-curvature segments to every derivative order: some positive-order
curvature derivative is discontinuous at one of the two joins. -/
theorem polynomial_transition_eventually_has_derivative_jump
    (p : Polynomial ℝ) {start finish : ℝ} (hinterval : start < finish)
    (hendpoints : p.eval start ≠ p.eval finish) :
    ∃ n : ℕ, 1 ≤ n ∧
      (¬ContinuousAt (iteratedDeriv n (polynomialTransition p start finish)) start ∨
       ¬ContinuousAt (iteratedDeriv n (polynomialTransition p start finish)) finish) := by
  set g := polynomialTransition p start finish with hg
  set n := p.natDegree with hn
  -- `p` is nonconstant, so its degree is at least 1
  have hn1 : 1 ≤ n := by
    by_contra hlt
    have hp : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    apply hendpoints
    rw [hp]; simp
  -- the `n`-th formal derivative of `p` is a nonzero constant `c`
  set c := (derivative^[n] p).coeff 0 with hc
  have hderiv : derivative^[n] p = C c :=
    eq_C_of_natDegree_le_zero (by
      have := natDegree_iterate_derivative p n
      rw [← hn, Nat.sub_self] at this
      exact this)
  have hc0 : c ≠ 0 := by
    rw [hc, coeff_iterate_derivative]
    rw [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
      (leadingCoeff_ne_zero.mpr (by rintro h0; rw [h0, natDegree_zero] at hn; omega))
  refine ⟨n, hn1, Or.inl ?_⟩
  intro h
  -- left of `start`, `g` is constant, so its `n`-th derivative is `0`
  have hL : Filter.Tendsto (iteratedDeriv n g) (nhdsWithin start (Set.Iio start)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : g =ᶠ[nhds s] fun _ => p.eval start := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      simp [hg, polynomialTransition, le_of_lt (Set.mem_Iio.mp ht)]
    rw [this.iteratedDeriv_eq, iteratedDeriv_const, if_neg (by omega)]
  -- right of `start` (before `finish`), `g` is `p`, so its `n`-th derivative is `c`
  have hR : Filter.Tendsto (iteratedDeriv n g) (nhdsWithin start (Set.Ioo start finish)) (nhds c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : g =ᶠ[nhds s] fun t => p.eval t := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      simp [hg, polynomialTransition, not_le.mpr ht.1, not_le.mpr ht.2]
    rw [this.iteratedDeriv_eq, iteratedDeriv_polynomial_eval, hderiv]
    simp
  have hL' := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio start))
  have hR' := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioo start finish))
  -- `Ioo start finish` is nonempty near `start`, so the limit there is unique
  haveI : (nhdsWithin start (Set.Ioo start finish)).NeBot :=
    left_nhdsWithin_Ioo_neBot hinterval
  have e1 := tendsto_nhds_unique hL hL'
  have e2 := tendsto_nhds_unique hR hR'
  exact hc0 (e2.trans e1.symm)

end Motivation
