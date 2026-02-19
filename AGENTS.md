# Agents

This file provides guidance to LLM-based agents when working with code in this repository.

## Project Overview

A Lean 4 proof formalizing smoothstep curves—infinitely differentiable curvature functions for G∞ continuous transitions between constant curvature segments (tangent lines and circular arcs). The proofs use Mathlib.

## Build Commands

```bash
lake build           # Build the project
lake exe runLinter   # Run the linter
lake exe cache get   # Download pre-built Mathlib cache (use after lake update)
```

**NEVER run `lake clean`** - This project depends on Mathlib, which takes 1+ hour to rebuild from scratch. If you need to force a rebuild of project files only, delete specific `.olean` files in `.lake/build/lib/proofs/` instead. If Mathlib cache is missing, use `lake exe cache get` to download pre-built oleans.

## Architecture

**Core Design**: Transitions are parameterized by a bump function G supported in (0,1), from which the shape function H is derived as the normalized primitive:
- `HInt G z` = ∫₀ᶻ G(t)dt
- `HInt_denom G` = ∫₀¹ G(t)dt (normalization)
- `H G z` = HInt G z / HInt_denom G

**Key Files**:
- `proofs/smoothstep_curve.lean` - Main proof file containing all theorems and structures
- `proofs/Common.lean` - Shared Mathlib imports and options

**Main Structures and Constructors** (`proofs/smoothstep_curve.lean`):
- `SmoothstepCurve` - Structure packaging H, κ, boundary conditions (global ContDiff)
- `mkSmoothstepCurveFromShape` - Constructor from shape function H directly
- `DenomParams` - Helper structure for denominator-based construction
- `curveFrom` - Constructor from DenomParams via `expNegInvGlue ∘ denom`

**Namespaces**:
- `GenericFramework` - Core primitives, H construction, curvature definitions
- `CanonicalSmoothstep` - Example using `denomCanonical z = z * (1 - z)`
- `ParametricDenominators` - Families: `denomScaled`, `denomPow`, `denomPoly`
- `Reparametrization` - Composing curves with reparametrization functions
- `ConvexCombination` - Mixing two smoothstep curves

## Lean Development Workflow

**Iterative approach**: Make one small change at a time and check results before proceeding.

**MCP Lean tools** (use frequently):
- `lean_goal` - Check proof state (omit column for before/after view)
- `lean_diagnostic_messages` - Get errors/warnings for a file
- `lean_hover_info` - Type signatures and docs (column at START of identifier)
- `lean_leansearch` - Natural language theorem search (rate limited: 3/30s)
- `lean_loogle` - Type pattern search (rate limited: 3/30s)
- `lean_local_search` - Fast local declaration search (verify names exist BEFORE using)
- `lean_multi_attempt` - Test multiple tactics without editing

**Search decision tree**:
1. "Does X exist locally?" → `lean_local_search`
2. "I need a lemma that says X" → `lean_leansearch`
3. "Find lemma with type pattern" → `lean_loogle`
4. Goal-specific search → `lean_state_search`

**Critical**: Never guess theorem names. When diagnostics show "Unknown identifier", search for alternatives rather than using completions on non-existent names.

**Type system gotchas**:
- Use explicit type annotations: `(1/2 : ℝ)` not `0.5`
- Use `@theorem_name` to make implicit arguments explicit
- Subset directions matter for monotonicity lemmas
- `ContinuousOn f s` vs `Continuous f` distinction

**Proof strategy**:
1. Start with `sorry`/`admit` to get structure compiling
2. Use `have` for intermediate results
3. Fill in one piece at a time, checking `lean_goal` after each change

## Project-Specific Tips

**Cleaning up unused lemmas**:
- Use `Grep` with `output_mode: "count"` to find usage - 1 occurrence = unused (definition only)
- Wrapper lemmas accumulate over time - periodically audit and remove

**ContDiffOn vs ContDiff**:
- `ContDiff ℝ ∞ f` = globally smooth on all of ℝ
- `ContDiffOn ℝ ∞ f s` = smooth on subset s
- When migrating to global smoothness, update derivative lemmas too (`iteratedDeriv` vs `iteratedDerivWithin`)
- Valid proof pattern: use `iteratedDerivWithin` internally, then convert to `iteratedDeriv` via `iteratedDerivWithin_eq_iteratedDeriv`
- Argument order: `iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn) (h : ContDiffAt) (hx : x ∈ s)`

**Linter fixes**:
- Unused lambda args need `_` prefix: `fun _z hz => ...` not `fun z hz => ...`
- The linter uses nolints.json for exceptions - run with `--update` to regenerate
