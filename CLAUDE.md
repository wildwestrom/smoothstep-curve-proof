# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Lean 4 proof formalizing smoothstep curves—infinitely differentiable curvature functions for G∞ continuous transitions between constant curvature segments (tangent lines and circular arcs). The proofs use Mathlib.

## Build Commands

```bash
lake build           # Build the project
lake exe runLinter   # Run the linter
```

## Architecture

**Core Design**: Transitions are parameterized by a bump function G supported in (0,1), from which the shape function H is derived as the normalized primitive:
- `HInt G z` = ∫₀ᶻ G(t)dt
- `HInt_denom G` = ∫₀¹ G(t)dt (normalization)
- `H G z` = HInt G z / HInt_denom G

**Key Files**:
- `proofs/smoothstep_curve.lean` - Main proof file containing all theorems and structures
- `proofs/Common.lean` - Shared Mathlib imports and options

**Main Structures and Constructors** (`proofs/smoothstep_curve.lean`):
- `SmoothstepCurve` (line 514) - Structure packaging H, κ, boundary conditions
- `mkSmoothstepCurve` (line 542) - Constructor from bump function G
- `mkSmoothstepCurveFromShape` (line 580) - Constructor from shape function H directly
- `mkSmoothstepCurveFromDenom` (line 814) - Constructor from denominator function via `expNegInvGlue ∘ denom`
- `DenomParams` (line 850) - Helper structure for denominator-based construction

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
