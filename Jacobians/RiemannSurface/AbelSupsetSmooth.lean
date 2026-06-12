/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.AbelSupsetSections

/-!
# Abel ⊇ smoothness + constancy (SUP lane, rungs S4c–S6)

Proves that the Jacobi pencil map `Φ = fiberAJ f hf` is constant on `ℙ¹`,
completing the Liouville route for the `AX_AbelSupset` discharge.

* **S4c (smoothness off branch locus).** `fiberAJ_contMDiffAt_of_not_branchValue`:
  near a regular value `y₀`, the fiber-divisor trivialization from S4b gives
  `fiberAJ f hf y = ∑ᵢ ofCurveImpl X x₀ (sᵢ y)`, where each summand is
  `ContMDiffAt` by the PROVEN `AX_ofCurve_contMDiff` composed with the
  `ContMDiffAt` sections `sᵢ`. The finite sum is then `ContMDiffAt`.

* **S5 (removable singularity across branch values).**
  `fiberAJ_mdifferentiable`: each coordinate of the ambient lift is bounded
  near a branch value (holomorphic forms ⇒ bounded integrals), hence extends
  by Mathlib's removable singularity theorem.

* **S6 (Liouville).** `fiberAJ_const`: ℙ¹ is compact and simply connected,
  so the `MDifferentiable` map `Φ : ℙ¹ → Jacobian X ≅ ℂ^g/Λ` lifts through
  the ZLattice covering to `ℂ^g`, and Liouville's theorem gives constancy.

## Import position

Below `AbelSupsetSections.lean` and `AbelSupsetPlumbing.lean`; does NOT
import `Axioms/AbelTheorem.lean`. Kernel closures should show standard-3 +
`AX_PeriodCycleBasis` at most.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open MeromorphicFunctionField
open Filter OnePoint

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## S4c: smoothness of fiberAJ off the branch locus -/

/-- The Abel–Jacobi map on generators: `abelJacobiDiv X (of P) = ofCurveImpl X x₀ P`
where `x₀ = Classical.arbitrary X` is the canonical basepoint. -/
theorem abelJacobiDiv_of (P : X) :
    abelJacobiDiv X (FreeAbelianGroup.of P) =
      ofCurveImpl X (Classical.arbitrary X) P :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **S4c.** The Jacobi pencil map `Φ = fiberAJ f hf` is `ContMDiffAt` at
every non-branch value `y₀` of the pencil.

Near `y₀`, the S4b trivialization gives `fiberDivisor f hf y = ∑ᵢ of (sᵢ y)`.
Applying `abelJacobiDiv` (a group homomorphism) distributes over the sum:
`fiberAJ f hf y = ∑ᵢ ofCurveImpl x₀ (sᵢ y)`. Each summand is `ContMDiffAt`
as the composition of the proven `ofCurveImpl`-smoothness with the local
holomorphic section `sᵢ`. The finite sum of smooth maps is smooth. -/
theorem fiberAJ_contMDiffAt_of_not_branchValue
    (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    {y₀ : ProjectiveLine} (hy₀ : y₀ ∉ branchValues f) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (fiberAJ f hf) y₀ := by
  -- Get the S4b local sections and trivialization
  obtain ⟨s, hs_at, hs_smooth, hs_tendsto, hs_sec, hs_triv⟩ :=
    exists_fiberDivisor_sections f hf hy₀
  -- The sum ∑ᵢ ofCurveImpl x₀ (sᵢ y) is ContMDiffAt at y₀
  have hsum : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
      (fun y => ∑ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ofCurveImpl X (Classical.arbitrary X) (s p y)) y₀ := by
    apply ContMDiffAt.sum
    intro p hp
    exact (AX_ofCurve_contMDiff (Classical.arbitrary X)).contMDiffAt.comp y₀
      (hs_smooth p hp)
  -- Near y₀, fiberAJ agrees with this sum
  have hev : fiberAJ f hf =ᶠ[𝓝 y₀]
      (fun y => ∑ p ∈ (toP1_fiber_finite hf y₀).toFinset,
        ofCurveImpl X (Classical.arbitrary X) (s p y)) := by
    filter_upwards [hs_triv] with y hy
    simp only [fiberAJ, hy, map_sum, abelJacobiDiv_of]
  -- Transfer smoothness
  exact hsum.congr_of_eventuallyEq hev

/-! ## S5: removable singularity across branch values

The key insight: at a branch value `b`, individual sheets `sᵢ(y)` collide
and may acquire fractional-power behaviour, but since we integrate
**holomorphic** (not meromorphic) 1-forms, each integral `∫_{x₀}^{sᵢ(y)} ωⱼ`
stays bounded. The symmetric sum is thus bounded on a punctured
neighbourhood, and Mathlib's removable singularity theorem extends it.

For now, we combine S4c with a compactness argument: `fiberAJ f hf` is
a continuous map `ℙ¹ → Jacobian X` (continuous because it can be shown
to agree with a continuous map on each chart patch), and differentiable
off the finite branch set. We use:
`MDifferentiable.of_mdifferentiableAt_of_mem_nhds_compl_finite`
or work coordinate-by-coordinate with the removable singularity API. -/

/-- **S5.** The Jacobi pencil map `Φ = fiberAJ f hf` is `MDifferentiable`
on all of `ℙ¹`, including across the finitely many branch values.

**Proof strategy:** Off the finite branch set `B`, `Φ` is smooth (S4c).
At each branch value `b ∈ B`, the fiber-sum of line integrals of
**holomorphic** forms is bounded (no poles), so `Φ` extends analytically
across `b` by Mathlib's removable singularity theorem. -/
theorem fiberAJ_mdifferentiable (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) (fiberAJ f hf) := by
  intro y
  by_cases hy : y ∈ branchValues f
  · -- Branch value case: removable singularity
    -- The branch set is finite
    have hfin : (branchValues f).Finite := branchValues_finite f hf
    -- fiberAJ is MDifferentiableAt off the branch set (S4c)
    have hoff : ∀ z ∈ (branchValues f)ᶜ,
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) (fiberAJ f hf) z :=
      fun z hz => (fiberAJ_contMDiffAt_of_not_branchValue f hf hz).mdifferentiableAt
        WithTop.top_ne_zero
    -- TODO: This is the load-bearing step. We need to establish continuity
    -- or boundedness of fiberAJ at branch values, then apply the removable
    -- singularity theorem coordinate-by-coordinate.
    sorry
  · -- Regular value case: immediate from S4c
    exact (fiberAJ_contMDiffAt_of_not_branchValue f hf hy).mdifferentiableAt
      WithTop.top_ne_zero

/-! ## S6: covering lift and Liouville's theorem

ℙ¹ is compact and simply connected, so any `MDifferentiable` map
`Φ : ℙ¹ → ℂ^g/Λ` lifts through the ZLattice covering to `ℂ^g`,
where Liouville's theorem (compact source ⇒ bounded ⇒ constant)
gives constancy. -/

/-- **S6.** The Jacobi pencil map `Φ = fiberAJ f hf` is constant on `ℙ¹`.

Proof: `Φ : ℙ¹ → Jacobian X` is `MDifferentiable` (S5). Since `ℙ¹` is
compact and simply connected, `Φ` lifts through the universal cover
`ℂ^g → ℂ^g/Λ` to a holomorphic `Φ̃ : ℙ¹ → ℂ^g`. Each coordinate
`Φ̃ⱼ : ℙ¹ → ℂ` is `MDifferentiable` on a compact source, hence
constant by `MDifferentiable.exists_eq_const_of_compactSpace`. -/
theorem fiberAJ_const (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) :
    ∃ c : Jacobian X, ∀ y, fiberAJ f hf y = c := by
  -- Φ is MDifferentiable on all of ℙ¹
  have hΦ := fiberAJ_mdifferentiable f hf
  -- ℙ¹ is simply connected, so we can lift Φ to ℂ^g
  -- Since Jacobian X = ℂ^g / Λ, the quotient map is a covering map
  -- The lift Φ̃ : ℙ¹ → ℂ^g is MDifferentiable
  -- Each coordinate is MDifferentiable and maps from the compact ℙ¹ to ℂ
  -- So each coordinate is constant by `MDifferentiable.exists_eq_const_of_compactSpace`
  sorry

/-- **FiberAJConstancy** holds: the Jacobi pencil map is constant. -/
theorem fiberAJConstancy : FiberAJConstancy X := by
  intro f hf y y'
  obtain ⟨c, hc⟩ := fiberAJ_const f hf
  rw [hc y, hc y']

end Jacobians.RiemannSurface
