/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.vac425ed308e0.TauCeti.Analysis.Complex.Conformal.Area
public import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.vac425ed308e0.TauCeti.MeasureTheory.Integral.CircleLIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
/-!
# The length–area inequality for a holomorphic map

The **length–area method** converts the finiteness of the Dirichlet integral
`∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` — which `TauCeti/Analysis/Complex/Conformal/Area.lean` identifies
with the area of `f '' s` — into a statement about *lengths*: among the circles `‖z - ζ‖ = ρ`
with `r < ρ < R`, at least one has a short image. This file is the holomorphic half of that
method. The measure-theoretic half is
`TauCeti/MeasureTheory/Integral/CircleLIntegral.lean`, which proves the length–area inequality and
Wolff's lemma for an arbitrary measurable weight `g : ℂ → ℝ≥0∞` on the plane, out of
Cauchy–Schwarz on each circle and polar Fubini. All this file does is instantiate that weight at
the **length density of `f`**, namely `‖deriv f‖ₑ` cut off outside `s`, and identify what the two
sides of the general estimates then mean:

* the circle integral `TauCeti.circleLIntegral` of that weight is
  `TauCeti.circleImageLength f s ζ ρ`, which for `ρ > 0`, measurable `s` and holomorphic `f` is the
  arc length of the parametrised curve `f ∘ circleMap ζ ρ` over the angles landing in `s` (for
  `ρ ≤ 0` it is `0` by the `ENNReal.ofReal ρ` convention of `TauCeti.circleLIntegral`, and carries
  no geometric reading);
* its plane integral of squares is the Dirichlet integral of `f` over `s`, hence by
  `Conformal/Area.lean` the area of `f '' s`.

So the length–area inequality reads
`∫⁻ ρ in Ioi 0, ℓ ρ ^ 2 / ρ ≤ 2 π * volume (f '' s)`, and Wolff's lemma reads: on every annulus,
and for every `c` strictly above the average `2 π A / log (R / r)`, there is a radius with
`ℓ ρ ^ 2 < c` — a threshold that falls without limit as the annulus is made longer. Letting it fall
below an arbitrary `c ≠ 0`, which a finite Dirichlet integral allows, gives the form the crosscut
estimates consume: `ℓ ρ < c` at some radius below every prescribed bound
(`TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top`), equivalently `ℓ` has lower limit `0` at
the centre (`TauCeti.liminf_circleImageLength_nhdsGT_eq_zero`). A *limit* is not available and is
false in general; only some arbitrarily small radii carry a short circle.

The genuinely holomorphic content added here is the **chord bound**
`TauCeti.ofReal_dist_le_circleImageLength`, which is what makes `ℓ` a length: the fundamental
theorem of calculus along the arc bounds the distance between the images of the endpoints of a
sub-arc by `ℓ ρ`. That is the form in which Wolff's lemma is used, and it is the analytic engine of
layer **L5** of the conformal-mapping roadmap (`ConformalMapping/README.md`), Carathéodory's
boundary correspondence. Only that quantitative input is proved here: a radius whose circle has
short image, and a bound on the chords of its arcs. The crosscuts of a Riemann map at a boundary
point `ζ` are not constructed here, nor is the bound on their diameter that a later file is to draw
from these estimates in order to force the cluster set at `ζ` to degenerate to a point.

## Main results

* `TauCeti.circleImageLength` — the circle integral of the length density of `f` cut off outside
  `s`; for `ρ > 0`, measurable `s` and holomorphic `f` this is the arc length of `f ∘ circleMap ζ ρ`
  over the angles landing in `s`, a length along the parametrisation, counted with multiplicity,
  rather than a measure of the image set.
* `TauCeti.ofReal_dist_le_mul_lintegral_Ioc` — the chord bound in its primitive, set-free form:
  the images of the endpoints of an arc of angles are at distance at most `|ρ|` times the angular
  integral of `‖deriv f‖` over that arc, for a radius `ρ` of either sign.
* `TauCeti.ofReal_dist_le_circleImageLength` — the chord bound justifying the name, and the only
  claim made here about lengths that is actually proved: a sub-arc of angular width at most `2 * π`
  that stays in `s` and in a set on which `f` is holomorphic has the distance between the images of
  its endpoints bounded by that quantity.
* `TauCeti.circleImageLength_eq_lintegral_Ioc` — the angular integral may be taken over any period,
  so the branch cut chosen in the definition is immaterial.
* `TauCeti.lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq` — the **length–area
  inequality**, and `TauCeti.lintegral_circleImageLength_sq_div_le_volume_image` its form with the
  area of `f '' s` on the right, through the area formula of `Conformal/Area.lean`.
* `TauCeti.exists_circleImageLength_sq_lt` and
  `TauCeti.exists_circleImageLength_sq_lt_of_volume_image` — **Wolff's lemma**: a radius with
  `ℓ ρ ^ 2 < c` exists in every annulus `r < ρ < R` on which `2 π A < c * log (R / r)`.
* `TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top` — its limiting form, the one a crosscut
  estimate consumes: for a finite Dirichlet integral, below every bound `R` there is a radius at
  which `ℓ ρ` is smaller than any prescribed `c ≠ 0`.
* `TauCeti.liminf_circleImageLength_nhdsGT_eq_zero` — the same statement as a lower limit at the
  centre, which is the exact sense in which the method makes arcs short.

Holomorphy is used in exactly two places: through `Conformal/Area.lean`, to replace the Dirichlet
integral by the area of the image, and in the chord bound, where the fundamental theorem of calculus
along the arc is applied. The estimates themselves hold for the measurable function `deriv f`
whatever it is, which is why they are proved for a general weight one file down.

## Coordination with upstream Mathlib

Layer L5 is absent from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
the in-progress human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem
itself, and the pinned Mathlib has no length–area estimate; so this file is new Lean formalization
rather than a temporary shim. Its Mathlib inputs — the measurability of `deriv` and the increment
bound `MeasureTheory.enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` along an arc — are consumed,
not restated.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method and
  Wolff's lemma).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/
public section
namespace TauCeti
open Complex MeasureTheory Metric Set Topology
open scoped ENNReal Real
variable {U s t : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ}
/-! ### The length density of a holomorphic map, and its circle integrals -/
theorem ofReal_dist_le_mul_lintegral_Ioc (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ)
    {ρ : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmemU : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
  have hcd : ContDiffOn ℝ 1 (fun θ => f (circleMap ζ ρ θ)) (Icc a b) := fun θ hθ =>
    (((hf.analyticAt (hUo.mem_nhds (hmemU θ hθ))).contDiffAt.restrict_scalars ℝ).comp θ
      (contDiff_circleMap ζ ρ).contDiffAt).contDiffWithinAt
  have hderiv : ∀ θ ∈ Ioc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ =
      ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
    intro θ hθ
    have hmem := hmemU θ (Set.Ioc_subset_Icc_self hθ)
    have h : HasDerivAt (fun θ => f (circleMap ζ ρ θ))
        ((circleMap 0 ρ θ * I) • deriv f (circleMap ζ ρ θ)) θ :=
      ((hf _ hmem).differentiableAt (hUo.mem_nhds hmem)).hasDerivAt.scomp θ
        (hasDerivAt_circleMap ζ ρ θ)
    rw [h.deriv, smul_eq_mul, enorm_mul]
    congr 1
    rw [← ofReal_norm, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  calc ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b)))
      = ‖f (circleMap ζ ρ b) - f (circleMap ζ ρ a)‖ₑ := by
        rw [dist_comm, dist_eq_norm, ofReal_norm]
    _ ≤ ∫⁻ θ in Icc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ :=
        enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd hab
    _ = ∫⁻ θ in Ioc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ := by
        rw [← restrict_Ioc_eq_restrict_Icc]
    _ = ∫⁻ θ in Ioc a b, ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
        setLIntegral_congr_fun measurableSet_Ioc hderiv
    _ = ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end TauCeti
