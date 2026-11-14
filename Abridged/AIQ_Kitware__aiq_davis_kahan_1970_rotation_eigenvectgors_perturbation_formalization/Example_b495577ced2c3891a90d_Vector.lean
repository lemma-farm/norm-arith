module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_b495577ced2c3891a90d_Vector ====
/-
Staged for Tau Ceti, roadmap topic T17.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/RotationSharp.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]).  Davis's classical
proof chooses a unimodular phase making the off-diagonal entry of the 2×2
compression real; the proof here avoids phases entirely — subtracting the two
eigenvector equations and taking real parts collapses the mixed term via
`re (c²·w − s²·conj w) = (c² − s²)·re w`, and the classical half-angle rotation
is realized by test vectors with *polynomial* coefficients
(`1 − 2cs = (c − s)²`, `1 + 2cs = (c + s)²`), so no square roots, inverses, or
normalizations appear anywhere.  No finite-dimensionality is assumed: the
subspace only needs an orthogonal projection.

For the `tan 2θ` theorem, under the vanishing-pinch hypotheses (`H` has no
diagonal blocks with respect to `U ⊕ Uᗮ`) the same block energy identity collapses to
`c·s·(re⟪y,Ty⟫ − re⟪z,Tz⟫) = (c² − s²)·re⟪y,Hz⟫`, and bounding the single
mixed term directly (no rotation, no half-angle) gives
`(b − a)·(‖Px‖·‖x − Px‖) ≤ |‖Px‖² − ‖x − Px‖²|·ε`, i.e. `tan 2θ ≤ 2ε/(b − a)`,
with no smallness assumption on the perturbation.
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-! # The Davis sin 2θ theorem (per-eigenvector, product form)

Let `T` be a symmetric operator, `U` a `T`-invariant subspace on which the
quadratic form of `T` is at least `b * ‖·‖ ^ 2` while on `Uᗮ` it is at most
`a * ‖·‖ ^ 2`, and let `x` be a unit eigenvector of the perturbed operator
`T + H`, with **no assumption on the location of its eigenvalue**.  Writing
`P` for the orthogonal projection onto `U` and `θ` for the angle between `x`
and `U` (`cos θ = ‖P x‖`, `sin θ = ‖x - P x‖`), Davis's sharp two-subspace
estimate bounds the *double* angle:

`sin 2θ ≤ 2 ‖H‖ / (b - a)`.

This file proves it in the product form `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`
(no angle, no division, no positivity side conditions), together with the
`Real.arccos` corollary in the literature-facing `sin 2θ` form.

The proof is elementary and phase-free.  Decompose `x = y + z` with `y = P x`,
`z = x - P x`, and pair the eigenvector equation with `y` and with `z`; the two
resulting scalar equations combine (eliminating the eigenvalue) into the real
identity

`‖z‖² re ⟪y, T y⟫ - ‖y‖² re ⟪z, T z⟫ + ‖z‖² re ⟪y, H y⟫ - ‖y‖² re ⟪z, H z⟫
+ (‖z‖² - ‖y‖²) re ⟪y, H z⟫ = 0`,

with no complex phase alignment needed (`re (c² w - s² conj w) = (c² - s²) re w`
identically).  Testing the quadratic form of `H` against the two orthogonal
vectors `s(c-s) • y + c(c+s) • z` and `-s(c+s) • y + c(c-s) • z` (where
`c = ‖y‖`, `s = ‖z‖`; each has squared norm `2c²s²` since `c² + s² = 1`)
recovers the left-hand side of the identity and yields
`4 c³s³ (b - a) ≤ 4 c²s² ε`.

## Main results

* `TauCeti.sin_two_theta_le`: the product form
  `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ ε`.
* `TauCeti.sin_two_arccos_le`: the literature-facing form
  `(b - a) * sin (2 * arccos ‖P x‖) ≤ 2 * ε`.
* `TauCeti.tan_two_theta_le` / `…_of_mem`: Davis's `tan 2θ` theorem under
  the vanishing-pinch hypotheses, in product form
  `(b - a) * (‖P x‖ * ‖x - P x‖) ≤ |‖P x‖ ^ 2 - ‖x - P x‖ ^ 2| * ε`.
* `TauCeti.map_mem_orthogonal_of_forall_map_mem`: the orthogonal complement
  of an invariant subspace of a symmetric operator is invariant.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*,
  J. Math. Anal. Appl. 6 (1963), 159–173 (the sharp two-subspace estimate).
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46 (the sin 2Θ theorem).

## Sources

The double-angle identity for the vector case follows Davis--Kahan's
`sin 2Θ`/`tan 2Θ` development; see
`prose/distilled_literature/DavisKahan1970_part_III.tex` and, for the branch
selection this avoids, `prose/distilled_literature/DoubleAngle_branch_selection_dossier.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/DoubleAngle/Vector.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/
public section
namespace TauCeti
open scoped InnerProductSpace
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T H : E →ₗ[𝕜] E}


set_option linter.unusedVariables false in
theorem tan_two_theta_le_of_mem (hT : T.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} (hUinv : ∀ u ∈ U, T u ∈ U) {a b ε : ℝ}
    (hb : ∀ u ∈ U, b * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_𝕜)
    (ha : ∀ w ∈ Uᗮ, RCLike.re ⟪T w, w⟫_𝕜 ≤ a * ‖w‖ ^ 2)
    (hε : ∀ v, ‖H v‖ ≤ ε * ‖v‖)
    (hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0)
    (hHUperp : ∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0)
    {y z : E} (hyU : y ∈ U) (hzU : z ∈ Uᗮ) (hx : ‖y + z‖ = 1) {μ : ℝ}
    (hμ : T (y + z) + H (y + z) = (μ : 𝕜) • (y + z)) 
    (h_TauCeti_eigenvector_block_energy_identity : ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] {T H : E →ₗ[𝕜] E},
      T.IsSymmetric →
        H.IsSymmetric →
          ∀ {U : Submodule 𝕜 E},
            (∀ u ∈ U, (T : E → E) u ∈ U) →
              ∀ {y z : E},
                y ∈ U →
                  z ∈ Uᗮ →
                    ∀ {μ : ℝ},
                      (T : E → E) (y + z) + (H : E → E) (y + z) = (↑μ : 𝕜) • (y + z) →
                        ‖z‖ ^ 2 * (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 y ((T : E → E) y)) -
                                  ‖y‖ ^ 2 * (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 z ((T : E → E) z)) +
                                ‖z‖ ^ 2 * (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 y ((H : E → E) y)) -
                              ‖y‖ ^ 2 * (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 z ((H : E → E) z)) +
                            (‖z‖ ^ 2 - ‖y‖ ^ 2) *
                              (RCLike.re : 𝕜 → ℝ) (Inner.inner 𝕜 y ((H : E → E) z)) =
                          0)
    :
    (b - a) * (‖y‖ * ‖z‖) ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * ε := by
  have hε0 : 0 ≤ ε := by
    have h := hε (y + z)
    rw [hx, mul_one] at h
    exact (norm_nonneg _).trans h
  have key := h_TauCeti_eigenvector_block_energy_identity hT hH hUinv hyU hzU hμ
  have hyH : RCLike.re ⟪y, H y⟫_𝕜 = 0 := by rw [hHU y hyU y hyU]; simp
  have hzH : RCLike.re ⟪z, H z⟫_𝕜 = 0 := by rw [hHUperp z hzU z hzU]; simp
  have hby : b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_𝕜 := by
    have h := hb y hyU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have haz : RCLike.re ⟪z, T z⟫_𝕜 ≤ a * ‖z‖ ^ 2 := by
    have h := ha z hzU
    rwa [← inner_conj_symm, RCLike.conj_re] at h
  have hmix : |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖y‖ * ‖z‖ * ε :=
    calc |RCLike.re ⟪y, H z⟫_𝕜| ≤ ‖⟪y, H z⟫_𝕜‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖y‖ * ‖H z‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε * ‖z‖) := by gcongr; exact hε z
      _ = ‖y‖ * ‖z‖ * ε := by ring
  -- The vanishing diagonal blocks collapse the block energy identity.
  have hcollapse : ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜
      = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := by
    rw [hyH, hzH] at key
    linear_combination key
  -- The two quadratic-form bounds give the lower bound on the collapsed LHS.
  have hlow : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := by
    nlinarith [mul_le_mul_of_nonneg_left hby (sq_nonneg ‖z‖),
      mul_le_mul_of_nonneg_left haz (sq_nonneg ‖y‖)]
  -- Chain: `‖y‖²‖z‖²(b-a) ≤ (Y-Z)·W ≤ |Y-Z|·‖y‖‖z‖·ε`.
  have hchain : ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
      ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) :=
    calc ‖y‖ ^ 2 * ‖z‖ ^ 2 * (b - a)
        ≤ ‖z‖ ^ 2 * RCLike.re ⟪y, T y⟫_𝕜 - ‖y‖ ^ 2 * RCLike.re ⟪z, T z⟫_𝕜 := hlow
      _ = (‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜 := hcollapse
      _ ≤ |(‖y‖ ^ 2 - ‖z‖ ^ 2) * RCLike.re ⟪y, H z⟫_𝕜| := le_abs_self _
      _ = |‖y‖ ^ 2 - ‖z‖ ^ 2| * |RCLike.re ⟪y, H z⟫_𝕜| := abs_mul _ _
      _ ≤ |‖y‖ ^ 2 - ‖z‖ ^ 2| * (‖y‖ * ‖z‖ * ε) := by gcongr
  -- Divide by `‖y‖‖z‖`; degenerate case handled by nonnegativity.
  rcases (mul_nonneg (norm_nonneg y) (norm_nonneg z)).eq_or_lt with hn | hn
  · rw [← hn, mul_zero]
    exact mul_nonneg (abs_nonneg _) hε0
  · have hh : (‖y‖ * ‖z‖) * ((b - a) * (‖y‖ * ‖z‖))
        ≤ (‖y‖ * ‖z‖) * (|‖y‖ ^ 2 - ‖z‖ ^ 2| * ε) := by
      linear_combination hchain
    exact le_of_mul_le_mul_left hh hn
end TauCeti
