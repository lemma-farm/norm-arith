import Examples.SauersML__group_approximation.Dependencies.v80e18e28bc98.GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RealProjectiveSpace
set_option warningAsError true
/-!
# The equatorial inclusions `Sⁿ ↪ Sⁿ⁺¹` and `RPⁿ ↪ RPⁿ⁺¹`

This file builds the first piece of the cell-structure / long-exact-sequence
infrastructure for the mod-two cohomology computation of `RPⁿ`: the genuine
*equatorial inclusion*

```text
Sⁿ ↪ Sⁿ⁺¹,        RPⁿ ↪ RPⁿ⁺¹,
```

obtained from the standard isometric embedding
`EuclideanSpace ℝ (Fin (n+1)) ↪ EuclideanSpace ℝ (Fin (n+2))` that pads a vector
with a final zero coordinate (`Fin.snoc · 0`).

Implemented here:

* `inclLin n` — the padding linear map, and `inclIso n` — its upgrade to a
  genuine `LinearIsometry` (norm-preserving, via inner-product preservation);
* `sphereInclusion n : C(Sⁿ, Sⁿ⁺¹)` — the equatorial sphere inclusion, with the
  computation rule `sphereInclusion_apply_coe`, **oddness/equivariance**
  `sphereInclusion_odd`, injectivity `sphereInclusion_injective`, and the fact
  that it is a topological embedding `sphereInclusion_isEmbedding`;
* `rpInclusion n : C(RPⁿ, RPⁿ⁺¹)` — the descended projective inclusion, with the
  defining square `rpInclusion_proj` (`ī ∘ proj = proj ∘ i`), its bundled form
  `rpInclusion_comp_proj`, and injectivity `rpInclusion_injective`.

These are genuine topological objects with no placeholder content. They provide
the inclusion of the preferred CW/LES route `RPⁿ⁻¹ ↪ RPⁿ`; the induced pullback
on singular cohomology is built in `RPnInclusionCohomology.lean`.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
/-- The padding linear map `EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ
(Fin (n+2))` appending a final zero coordinate, via `Fin.snoc · 0`. -/
def inclLin (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  toFun x := (WithLp.equiv 2 _).symm (Fin.snoc ((WithLp.equiv 2 _) x) (0 : ℝ))
  map_add' x y := by
    ext i; refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp [Fin.snoc_castSucc]
  map_smul' c x := by
    ext i; refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp [Fin.snoc_castSucc]
def inclIso (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (inclLin n).isometryOfInner (by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [Fin.sum_univ_castSucc]
    simp [inclLin, Fin.snoc_castSucc])
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
