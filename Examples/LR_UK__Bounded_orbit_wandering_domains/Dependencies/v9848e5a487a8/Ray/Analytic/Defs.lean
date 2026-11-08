module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Basic
/-!
## Analytic definitions, allowing minimal public imports
-/
open Classical
open Set
noncomputable section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
/-!
## Order definitions
-/
/-- The order of a zero at a point.
    We define this in terms of the function alone so that expressions involving order can
    depend only on `f`. -/
@[expose] public def orderAt (f : 𝕜 → E) (c : 𝕜) : ℕ :=
  if p : AnalyticAt 𝕜 f c then (choose p).order else 0
/-- The leading nonzero coefficient of `f`'s power series -/
@[expose] public def leadingCoeff (f : 𝕜 → E) (c : 𝕜) : E :=
  ((Function.swap dslope c)^[orderAt f c]) f c
/-- The power series of `(z - c) • f z` -/
def FormalMultilinearSeries.unshift' (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) :
    FormalMultilinearSeries 𝕜 𝕜 E :=
  ((ContinuousLinearMap.smulRightL 𝕜 𝕜 E (ContinuousLinearMap.id 𝕜 𝕜)).compFormalMultilinearSeries
        p).unshift c
/-- The power series of `(z - c)^n • f z` -/
def FormalMultilinearSeries.unshiftIter (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :=
  (fun p ↦ FormalMultilinearSeries.unshift' p (0 : E))^[n] p
/-!
## Product definitions
-/
/-- For all z, `Πₙ f n z` converges absolutely to `g z` (analogous to `HasSumOn`) -/
@[expose] public def HasProdOn (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasProd (fun n ↦ f n z) (g z)
/-- The product of `f` converges absolutely to something (analogous to `Summable`) -/
@[expose] public def ProdExists (f : ℕ → ℂ) : Prop :=
  ∃ g, HasProd f g
/-- The limit of an infinite product if it exists, or `0` -/
@[expose] public noncomputable def tprodOn (f : ℕ → ℂ → ℂ) := fun z ↦ tprod fun n ↦ f n z
/-- The limit of a parameterized infinite product if it exists, or `0` -/
@[expose] public def ProdExistsOn (f : ℕ → ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → ProdExists fun n ↦ f n z
/-- If a product has a particular limit, it has some limit -/
public theorem HasProd.prodExists {f : ℕ → ℂ} {g : ℂ} (h : HasProd f g) : ProdExists f :=
  ⟨g, h⟩
/-- `tprodOn` is the product on `s` if it exists on `s` -/
public theorem HasProdOn.tprodOn_eq {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} :
    HasProdOn f g s → ∀ z, z ∈ s → tprodOn f z = g z := fun h z zs ↦ (h z zs).tprod_eq
