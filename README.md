# Clean norm-arithmetic examples

844 recorded native-validated examples from 130 source repositories, with their local support modules and provenance. This is the dataset branch of the Tomas Ortega `norm-arith` fork.

## Layout

```text
Examples/
  owner__repository/
    Examples/Example_<id>_<original-file>.lean
    Dependencies/<source-and-configuration-variant>/...
manifest.json
lakefile.toml
lake-manifest.json
lean-toolchain
docs/                         # static GitHub Pages explorer
```

Each example file contains the actual Lean declarations and proof; it is not an import-only wrapper. Dependency variants prevent conflicting original commits or proof/configuration variants from being silently merged. Identical source/configuration graphs share support modules within a repository. The short ID disambiguates examples from the same original filename.

Blank padding outside strings and block comments has been removed. Every example's highlighted proof lines are checked against the selected original source, ignoring only removed blank lines. `manifest.json` records the original repository, commit, file and interesting line range, the validated source identity, the final exported path/hash, and the new interesting line range. Local imports and source options are adjusted for the shared build; those transformations are recorded separately from the selected proof text.

## Build the suite

The shared environment is pinned to Lean `v4.36.0-rc1` and Mathlib commit `2f3c7c8a8949b04a32f9303f59163acffb766996`.

```sh
lake update
lake exe cache get
lake build
```

`lake build` selects all 844 example modules. It builds their reachable support dependencies, without an umbrella import that would combine conflicting original global declarations. The nondefault dependency library supplies module ownership; it is not an instruction to build every unrelated retained support file.

Historical per-example `.source` build snapshots are not required by this layout and are omitted. The common configuration and manifest replace them. Original native validation does not by itself certify the rewritten layout; see the committed validation summary for the actual checks performed. Source configurations written in Lean rather than TOML have a separately recorded option-routing limitation; no unsupported setting is silently claimed preserved.

## Browse the dataset

The static explorer is in `docs/`. In GitHub repository **Settings → Pages**, choose branch **examples_dataset**, folder **/docs**. It provides repository and mathematical-pattern search, selected-line highlighting, source links, and validation/provenance information. Source files load lazily from the same published branch. Committing `docs/` does not enable repository hosting settings automatically.

## Scope and licensing

This branch excludes failed/unvalidated examples, older compile-only baselines without the stricter target evidence, and separately curated simplified analogues. Native target type hashes and standard-axiom evidence refer to the recorded original extraction. A full original-pin semantic-equivalence claim is not made, nor is this compiler-accepted subset claimed statistically representative.

The example sources retain their original authors' licensing terms. Consult the recorded source repositories at their pinned commits; the upstream `norm-arith` license is not automatically a license for every third-party example.
