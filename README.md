# Clean norm-arithmetic dataset

844 validated original examples, grouped by source repository and case ID. Each folder contains actual Lean source files, local dependency modules at their recorded paths, provenance, native target type hashes and standard-axiom receipts.

This branch contains only the dataset and its preparation metadata. It excludes the 298 older compile-only candidates, failed/unvalidated cases, and separately curated or simplified analogues. The original frozen corpus has 3,061 examples; this compiler-accepted subset is biased toward smaller dependency closures and is not claimed representative.

## Shared environment

Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib `2f3c7c8a8949b04a32f9303f59163acffb766996` are pinned in dependency-pins.json. All examples use one shared packages directory; dependencies are not duplicated or bundled. Provision those exact package revisions once, then run:

```sh
python3 prepare.py EXAMPLE_ID --packages /absolute/shared/packages
cd examples/REPOSITORY/EXAMPLE_ID
lake --packages=common-overrides.json build TARGET_PATH.lean:olean
```

The preparation command prints the exact case path and target command. Build configurations are preserved byte-for-byte under build-config/ and relocated only by prepare.py. These exports preserve the previously compiled source bytes; a complete replay of the relocated export has not been run.

## Provenance and limits

manifest.json records original repo, commit, line span, selected declaration, validation receipt hash and case directory. Each example.json includes every local source SHA256, the recorded native target type SHA256 and allowed axioms. The target axioms are limited to propext, Classical.choice and Quot.sound. No original-pin type/semantic equivalence is claimed where no baseline existed.

Source authors retain their original rights. Refer to each source repository at the recorded commit for its applicable license; inclusion here does not apply the norm-arith repository license to third-party source files.
