# Three-Colour Pythagorean Triples Problem

This repository contains the Lean 4 verification of a new world record for the three-colour Pythagorean triples problem of Erdős and Graham.

**Result.** The interval `{1, ..., 25,000,000}` admits a 3-colouring in which none of the `62,324,099` Pythagorean triples `a² + b² = c²` is monochromatic. This is 2.5 times the previous world record `N = 10⁷` (Heule and Kullmann, *The science of brute force*, Communications of the ACM 60(8), 2017).

The colouring is stored in `data/pyth3col_N25000000.raw.gz`. After decompression it is a file of 25,000,000 bytes, one byte per integer: byte `i` is the colour (`0`, `1`, or `2`) of the integer `i + 1`. Its SHA-256 checksum is `e1500d6c25b116bdf1cb237bd9954b6f5a90b102fb1a77cb754e8d7be153e7d6`.

## Contents

```
.
├── data/
│   ├── pyth3col_N25000000.raw.gz      the colouring (gzip, 5.9 MB)
│   └── SHA256SUMS.txt                 checksum of the decompressed file
├── checker/                           stand-alone Lean 4 program, no Mathlib (6 s)
│   ├── Verify.lean
│   └── lakefile.toml
└── lean/                              Lean 4 + Mathlib proof (Lake project)
    ├── Proofs/Euclid.lean             every Pythagorean triple has Euclid's form
    ├── Proofs/Check.lean              the colouring is triple-free (Pyth.main)
    ├── Proofs/Coincidence.lean        coincidence lemma (Pyth.coincidence)
    ├── Proofs/OnePrime5.lean          exact threshold for 5-adic colourings (Pyth5.threshold)
    ├── Proofs/Axioms.lean             prints the axioms used
    ├── scripts/gen_data.py            builds Proofs/Data.lean from the colouring
    ├── lakefile.toml, lake-manifest.json, lean-toolchain
```

## Requirements

* [elan](https://github.com/leanprover/elan), the Lean version manager. The Lean toolchain (`leanprover/lean4:v4.33.1`) is installed automatically from the `lean-toolchain` files.
* Python 3 for `gen_data.py`.
* For the full proof only: about 10 GB of disk space for Mathlib (`v4.33.1`) and its build cache.

## 1. Quick check with the stand-alone program (about 10 seconds)

The program enumerates every Pythagorean triple through Euclid's formula, reads the colours of its three entries, and counts monochromatic triples.

```bash
gunzip -k data/pyth3col_N25000000.raw.gz
shasum -a 256 data/pyth3col_N25000000.raw          # compare with data/SHA256SUMS.txt

cd checker
lake build
.lake/build/bin/verify ../data/pyth3col_N25000000.raw 25000000
```

Expected output, with exit code `0`:

```
N=25000000 triples=62324099 monochromatic=0 invalid_colour_bytes=0
```

## 2. The full Lean proof

This proves, inside Lean's kernel, that the stored colouring has no monochromatic Pythagorean triple.

```bash
cd lean

# 1. turn the colouring into the Lean module Proofs/Data.lean (a 25 MB string literal)
gunzip -c ../data/pyth3col_N25000000.raw.gz > /tmp/pyth3col_N25000000.raw
python3 -I scripts/gen_data.py /tmp/pyth3col_N25000000.raw Proofs/Data.lean

# 2. download the prebuilt Mathlib and build the proofs
lake exe cache get
lake build
```

`lake build` compiles `Proofs/Euclid.lean`, `Proofs/Check.lean`, `Proofs/Coincidence.lean`, and `Proofs/OnePrime5.lean`. On a laptop, `Proofs/Check.lean` takes about 2 minutes 20 seconds because the check over all 62 million triples runs through `native_decide`.

Print the axioms used by the theorems:

```bash
lake env lean Proofs/Axioms.lean
```

Expected output:

```
'Pyth.main' depends on axioms: [propext, Classical.choice, Quot.sound,
 Pyth.okAll_true._native.native_decide.ax_1_1,
 Pyth.validData_true._native.native_decide.ax_1_1]
'Pyth.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is proved

**`Pyth.main`** (`Proofs/Check.lean`). With `col v` the byte of the stored colouring at position `v - 1` and `N = 25000000`:

```lean
theorem main :
    validData = true ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → a * a + b * b = c * c → c ≤ N →
      ¬ (col a = col b ∧ col b = col c)
```

The first part says that every byte is `0`, `1`, or `2`. The second part says that no Pythagorean triple with hypotenuse at most `N` is monochromatic.

**How the proof is organised.**

* `Pyth.euclid_nat` (`Proofs/Euclid.lean`): every Pythagorean triple has the form `K·(M² − n², 2Mn, M² + n²)` up to the order of the legs, with `gcd(M, n) = 1`. It uses Mathlib's classification of Pythagorean triples.
* `Pyth.sound` (`Proofs/Check.lean`): if the Boolean check `okAll` over the Euclid parameters returns `true`, then no triple is monochromatic. This theorem depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
* `Pyth.okAll_true` and `Pyth.validData_true`: the two finite computations over the data, evaluated by `native_decide`. They are the only places where the extra axioms of the list above enter.

**`Pyth.coincidence`** (`Proofs/Coincidence.lean`). If `a² + b² = c²` and `a ≡ b ≡ c (mod M)` for positive integers `a, b, c`, then `M` divides `a`, `b`, and `c`. It implies that every colouring of the form `f(n mod M)` has a monochromatic triple. It uses only the standard axioms.

**`Pyth5.threshold`** (`Proofs/OnePrime5.lean`). For every `K ≥ 1`, every colouring `F : ℕ → Fin K` of the `5`-adic valuations produces a Pythagorean triple with hypotenuse at most `5^K` whose three valuations have the same colour, and no Pythagorean triple with hypotenuse below `5^K` has `v₅(a) ≡ v₅(b) ≡ v₅(c) (mod K)`. It uses only the standard axioms.

## License

MIT, see `LICENSE`.

## Paper

*Twenty-Five Million Integers, Three Colours, No Pythagorean Triple*, Python Song, October 2026.
