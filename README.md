# On the irrationality of 2-adic zeta values in short intervals: Lean 4 formalization

Lean 4 proof of the main results of *On the irrationality of 2-adic zeta values in short intervals* by Ijtihed Kilani.

```lean
-- lean/RequestProject/TwoAdic/MainFinal.lean
theorem TwoAdicWin.thm_1_1_final : TwoAdicWin.Thm11
theorem TwoAdicWin.cor_1_2_window_final : TwoAdicWin.Cor12Window
theorem TwoAdicWin.cor_1_2_sets_final : TwoAdicWin.Cor12Sets
```

The statements are written out in `lean/RequestProject/TwoAdic/Target.lean`:

- `Thm11`: for even `q ≥ 4` and odd `d` with `q ≤ d + 1` and `7(d + 2) ≤ 10q`, one of
  ζ₂(d+4), ζ₂(d+6), …, ζ₂(d+q) is irrational.
- `Cor12Window`: for every odd `s ≥ 7` there is an odd `j` with `s ≤ j < 1.7s` and ζ₂(j) irrational.
- `Cor12Sets`: ζ₂(7) is irrational, and each of {ζ₂(9), ζ₂(11)}, {ζ₂(11), ζ₂(13), ζ₂(15)} and
  {ζ₂(13), ζ₂(15), ζ₂(17)} contains an irrational number.

The theorems have no hypotheses. They depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
`zeta2 s` is defined through the 2-adic Volkenborn integral as I_{s−1}/((s−1)·2^s), with
I_M = ∫_{ℤ₂} (t + 1/2)^{−M} dt. Its identity with the Kubota–Leopoldt value L₂(s, ω^{1−s}) is classical
(Lai–Sprang–Zudilin, Lemma 2.8) and is not formalized. The formal budget uses slightly relaxed constants
(C̃ ≤ 4.3892 and a margin of at least 0.0129 q², against 4.388838 and 0.013285 q² in the paper).

## Build

Requires Lean 4.28.0 and Mathlib v4.28.0, both pinned in `lean/`.

```
cd lean
lake exe cache get
lake build RequestProject.TwoAdic.MainFinal
lake env lean scripts/print_axioms_final.lean
```

The certificate modules are checked by kernel evaluation and need time and memory.

## Contents

- `lean/`: the Lean project, exactly the 403 modules imported by the final theorems. `TwoAdic/` and `Frame/` are this
  formalization. `Zeta7/` is reused from the author's ζ₂(7) formalization and `Zeta35/` from the ζ₃(5) formalization
  ([doi:10.5281/zenodo.23203596](https://doi.org/10.5281/zenodo.23203596)). In comments, [P] is the ζ₂(7) paper
  ([doi:10.5281/zenodo.23058762](https://doi.org/10.5281/zenodo.23058762)), N the ζ₃(5) paper and II this paper.
- `lean/certificates/`: the denominator certificate and the independent checker `check_uniform.py`, which also
  validates the structure (cells tiling [1/20, 7/2], subcells tiling each cell, signs, sorted weights);
  `enclose_constants.py`, which proves the final numerical bounds in exact rational arithmetic; `test_check_uniform.py`,
  negative controls that must be rejected; and an audit of the homogeneous relaxation (2100 inequalities: 300 random
  class types, seven multipliers each; a corroboration, the lemma is proved in the paper).
- `lean/scripts/`: the generators of the certificate data modules, `cert_dual.py` (checks the generator's dual
  multipliers against `check_uniform.py`), and the axiom printout.
- `checks/`: exact checks of the window arithmetic and of non-vanishing in small cases.
- `verification/VERIFY.md`: build, `#print` and `leanchecker` logs.

## Running the checks

Python 3.10 or later. `checks/exact2.py` also needs `python-flint` (`pip install python-flint`); the other scripts use
the standard library only. Every script exits with a non-zero status on failure.

```
cd lean
python certificates/check_uniform.py certificates/cert_uniform_M96_delta0.4286.json
python certificates/enclose_constants.py certificates/cert_uniform_M96_delta0.4286.json
python certificates/test_check_uniform.py
python certificates/audit_uniform_relaxation_homogeneous.py
python scripts/cert_dual.py
cd ../checks
python check_windows.py
python exact2.py 4 3 4 6 8
python exact2.py 6 5 6 6 8
```

The formalization was produced with Harmonic's Aristotle prover.

## License

MIT
