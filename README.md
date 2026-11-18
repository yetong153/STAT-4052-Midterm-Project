# STAT-4052-Midterm-Project

## The Unique Minimizer of Ridge Regression
STAT 4052, Fall 2026. Chelsea Zhang, Sherry Meng, Xiaodi Yuan, and Xiaoyi Chang.

For any finite real design matrix and response vector, a positive squared L2 penalty on every coefficient gives a unique global minimizer. The design matrix may have any rank. No additional external axioms are used beyond the stated theorem hypotheses and the standard Lean/mathlib foundations.

## Build
With Git and elan installed, run these commands from this directory. The first command obtains compiled dependencies for the full mathlib import.

```sh
lake exe cache get
lake build
lake env lean RidgeUniqueMinimizer.lean
```

The toolchain is Lean 4.36.0. The Lake configuration pins mathlib v4.36.0 at fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The manifest pins transitive dependencies.

## Source and proof
RidgeUniqueMinimizer.lean contains the entire project proof. In the RidgeRegression namespace, normalMatrix_posDef and normalMatrix_quadratic_pos give positive definiteness. normalMatrix_invertible establishes the inverse identity. exists_normal_solution constructs the candidate. loss_sub_eq expands the residual and penalty at a normal-equation solution. loss_lt_of_ne proves that every distinct competitor has strictly higher loss. The final theorem ridge_unique_minimizer combines existence and uniqueness. Its axiom audit lists propext, Classical.choice, and Quot.sound.

AI assistance: OpenAI Codex assisted with exposition, Lean development and verification, documentation, and LaTeX preparation.
