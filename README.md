# Demazure Operators and Lean

This project formalizes the definition of Demazure operators and some fundamental properties of Coxeter groups. It is part of my Master's thesis, *Demazure Operators and Lean*, submitted to the University of Bonn. The full manuscript can be found in the file `master_thesis.pdf` or downloaded [here](https://github.com/bolito2/DemazureOperatorsLean/blob/b98a475967a904af0ab9471b86e1d3ccc8d223a2/master_thesis.pdf).

The documentation for the Lean code can be viewed at [demazure-docs](https://bolito2.github.io/DemazureOperatorsLean/DemazureOperators/Demazure.html) or built locally following the instructions below.

## Contents

- `Demazure.lean`: Defines Demazure operators and proves basic properties.
- `DemazureAux.lean`: Contains an auxiliary definition tailored for combinatorial proofs and results about Demazure operators (including equivalence to the original definition).
- `DemazureAuxRelations.lean`: Establishes combinatorial results using the auxiliary definition.
- `DemazureRelations.lean`: Translates results from `DemazureAuxRelations.lean` to the original definition.
- `StrongExchange.lean`: Proves results about Coxeter groups, culminating in the Strong Exchange Theorem.
- `Matsumoto.lean`: Defines nil and braid moves and provides combinatorial lemmas for proving Matsumoto’s theorem under specific Coxeter group conditions.
- `SymmetricGroup.lean`: Sketches a proof that `S_{n+1}` is a Coxeter group and verifies that it satisfies Matsumoto’s theorem.
- `DemazureWords.lean`: Defines Demazure operators over arbitrary elements of `S_{n+1}`, building on previous results and Matsumoto’s theorem.

## Usage Instructions

### Requirements
To use this project, install [Lean 4](https://leanprover-community.github.io/get_started.html).

### Installation
To install the project dependencies, run:

```bash
lake exe cache get
```

### Building the Documentation
To generate the documentation with `doc-gen4`, run:

```bash
lake -R -Kenv=dev build DemazureOperators:docs
```

The generated documentation will be located in `.lake/build/doc` and can be served with any HTTP server. Note that opening the HTML files directly may not work in some browsers (refer to [doc-gen4](https://github.com/leanprover/doc-gen4) for more details).