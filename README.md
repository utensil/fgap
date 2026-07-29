![FGAP banner](assets/fgap-banner.png)

# FGAP

FGAP is read "F-gap," for the foundational gap between established mathematical
tools and open questions about physical structures, especially beyond the
Standard Model. It is also a coined acronym for Foundational Group Algebras
(for) Physics.

This repository studies mathematical structures that may help us understand
physical structures more deeply. It does not construct or claim a physical
theory. Its Lean library is developed alongside expository notes and worked
calculations.

## Theme

The question is whether group algebras provide a useful organizing level for
structures that physics usually introduces separately. Finite groups and their
real group algebras offer a controlled setting for studying actions,
representations, idempotents, simple components, and explicit maps into familiar
algebras. The aim is to make these relationships explicit through constructions,
representations, and proofs.

Group algebras are the current working hypothesis. The mathematical scope remains
broader: the project will also study its relationships with Clifford and Lie
algebras, twisted group algebras, quaternionic structures, operator algebras,
and representation categories where they clarify the question or show the
limits of an associative approach.

Each candidate is examined on its own mathematical terms: its definitions,
representations, invariants, decompositions, and relationships with other
structures. When a physics-motivated correspondence is discussed, the
representation, algebra map, kernel, real form, involution, or other required
data must be stated explicitly.

## Approach

Foundational physics supplies the motivation; mathematical structures are the
subject. Structural hypotheses are turned into small, testable vertical slices,
grounded in scholarly sources and explicit calculations, and examined through
formalization as theory modeling to expose hidden assumptions. The workflow is
informed, but not dictated, by established reference projects.

The inquiry is not limited to elaborating a single source or assigning one
mathematical structure to each physical theory. Candidate structures are
compared against shared requirements and constraints, so that useful
correspondences, limitations, and relationships between different mathematical
choices can be stated precisely.

## Origins and guiding intuition

Clifford algebras (a.k.a. Geometric Algebra in the context of work pioneered by
David Hestenes) were considered as a potential route to this question. This
direction was inspired by Chris Doran and Anthony Lasenby's
[*Geometric Algebra for Physicists*](https://doi.org/10.1017/CBO9780511807497),
which later led to
[`pygae/lean-ga`](https://github.com/pygae/lean-ga) and the paper
[*Formalizing Geometric Algebra in Lean*](https://arxiv.org/abs/2110.03551).
That paper was only the beginning of Eric Wieser's PhD thesis,
[*Formalizing Clifford algebras and related constructions in the Lean theorem
prover*](https://www.repository.cam.ac.uk/items/9ad1ac65-48c4-49cd-a00c-3cec6397a93b).
There is still ongoing work in mathlib in the same vein, and it can be viewed as
an example of formalization as theory modeling, where formalization recasts
mathematical theory through representations shaped by the possibilities and
constraints of the theorem prover's underlying type theory.

The shared abbreviation GA is a happy coincidence: here it means group algebras,
and the search extends beyond the limitations of Clifford algebras.

[Rob Wilson's group-theoretic work](https://robwilson1.wordpress.com/) supplies
concrete examples of using finite groups to probe physical structures.
Inspiration is taken from that work alongside representation theory and
exploratory work in other directions, including non-associative algebras.
Across these sources, we separate mathematical constructions from physical
hypotheses.

## Components

- Forest notes support theory building, mathematical foundations, and focused
  informal proofs and calculations.
- The Lean library checks definitions, dependencies, constructions, and proofs.
- A Verso Blueprint records theorem dependencies and nontrivial adaptations
  made for formalization.

To build the Lean library:

```bash
lake exe cache get
lake build
```

## Conventions

The Lean code and project workflow follow applicable conventions from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).
These conventions are adapted for this project's approach; see
[`AI_POLICY.md`](AI_POLICY.md) and [`AGENTS.md`](AGENTS.md).
