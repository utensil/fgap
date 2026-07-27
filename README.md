# FGAP

Foundational Group-Algebraic Physics (FGAP) is a Lean library about group
algebras and related algebraic structures.

FGAP began with a search for mathematical structures beyond Clifford and Lie
algebras for physics beyond the Standard Model. Group algebra is the current
organizing candidate: the program will test whether familiar algebras can be
recovered from it within one representation-theoretic setting.

The first development track studies finite group algebras over real and general
coefficient rings: basis elements, subgroup averages, idempotents, module
splittings, and explicit examples. Questions from physics motivate the choice of
examples. They do not turn algebraic decompositions into physical evidence.

[Rob Wilson's group-theoretic writing](https://robwilson1.wordpress.com/) is one
source of problems, alongside other mathematical work such as
[John Baez's survey of the octonions](https://arxiv.org/abs/math/0105155).
FGAP is not tied to any one physical program. Definitions and proofs are checked
independently in Lean, and conjectural physics interpretations stay separate
from proved mathematics.

The Lean layout follows [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
where its conventions apply.
