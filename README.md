# LinearLogic

Formalization of linear logic and related concepts.

## Documentation
https://formalizedformallogic.github.io/LinearLogic/docs

## Table of sequnet calculi

| | Propositional | First-Order | Second-Order |
|-|---------------|-------------|--------------|
| Linear Logic | [$\mathbf{LL^0}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/LL/Propositional.lean) | [$\mathbf{LL^1}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/LL/FirstOrder/Calculus.lean) | - |
| Multiplicative Linear Logic | [$\mathbf{MLL^0}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/MLL/Propositional.lean) | - | - |
| Multiplicative Exponential Linear Logic | [$\mathbf{MELL^0}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/MELL/Propositional.lean) | - | - |
| Constructive Classical Logic | [$\mathbf{LC^0}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/LC/Propositional.lean) | - | - |
| Elementary Linear Logic | [$\mathbf{ELL^0}$](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/ELL/Propositional.lean) | - | - |
| Variants of LK | [$\mathbf{LK^0}$](https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Propositional/Tait/Calculus.lean) | [$\mathbf{LK^1}$](https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/FirstOrder/Basic/Calculus.lean) | [$\mathbf{LK^2}$](https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/SecondOrder/Derivation.lean) |

## Cut elimination

- $\mathbf{LL^0}$: [`LL.hauptsatz`](https://github.com/FormalizedFormalLogic/LinearLogic/blob/main/LinearLogic/LL/CutElimination.lean) — structural cut elimination following Pfenning's *Structural cut elimination in linear logic* (via admissibility of cut and of a persistent multicut in the cut-free calculus), with consistency as a corollary.

