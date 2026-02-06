[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Dead ends in square-free digit walks

These files accompany the paper [arXiv:2602.05095](https://arxiv.org/abs/2602.05095).

The formal proofs provided in this work were developed and verified using **Lean 4.26.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core libraries.

## Input files

- `dead-ends.tex`: natural language description of the problem
- `task.md`: description of the task to be completed (deferring to `dead-ends.tex`)
- `.environment`: specifies the Lean version

## Output files (Run with Lean 4.26.0)

- `Deadends/problem.lean`: translation of the problem statement into formal language (Lean),
  including the answer itself (computed by AxiomProver)
- `Deadends/solution.lean`: solution in formal language (Lean)

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Seewoo Lee](https://github.com/seewoo5)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)
