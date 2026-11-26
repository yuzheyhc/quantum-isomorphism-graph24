# Quantum graph isomorphism at order 24

*The Minimum Order for Quantum Isomorphism of Nonisomorphic Graphs*

Can two players win the graph isomorphism game with probability one even when the two graphs are not isomorphic? A perfect classical strategy would give an actual isomorphism. Entangled players can nevertheless win on a particular pair of 24-vertex graphs constructed from the magic square. The paper determines the first order at which this can happen.

Let $m_t$ be the least number of vertices per graph in a nonisomorphic pair admitting a perfect isomorphism-game strategy in model $t$. For finite simple undirected graphs the result is

$$
m_{\mathrm{qc}}=m_{\mathrm{fin}}=24 ,
$$

where $\mathrm{qc}$ is the commuting-operator model and $\mathrm{fin}$ is the finite-dimensional tensor-product model. The lower bound uses the relations on ordered pairs that a perfect strategy preserves. Incidence matrices constrain the vertex bijections on different fibers. The remaining configurations are settled by small-order classifications and finite checks in Lean. The paper also determines the quantum-isomorphism class of the standard magic-square graph and gives the sharp order range in which planar homomorphism counts distinguish all graphs.

## 中文简介

两张图如果经典不同构，最少各有多少个顶点，玩家仍能在图同构博弈中完美获胜？答案是 **24**。下界在允许无限维空间的对易算子模型中成立。达到上界的魔方阵图对已有一个有限维完美策略。论文的核心问题是如何把各个顶点纤维上的局部对应拼成同一个双射。正文给出矩阵推导，第 16 至 23 阶归约后的有限情形由 Lean 工程处理。

## Paper and proofs

| File | What to look for |
| --- | --- |
| [Read the paper](paper/QuantumGraph24.pdf) · [LaTeX source](paper/main.tex) | The isomorphism game, fiber reconstruction, the eight lower-bound orders, and the extremal pair. |
| [Minimum-order theorem](lean/src/Minimum24.lean) | Lean declaration `QGI.exactMinimum24`. |
| [Verification entry point](lean/Verify.lean) | The statements for orders 16 through 23, the explicit 24-vertex example and the expanded conclusion with its dependencies. |
| [Magic-square strategy](lean/src/Upper24Hilbert.lean) | A perfect strategy for the concrete pair at order 24. |
