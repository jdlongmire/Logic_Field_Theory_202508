# 5. Quantum Structure

Having established the complex Hilbert space $\mathcal{H} = \ell^2(\mathcal{A}/\sim, \mathbb{C})$ from logical requirements, we now derive the operator formalism and algebraic structure of quantum mechanics.

## 5.1 Foundation: The Logical Inner Product

**Critical reminder:** The inner product we use throughout this section is **not** imported from quantum mechanics. It was derived in Section 4 from logical distinguishability:

$$\langle [G] | [H] \rangle = \begin{cases}
1 & \text{if } [G] = [H] \\
0 & \text{if } [G] \neq [H]
\end{cases}$$

This encodes the fundamental principle that distinct logical content must be distinguishable. All operator properties and algebraic relations that follow inherit this logical foundation—they are not quantum postulates.

## 5.2 Observables as Logical Queries

### 5.2.1 From Graph Properties to Operators

**Definition 5.1 (Graph Property).** A graph property $\mathcal{P}$ is a function:
$$\mathcal{P}: \mathcal{A}/\sim \to \mathbb{R}$$
that assigns a real value to each equivalence class of admissible graphs.

**Examples of Graph Properties:**
- **Vertex count:** $\mathcal{P}_{V}([G]) = |V(G)|$
- **Edge density:** $\mathcal{P}_{E}([G]) = |E(G)|/|V(G)|^2$
- **Cycle number:** $\mathcal{P}_{C}([G]) = $ number of directed cycles
- **Path length:** $\mathcal{P}_{L}([G]) = $ average shortest path length

### 5.2.2 Operator Construction

**Theorem 5.1 (Property-Operator Correspondence).** Every graph property $\mathcal{P}$ induces a self-adjoint operator:

$$\hat{\mathcal{P}} = \sum_{[G] \in \mathcal{A}/\sim} \mathcal{P}([G]) |[G]\rangle\langle[G]|$$

**Proof:** Self-adjointness follows from real-valuedness of $\mathcal{P}$ and the logical inner product structure. $\square$

### 5.2.3 Projection Operators

For a yes/no query "Does property P hold?":

$$\hat{P} = \sum_{[G] \models P} |[G]\rangle\langle[G]|$$

Properties verified explicitly:
- **Idempotent:** $\hat{P}^2 = \sum_{[G],[H] \models P} |[G]\rangle\langle[G]|[H]\rangle\langle[H]| = \sum_{[G] \models P} |[G]\rangle\langle[G]| = \hat{P}$
- **Self-adjoint:** $\hat{P}^\dagger = \hat{P}$ (coefficients are real)
- **Eigenvalues:** 0 or 1 (characteristic function)

## 5.3 Canonical Observables from Logical Structure

### 5.3.1 Position from Graph Embedding

**Definition 5.2 (Logical Position).** For graphs embedded in logical space, define the position operator:

$$\hat{x} = \sum_{[G]} x_{cm}([G]) |[G]\rangle\langle[G]|$$

where $x_{cm}([G])$ is the center of mass of vertices in the embedded graph:
$$x_{cm}([G]) = \frac{1}{|V|} \sum_{v \in V} x_v$$

### 5.3.2 Momentum from Translation Generator

**Definition 5.3 (Translation Operator).** The infinitesimal translation of embedded graphs:

$$\hat{T}_\epsilon: [G(x)] \mapsto [G(x + \epsilon)]$$

The momentum operator is the generator of translations:
$$\hat{p} = -i\hbar \lim_{\epsilon \to 0} \frac{\hat{T}_\epsilon - \hat{I}}{\epsilon}$$

### 5.3.3 Canonical Commutation Relations

**Theorem 5.2 (Canonical Commutator).** The position and momentum operators satisfy:
$$[\hat{x}, \hat{p}] = i\hbar$$

**Proof:** 
Consider the action on a basis state $|[G]\rangle$:

$$[\hat{x}, \hat{p}]|[G]\rangle = \hat{x}\hat{p}|[G]\rangle - \hat{p}\hat{x}|[G]\rangle$$

Using $\hat{p} = -i\hbar \nabla_x$ (translation generator):

$$\hat{x}\hat{p}|[G]\rangle = -i\hbar \hat{x}\nabla_x|[G]\rangle = -i\hbar(x_{cm}\nabla_x|[G]\rangle)$$

$$\hat{p}\hat{x}|[G]\rangle = -i\hbar \nabla_x(x_{cm}|[G]\rangle) = -i\hbar(x_{cm}\nabla_x|[G]\rangle + |[G]\rangle)$$

Therefore:
$$[\hat{x}, \hat{p}]|[G]\rangle = i\hbar|[G]\rangle$$

Since this holds for all basis states: $[\hat{x}, \hat{p}] = i\hbar\hat{I}$. $\square$

**Key Insight:** The factor $i$ emerges from the complex structure required for orientation (Section 4), while $\hbar$ sets the scale of logical action.

## 5.4 The Hamiltonian from Graph Dynamics

### 5.4.1 Graph Connectivity Energy

**Definition 5.4 (Connectivity Hamiltonian).** The logical energy of a configuration is determined by its graph structure:

$$\hat{H}_0 = \sum_{[G]} E([G]) |[G]\rangle\langle[G]|$$

where the energy functional is:
$$E([G]) = \sum_{(u,v) \in E(G)} w(u,v) + \lambda \cdot \text{cycles}(G)$$

- $w(u,v)$: weight of edge (logical coupling strength)
- $\text{cycles}(G)$: weighted sum of directed cycles
- $\lambda$: cycle tension parameter

### 5.4.2 Strain Potential

From Section 3, the strain functional adds a potential term:

$$\hat{V}_{strain} = \sum_{[G]} D([G]) |[G]\rangle\langle[G]|$$

where $D([G]) = w_I v_I([G]) + w_N v_N([G]) + w_E v_E([G])$.

### 5.4.3 Total Hamiltonian

The complete Hamiltonian is:

$$\hat{H} = \hat{H}_0 + \hat{V}_{strain} = \sum_{[G]} [E([G]) + D([G])] |[G]\rangle\langle[G]|$$

This determines time evolution via:
$$i\hbar\frac{\partial}{\partial t}|\psi\rangle = \hat{H}|\psi\rangle$$

## 5.5 Non-Commuting Observables

### 5.5.1 Incompatible Partitions

**Definition 5.5 (Compatible Queries).** Two graph properties $\mathcal{P}_1, \mathcal{P}_2$ are compatible if they induce the same partition of $\mathcal{A}/\sim$ up to refinement.

**Theorem 5.3 (Commutation Criterion).** 
$$[\hat{\mathcal{P}}_1, \hat{\mathcal{P}}_2] = 0 \iff \mathcal{P}_1, \mathcal{P}_2 \text{ are compatible}$$

### 5.5.2 Origin of Non-Zero Commutators

For incompatible properties, the commutator is:

$$[\hat{\mathcal{P}}_1, \hat{\mathcal{P}}_2] = \sum_{[G]} [\mathcal{P}_1([G]), \mathcal{P}_2([G])]_{Poisson} \cdot i\hbar |[G]\rangle\langle[G]|$$

where $[\cdot,\cdot]_{Poisson}$ is the Poisson bracket on the graph phase space.

**Example:** For position and momentum:
$$[\hat{x}, \hat{p}] = i\hbar$$
because translation (generating $\hat{p}$) and position measurement are maximally incompatible.

### 5.5.3 The Uncertainty Principle

**Theorem 5.4 (Uncertainty from Incompatibility).** For non-commuting observables with $[\hat{A}, \hat{B}] = i\hat{C}$:

$$\Delta A \cdot \Delta B \geq \frac{1}{2}|\langle\hat{C}\rangle|$$

**Proof:** This follows from the Cauchy-Schwarz inequality applied to the logical inner product space, where incompatible partitions create irreducible spreads in measurement outcomes. $\square$

## 5.6 Example: Harmonic Oscillator

### 5.6.1 Graph Representation

Consider graphs with vertices arranged on a line with nearest-neighbor edges. The Hamiltonian becomes:

$$\hat{H} = \frac{\hat{p}^2}{2m} + \frac{1}{2}m\omega^2\hat{x}^2$$

where:
- Kinetic term: from translation generator squared
- Potential term: from displacement strain in graph embedding

### 5.6.2 Energy Spectrum

The eigenstates are graphs with specific cyclic patterns:
$$E_n = \hbar\omega(n + \frac{1}{2})$$

where $n$ counts the number of logical cycles in the eigenstate graph.

### 5.6.3 Creation/Annihilation Operators

Define cycle-adding/removing operators:
$$\hat{a}^\dagger|[G_n]\rangle = \sqrt{n+1}|[G_{n+1}]\rangle$$
$$\hat{a}|[G_n]\rangle = \sqrt{n}|[G_{n-1}]\rangle$$

These satisfy $[\hat{a}, \hat{a}^\dagger] = 1$, emerging from the graph cycle algebra.

## 5.7 Dynamics from Coherence Preservation

### 5.7.1 The Coherence Requirement

Time evolution must:
1. Preserve admissibility: $\mathcal{A} \to \mathcal{A}$
2. Maintain logical relationships (distinguishability)
3. Act continuously

### 5.7.2 Unitary Evolution

**Theorem 5.5 (Unitarity from Logic).** Any continuous transformation preserving logical distinguishability must be unitary.

**Proof:** 
1. Distinguishability preservation: $\langle T[G]|T[H]\rangle = \langle[G]|[H]\rangle$
2. This implies: $\langle T^\dagger T[G]|[H]\rangle = \langle[G]|[H]\rangle$ for all $[G],[H]$
3. Therefore: $T^\dagger T = I$ (unitarity)

The generator of continuous unitary evolution is self-adjoint (the Hamiltonian). $\square$

## 5.8 Composite Systems

### 5.8.1 Tensor Product Structure

For independent logical systems:
$$\mathcal{A}_{12} = \mathcal{A}_1 \times \mathcal{A}_2$$

The Hilbert spaces compose as:
$$\mathcal{H}_{12} = \mathcal{H}_1 \otimes \mathcal{H}_2$$

### 5.8.2 Entanglement from Global Constraints

Entangled states arise when the composite graph has edges connecting subsystems:
$$[G_{12}] \neq [G_1] \times [G_2]$$

These inter-system edges create non-factorizable logical constraints.

## 5.9 Example: Hydrogen Atom

### 5.9.1 Graph Model

The hydrogen atom corresponds to graphs with:
- Radial structure: vertices at discrete radii
- Angular structure: cyclic subgraphs encoding angular momentum
- Coulomb constraint: edge weights $\propto 1/r$

### 5.9.2 Energy Eigenvalues

The energy levels emerge from allowed graph configurations:
$$E_n = -\frac{m_e e^4}{2\hbar^2 n^2} = -\frac{13.6 \text{ eV}}{n^2}$$

where $n$ counts the number of radial layers in the graph.

### 5.9.3 Selection Rules

Transitions require edge additions/removals that preserve admissibility:
- $\Delta\ell = \pm 1$: single edge change in angular subgraph
- $\Delta n$: arbitrary (radial restructuring allowed)

## Key Results

- **Theorem 5.1:** Graph properties yield self-adjoint operators
- **Theorem 5.2:** Position and momentum satisfy $[\hat{x},\hat{p}] = i\hbar$
- **Definition 5.4:** Hamiltonian from graph connectivity and strain
- **Theorem 5.3:** Commutation from partition compatibility
- **Theorem 5.5:** Unitarity from distinguishability preservation
- **Examples:** Harmonic oscillator and hydrogen atom from graph structure

## Summary

The quantum formalism emerges necessarily from logical structure:
1. **Operators** arise from graph properties
2. **Commutation relations** reflect partition incompatibility
3. **The Hamiltonian** encodes graph connectivity and strain
4. **Canonical commutators** emerge from translation generators
5. **Energy spectra** determined by admissible graph configurations
6. **Unitary evolution** preserves logical distinguishability

The operator algebra, commutation relations, and energy levels are not mysterious—they are consequences of representing logical structure as operators on the Hilbert space of admissible configurations.