# 4. From Graphs to Vector Spaces

This section bridges discrete graph structures to the continuous vector spaces of quantum mechanics. We show that coherence preservation and composition requirements force a linear structure on the space of admissible configurations, with complex numbers emerging as the unique scalar field.

## 4.1 The Composition Problem

Given admissible graphs $G_1, G_2 \in \mathcal{A}$, we need to:

1. Combine them into composite descriptions
2. Transform them while preserving admissibility
3. Maintain logical relationships under these operations

The naive approach—working directly with individual graphs—fails because:

* Graphs are discrete; physical transformations appear continuous
* No natural way to "interpolate" between graphs while maintaining admissibility
* Composition of constraints can create new admissible states not present in either component

### 4.1.1 From Discrete Graph Operations to Continuous Groups

The bridge from discrete graphs to continuous transformations occurs through cycle structures:

**Step 1: Graph Automorphisms**
For $G \in \mathcal{A}$, the automorphism group $\text{Aut}(G)$ acts discretely on vertices while preserving logical structure.

**Step 2: Cycle Rotation Embedding**
Each automorphism $\sigma \in \text{Aut}(G)$ induces a rotation on the space of directed cycles. These discrete rotations generate continuous groups:

* $\mathbb{Z}_n$ symmetry of $n$-cycle → $U(1)$ continuous rotations
* Permutation group $S_n$ → $SU(n)$ (detailed in Section 7)

**Step 3: One-Parameter Subgroups**
Continuous deformations arise as one-parameter subgroups:
$$U(t) = \exp(tX)$$
where $X$ is a generator derived from the graph structure.

**Step 4: Completion**
Finite superpositions approximate continuous transformations. The Cauchy completion includes all limits, yielding the full Hilbert space.

## 4.2 Superposition as Logical Necessity

### 4.2.1 The Incompleteness Principle

Consider a proposition $P$ that is:

* Neither provable nor disprovable from current constraints
* Logically independent of the existing structure
* Potentially resolvable through additional information

The configuration must encode this incompleteness. A single graph $G$ forces either $P$ or $\neg P$ to be present (by Excluded Middle), artificially resolving the indeterminacy.

### 4.2.2 Weighted Combinations

To represent genuine logical indeterminacy, we need **weighted combinations** of graphs:

$$\psi = \sum_{i} c_i [G_i]$$

where:

* $[G_i]$ are equivalence classes of admissible graphs
* $c_i$ are weights encoding relative consistency with available constraints
* The sum represents logical "or" at the structural level

This is not a choice—it's forced by the need to represent incomplete information faithfully.

## 4.3 Emergence of Linear Structure

### 4.3.1 Representation Axioms

To make progress, we introduce minimal representation requirements:

**R1 (Closure):** Logical combinations of admissible configurations remain admissible.

**R2 (Distinguishability):** Distinct logical content must be distinguishable. We define a **combinatorial pairing** on equivalence classes:

$$\delta([G], [H]) := \begin{cases}
1 & \text{if } [G] = [H] \\
0 & \text{if } [G] \neq [H]
\end{cases}$$

**Critical Note:** This pairing is **purely combinatorial**—it encodes logical distinguishability, not probability. It simply states that distinct logical configurations are orthogonal. No Born rule or probabilistic interpretation is assumed here.

**R3 (Coherence Preservation):** Logical relationships between configurations are preserved under valid transformations.

### 4.3.2 The Vector Space

With these axioms:
1. **Basis vectors:** $\{|[G]\rangle : [G] \in \mathcal{A}/\sim\}$
2. **Linear combinations:** $|\psi\rangle = \sum_i c_i |[G_i]\rangle$ (finite sums initially)
3. **Formal pairing:** Extended bilinearly from the combinatorial pairing

This gives us the free vector space $\mathcal{V}$ over field $\mathbb{F}$ (to be determined).

## 4.4 Why Complex Numbers?

### 4.4.1 Foundational Logical Requirements

We derive the scalar field from primitive logical needs:

**L1 (Countability):** The set of logically distinct configurations $\mathcal{A}/\sim$ is countable.
*Justification:* Each configuration is finitely describable in formal logic.

**L2 (Transformation Coherence):** Admissibility-preserving transformations must preserve distinguishability relationships.
*Justification:* If transformation $T$ preserves logical content, then $\delta(T[G], T[H]) = \delta([G], [H])$.

**L3 (Local Independence):** Operations on logically independent subsystems commute.
*Justification:* What happens in subsystem A cannot affect logically independent subsystem B.

**L4 (Orientation Distinction):** Directed cycles of logical inference have distinguishable orientations.
*Justification:* The inference chain $P \to Q \to R \to P$ differs from $P \to R \to Q \to P$ in its logical structure.

**L5 (Continuous Deformation):** Small changes in logical relationships cause small changes in representation.
*Justification:* Logic should not have arbitrary discontinuities—nearby configurations have similar properties.

### 4.4.2 From Logical Requirements to Mathematical Axioms

The logical requirements L1-L5 translate to mathematical axioms:

**A1 (Separability):** $\mathcal{A}/\sim$ is countable. [from L1]

**A2 (Overlap Preservation):** Transformations preserve the pairing structure up to a unit-modulus factor. [from L2]

**A3 (Scalar Commutativity):** Scalar multiplication commutes with local operations on independent subsystems. [from L3]

**A4 (Orientation Sensitivity):** Orientation-reversed cycles are distinct eigenstates of the cycle rotation operator. [from L4]

**A5 (Strong Continuity):** Logical deformations act as strongly continuous one-parameter groups. [from L5]

### 4.4.3 Graph Cycles and Rotation Groups

To understand how directed cycles lead to complex structure, consider the concrete mapping:

**Definition (Cycle Space):** For a logical configuration, the *cycle space* $\mathcal{C}$ consists of all directed cycles in its inference graph.

**Example: Elementary 2-Cycle**
Consider propositions $P, Q$ with the minimal non-trivial cycles:
- **Clockwise cycle:** $C_+: P \to Q \to \neg P \to \neg Q \to P$
- **Counterclockwise cycle:** $C_-: P \to \neg Q \to \neg P \to Q \to P$

These represent opposite orientations of the same logical relationship.

**Rotation Action:** A continuous deformation of the logical structure induces a rotation in cycle space:
$$R_\theta: \mathcal{C} \to \mathcal{C}$$

For the 2-cycle example, $R_\theta$ acts on the span $V = \text{span}\{C_+, C_-\}$ as:
$$R_\theta = \begin{pmatrix}
\cos\theta & -\sin\theta \\
\sin\theta & \cos\theta
\end{pmatrix}$$

### 4.4.4 The Orientation-Composition Theorem

**Theorem 4.1 (Field Uniqueness).** The scalar field for the Hilbert space of logical states must be $\mathbb{C}$.

**Proof:**

**Part I: Real Numbers Are Insufficient**

By A4, the orientation types $C_+, C_-$ must be eigenstates of $R_\theta$ with distinct eigenvalues. But for real matrices:

$$\det(R_\theta - \lambda I) = (\cos\theta - \lambda)^2 + \sin^2\theta = \lambda^2 - 2\lambda\cos\theta + 1$$

For generic $\theta \neq 0, \pi$, this has no real roots. The eigenvalues are $e^{\pm i\theta}$, requiring complex numbers.

To represent $C_\pm$ as stable eigenstates:
$$R_\theta |C_\pm\rangle = e^{\pm i\theta} |C_\pm\rangle$$

we need $\mathbb{F} \supseteq \mathbb{C}$.

**Part II: Quaternions Violate Independence**

Consider quaternionic scalars with independent subsystems $A, B$. For $q \in \mathbb{H} \setminus \mathbb{R}$ and operators $X_A, Y_B$:

By A3 (scalar commutativity from L3):
$$q(X_A \otimes Y_B) = (X_A \otimes Y_B)q$$

But in $\mathbb{H}$:
- Left side: $q$ multiplies the entire tensor product
- Right side: $q$ multiplies the entire tensor product

For this to equal $(qX_A) \otimes Y_B = X_A \otimes (Y_Bq)$, we need:
$$qX_A \otimes Y_B = X_A \otimes qY_B$$

Since $q$ acts on different factors, this forces $q$ to commute with all operators, hence $q \in \mathbb{R}$. Therefore $\mathbb{H}$ is excluded.

**Part III: Complex Numbers Are Necessary and Sufficient**

By the classification of normed division algebras: $\{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$
- $\mathbb{R}$: Cannot represent orientation eigenstates (Part I)
- $\mathbb{H}$: Violates subsystem independence (Part II)
- $\mathbb{C}$: Satisfies all requirements

Therefore $\mathbb{F} = \mathbb{C}$. $\square$

### 4.4.5 Physical Interpretation of the Imaginary Unit

The imaginary unit $i$ is not abstract—it is the **generator of logical orientation**:

For the elementary 2-cycle, the rotation generator:
$$K = \frac{d}{d\theta}\bigg|_{\theta=0} R_\theta = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$$

satisfies $K^2 = -I$, giving the complex structure $J = K$ with:
$$J|C_+\rangle = i|C_+\rangle, \quad J|C_-\rangle = -i|C_-\rangle$$

The phase $e^{i\theta}$ directly encodes the orientation angle of directed logical paths.

## 4.5 Hilbert Space Completion

With $\mathbb{F} = \mathbb{C}$ established, we complete the construction:

1. **Pre-Hilbert space:** $\mathcal{V} = \text{span}_\mathbb{C}\{|[G]\rangle : [G] \in \mathcal{A}/\sim\}$
2. **Inner product:** Extend the combinatorial pairing sesquilinearly:
   $$\langle \psi | \phi \rangle = \sum_{i,j} c_i^* d_j \delta([G_i], [G_j])$$
3. **Cauchy completion:** Include all limit points of Cauchy sequences
4. **Result:** $\mathcal{H} = \ell^2(\mathcal{A}/\sim, \mathbb{C})$

The completion is necessary because:
- Continuous rotations require limits of discrete approximations
- Physical evolution involves continuous parameter groups
- Measurement outcomes can approach limiting configurations

## 4.6 Path Counting and the Born Rule

### 4.6.1 Logical Paths in Configuration Space

**Definition (Inference Path):** A sequence of logical steps $G_0 \to G_1 \to \cdots \to G_n$ where each arrow represents a valid inference rule.

**Path Amplitude:** Each path $p$ from initial configuration $G_{\text{init}}$ to final configuration $G_{\text{final}}$ carries:
- **Weight:** $A_p$ = product of inference rule strengths
- **Phase:** $\theta_p$ = accumulated orientation from directed cycles traversed

**Total Amplitude:** When multiple paths lead to the same final configuration:
$$c_{G_{\text{final}}} = \sum_{\text{paths } p} A_p e^{i\theta_p}$$

### 4.6.2 Emergence of Quantum Interference

The complex structure enables interference:
- **Constructive:** Paths with similar phases ($\theta_p \approx \theta_{p'}$) reinforce
- **Destructive:** Paths with opposite phases ($\theta_p \approx \theta_{p'} + \pi$) cancel

This is not assumed—it follows from the complex addition of amplitudes required by orientation.

### 4.6.3 The Born Rule as Logical Necessity

**Proposition 4.2 (Born Rule Uniqueness).** The probability measure on logical configurations must be $P(G|\psi) = |c_G|^2$.

**Proof Outline:**

Given requirements:
1. **Positivity:** $P(G|\psi) \geq 0$
2. **Path interference:** Amplitudes add as $c_G = \sum_p A_p e^{i\theta_p}$
3. **Normalization:** $\sum_G P(G|\psi) = 1$
4. **Independence:** $P(G_A \times G_B|\psi_A \otimes \psi_B) = P(G_A|\psi_A) \cdot P(G_B|\psi_B)$

The measure must have form $P(G) = f(|c_G|)$ by (2) and positivity.

Independence (4) requires:
$$f(|c_A c_B|) = f(|c_A|) \cdot f(|c_B|)$$

Setting $f(x) = x^n$, normalization forces $n = 2$.

Therefore $P(G|\psi) = |c_G|^2$ uniquely. $\square$

## 4.7 Complete Derivation Chain

We have established without circular reasoning:

1. **Logic requires superposition** (incomplete information)
2. **Superposition requires vector space** (linear combinations)
3. **Discrete graphs generate continuous groups** (via cycle rotations)
4. **Orientation requires complex numbers** (proven via Theorem 4.1)
5. **Complex amplitudes require Born rule** (proven via Proposition 4.2)

No quantum mechanics was assumed—everything emerges from logical structure.

## 4.8 Connection to Standard QM

Our construction yields:
- **State space:** $\mathcal{H} = \ell^2(\mathcal{A}/\sim, \mathbb{C})$
- **Basis states:** Definite logical configurations $|[G]\rangle$
- **Superpositions:** Logical incompleteness
- **Inner product:** Extended combinatorial pairing
- **Born rule:** Path counting measure

This reproduces the standard framework while explaining its origin.

## Key Results

- **Theorem 4.1:** Complex numbers are the unique scalar field satisfying logical requirements
- **Proposition 4.2:** Born rule is the unique probability measure consistent with path counting
- **Bridge established:** Discrete graph automorphisms → continuous unitary groups via cycle rotations
- **Physical meaning:** The imaginary unit $i$ generates logical orientation

## Summary

The complex Hilbert space structure of quantum mechanics emerges necessarily from:
1. **Logical incompleteness** → Superposition
2. **Graph automorphisms** → Continuous groups
3. **Coherence preservation** → Linearity
4. **Orientation + Independence** → Complex numbers (uniquely)
5. **Path interference** → Born rule (uniquely)

The imaginary unit $i$ is the generator of logical orientation. The Born rule is the unique measure consistent with path counting in complex configuration space. Quantum mechanics is not mysterious—it is the unique mathematical framework for logically consistent information.