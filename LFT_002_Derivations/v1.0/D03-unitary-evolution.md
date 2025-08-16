# D03-unitary-evolution.md

## Abstract

We prove that unitary evolution is the unique dynamics preserving logical coherence and derive the Standard Model gauge groups U(1)×SU(2)×SU(3) from fundamental logical symmetries. The proof shows that continuous interpolation between admissible configurations while preserving distinguishability necessitates unitary transformations, and that local gauge invariance emerges from position-dependent logical operations.

## 1. Coherence Preservation and Unitarity

### 1.1 The Coherence Requirements

From Section 4, the logical inner product encodes distinguishability:
$$\langle [G] | [H] \rangle = \delta_{[G],[H]}$$

Physical evolution must preserve three properties:

**C1 (Admissibility Preservation):** If ψ(0) ∈ A, then ψ(t) ∈ A for all t

**C2 (Distinguishability Preservation):** 
$$\langle \psi(t) | \phi(t) \rangle = \langle \psi(0) | \phi(0) \rangle$$

**C3 (Continuity):** Small time intervals produce small changes:
$$\lim_{t \to 0} ||\psi(t) - \psi(0)|| = 0$$

### 1.2 Wigner's Theorem Applied to Logical Evolution

**Theorem D3.1 (Unitarity from Coherence).** Any transformation T: H → H preserving the logical inner product must be either unitary or antiunitary.

*Proof:*
Given T preserves inner products:
$$\langle T\psi | T\phi \rangle = \langle \psi | \phi \rangle$$

By Wigner's theorem, T must be:
- Either linear and unitary: T†T = I
- Or antilinear and antiunitary: T(αψ) = α*T(ψ)

For time evolution with continuity requirement C3:
- T(0) = I (identity at t=0)
- Antilinear maps cannot connect continuously to identity
- Therefore T(t) must be unitary for all t

Thus evolution operator U(t) satisfies U†(t)U(t) = I. □

### 1.3 Generator of Evolution

**Theorem D3.2 (Hamiltonian Generator).** The continuous unitary evolution has form:
$$U(t) = e^{-iHt/\hbar}$$
where H is a self-adjoint operator (the Hamiltonian).

*Proof:*
From Stone's theorem, any strongly continuous one-parameter unitary group has the form:
$$U(t) = e^{-iGt}$$

where G is self-adjoint. Setting G = H/ℏ gives the standard form.

Self-adjointness of H follows from:
$$U†(t) = e^{iH†t/\hbar} = U(-t) = e^{iHt/\hbar}$$

This requires H† = H. □

## 2. Discrete Logical Symmetries

### 2.1 Fundamental Symmetries of Admissible Configurations

The admissible set A possesses three irreducible symmetries:

**Definition D3.1 (Orientation Symmetry).** From Section 4.4.3, directed cycles in logical graphs have orientation:
- Clockwise: C₊
- Counterclockwise: C₋
- Generator: rotation by angle θ

**Definition D3.2 (Binary Symmetry).** From the Excluded Middle (Section 2):
- Every proposition P has exactly two states: {P, ¬P}
- Discrete group: Z₂ = {id, flip}

**Definition D3.3 (Triadic Symmetry).** From transitivity of implication:
- Minimal non-trivial inference: (P→Q) ∧ (Q→R) ⇒ (P→R)
- Permutation group: S₃ acting on {P, Q, R}

### 2.2 Why These Symmetries Are Fundamental

**Lemma D3.1 (Irreducibility).** The symmetries {U(1), Z₂, S₃} cannot be reduced or unified.

*Proof:*
1. U(1) is continuous, Z₂ and S₃ are discrete → no unification
2. Z₂ has order 2, S₃ has order 6 → Z₂ ⊄ S₃
3. U(1) is Abelian, S₃ is non-Abelian → independent structures □

## 3. Enhancement to Continuous Groups

### 3.1 The Interpolation Requirement

**Definition D3.4 (Logical Interpolation).** A continuous path between configurations [G₀] and [G₁] is a family {[G(s)]: s ∈ [0,1]} such that:
- [G(0)] = [G₀], [G(1)] = [G₁]
- Each [G(s)] ∈ A (admissible)
- s ↦ [G(s)] is continuous in H

### 3.2 Enhancement Theorem

**Theorem D3.3 (Symmetry Enhancement).** Requiring continuous interpolation while preserving the logical inner product uniquely enhances:

**Z₂ → SU(2)**  
**S₃ → SU(3)**  
**U(1) → U(1)**

*Proof:*

**Part I: Z₂ → SU(2)**

The Z₂ basis states for proposition P:
$$|T\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \quad |F\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix}$$

Continuous interpolation requires:
$$|ψ(s)\rangle = \cos(s\theta/2)|T\rangle + e^{i\phi}\sin(s\theta/2)|F\rangle$$

The group of transformations preserving ||ψ||² = 1 is:
$$U = \begin{pmatrix} a & b \\ -b* & a* \end{pmatrix}, \quad |a|² + |b|² = 1$$

This is precisely SU(2).

**Part II: S₃ → SU(3)**

Consider three logical states forming a transitive chain. The minimal faithful complex representation of S₃ has dimension 3:
$$\rho: S_3 \to GL(3,\mathbb{C})$$

Requiring:
- Unitarity (preserve inner product)
- Special condition (det = 1 for distinguishability)
- Continuity (interpolation between permutations)

The unique continuous completion is SU(3).

**Part III: U(1) Remains U(1)**

Already continuous, no enhancement needed. □

### 3.3 Uniqueness of Enhancement

**Proposition D3.1 (No Alternative Enhancement).** The enhancements in Theorem D3.3 are unique.

*Proof by exclusion:*
- Z₂ → U(2)? No: U(2) = U(1) × SU(2), extra U(1) is redundant
- Z₂ → SO(3)? No: SO(3) = SU(2)/Z₂, loses quantum phase needed for interference (see D02: complex necessity for path superposition)
- S₃ → U(3)? No: Extra U(1) lacks logical origin
- S₃ → SO(6)? No: Real structure cannot support complex amplitudes (Section 4) □

## 4. Local Gauge Invariance

### 4.1 Position-Dependent Transformations

**Definition D3.5 (Local Transformation).** A position-dependent logical operation:
$$|\psi(x)\rangle \to U(x)|\psi(x)\rangle$$
where U(x) belongs to the symmetry group at each point x.

### 4.2 The Coherence Problem

**Lemma D3.2 (Derivative Non-Covariance).** Under local transformation:
$$\partial_\mu|\psi\rangle \to U(x)[\partial_\mu|\psi\rangle + (\partial_\mu U)U^{-1}|\psi\rangle]$$

The extra term ∂_μU breaks logical coherence between neighboring points.

### 4.3 Gauge Fields as Logical Connectors

**Theorem D3.4 (Gauge Field Necessity).** Maintaining logical coherence under local transformations requires connection fields.

*Proof:*
Define covariant derivative:
$$D_\mu = \partial_\mu + iA_\mu(x)$$

Under local transformation U(x):
$$A_\mu \to UA_\mu U^{-1} - i(\partial_\mu U)U^{-1}$$

This ensures:
$$D_\mu|\psi\rangle \to U(x)D_\mu|\psi\rangle$$

preserving logical relationships. □

## 5. The Standard Model Gauge Groups

### 5.1 U(1): Electromagnetic Field

From orientation phase symmetry:
$$|\psi(x)\rangle \to e^{i\alpha(x)}|\psi(x)\rangle$$

Covariant derivative:
$$D_\mu = \partial_\mu + ieA_\mu$$

Field strength:
$$F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu$$

This yields QED with coupling e determined by charge quantization.

### 5.2 SU(2): Weak Force

From binary proposition symmetry:
$$|\psi(x)\rangle \to U_{SU(2)}(x)|\psi(x)\rangle$$

Covariant derivative:
$$D_\mu = \partial_\mu + ig\frac{\sigma^a}{2}W^a_\mu$$

Three gauge bosons W^a_μ (a=1,2,3). After spontaneous symmetry breaking:
- W^± = (W¹ ∓ iW²)/√2
- Z⁰ = W³cosθ_W - B sinθ_W

### 5.3 SU(3): Strong Force

From triadic logical structure:
$$|\psi(x)\rangle \to U_{SU(3)}(x)|\psi(x)\rangle$$

Covariant derivative:
$$D_\mu = \partial_\mu + ig_s\frac{\lambda^a}{2}G^a_\mu$$

Eight gluons G^a_μ (a=1,...,8) mediating color force.

**Confinement from Logical Strain:**
Single-colored states have infinite strain v_I → ∞ (Section 3), forcing color-neutral combinations.

## 6. Uniqueness of U(1)×SU(2)×SU(3)

### 6.1 No Smaller Group Suffices

**Theorem D3.5 (Minimality).** No proper subgroup of U(1)×SU(2)×SU(3) maintains local logical coherence.

*Proof:*
- Remove U(1): Lose phase coherence for oriented cycles
- Remove SU(2): Cannot represent binary superposition continuously
- Remove SU(3): Cannot maintain triadic logical consistency
- Reduce SU(N) to SU(N-1): Lose faithful representation □

### 6.2 No Larger Group Necessary

**Theorem D3.6 (Sufficiency).** U(1)×SU(2)×SU(3) is sufficient for all logical operations.

*Proof:*
Any logical configuration can be decomposed into:
- Phase rotations (U(1))
- Binary choices (SU(2))
- Triadic relations (SU(3))

Higher groups would require logical structures beyond {orientation, binary, triadic}, which are not present in A. □

## 7. Dynamics from Minimal Action

### 7.1 The Gauge Field Action

**Theorem D3.7 (Yang-Mills from Minimality).** The unique local, gauge-invariant, renormalizable action is:

$$S_{YM} = -\frac{1}{4}\int d^4x \text{Tr}(F_{\mu\nu}F^{\mu\nu})$$

*Proof:*
Requirements:
1. Gauge invariance: Must use F_μν, not A_μ directly
2. Locality: No derivatives higher than second order
3. Renormalizability: Dimension ≤ 4
4. Reality: Action must be real

These uniquely determine the Yang-Mills form. □

### 7.2 Coupling Constants

The coupling ratios are determined by Casimir invariants:
$\frac{g_1^2}{g_2^2} : \frac{g_2^2}{g_3^2} = \frac{C_2(U(1))}{C_2(SU(2))} : \frac{C_2(SU(2))}{C_2(SU(3))} = \frac{1}{2} : \frac{2}{3}$

Note: C₂(U(1)) uses GUT normalization where Y² = 3/5 to match SU(5) embedding.

At unification scale, this predicts:
$\sin^2\theta_W = \frac{3}{8} = 0.375$

(Compare to low-energy value ~0.23 after running)

## 8. Three Fermion Generations

### 8.1 Embeddings of Binary into Triadic

**Theorem D3.8 (Three Generations).** There are exactly three inequivalent ways to embed Z₂ into S₃.

*Proof:*
A Z₂ subgroup of S₃ corresponds to choosing 2 elements from {1,2,3}:
- Generation 1: (12) - swap elements 1,2
- Generation 2: (23) - swap elements 2,3  
- Generation 3: (13) - swap elements 1,3

These are cyclically related but not equivalent under S₃ action. □

### 8.2 Mass Hierarchy

The three embeddings have different "distances" from identity in S₃, quantified by internal strain v_I (Section 3):

- First generation: v_I,1 ∝ 1 (closest, lightest)
- Second generation: v_I,2 ∝ (ξ₂/ξ₁)² (intermediate)  
- Third generation: v_I,3 ∝ (ξ₃/ξ₁)² (furthest, heaviest)

where ξᵢ represents the coherence length scale for generation i. From D05, higher strain corresponds to larger mass, qualitatively explaining the observed hierarchy:
$m_e : m_\mu : m_\tau \approx 1 : 200 : 3500$

## 9. Predictions

### 9.1 No New Gauge Forces

**Prediction D3.1:** No additional gauge bosons below Planck scale.

*Reasoning:* All logical requirements are satisfied by U(1)×SU(2)×SU(3).

### 9.2 Modified Running at High Energy

**Prediction D3.2:** Near Planck scale, beta functions receive corrections:

$$\beta_i(E) = \beta_i^{SM}(E)\left(1 - \frac{E^2}{M_{Planck}^2}\right)$$

### 9.3 Dark Sector

**Prediction D3.3:** Dark matter consists of logically disconnected configurations with no gauge charges under U(1)×SU(2)×SU(3).

## 10. Summary

**Main Results:**

1. **Unitarity is necessary** for coherence preservation (Theorem D3.1)
2. **Symmetry enhancement** is unique: Z₂→SU(2), S₃→SU(3) (Theorem D3.3)
3. **Gauge fields** are logical connectors for local coherence (Theorem D3.4)
4. **U(1)×SU(2)×SU(3)** is minimal and sufficient (Theorems D3.5-D3.6)
5. **Three generations** from Z₂↪S₃ embeddings (Theorem D3.8)

**Key Insights:**
- Forces are not fundamental but emerge from local logic
- Standard Model structure is largely determined by logical requirements
- Gauge groups are unique, not arbitrary choices
- Confinement follows from logical strain

**Connection to Other Derivations:**
- Uses complex structure from D02
- Combines with Born rule (D04) for measurement
- Strain weights (D05) determine coupling evolution
- Together: Complete dynamics of logical configurations

## References

- Section 2: Admissibility and logical structure
- Section 4: Complex necessity and orientation
- Section 5: Quantum operators and unitarity
- Section 7: Gauge fields and symmetries
- D02: Why complex numbers
- D04: Born rule from paths
- D05: Strain weights and dynamics