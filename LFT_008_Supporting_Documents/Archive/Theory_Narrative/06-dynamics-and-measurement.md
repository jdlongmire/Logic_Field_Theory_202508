# 6. Dynamics and Measurement

This section derives quantum dynamics from logical principles and explains measurement as a strain-threshold phenomenon. The Born rule emerges from logical constraints rather than being postulated.

## 6.1 Dynamics from Action Minimization

### 6.1.1 The Logical Action

For a trajectory through configuration space $\psi(t) \in \mathcal{A}$, define the logical action:

$$S[\psi] = \int_0^T \left[ \langle\psi|\frac{\partial}{\partial t}|\psi\rangle - D(\psi(t)) \right] dt$$

where:
- First term: kinetic-like contribution from configuration change  
- $D(\psi)$: logical strain functional from Section 3

### 6.1.2 Euler-Lagrange Equations

Minimizing $S[\psi]$ subject to normalization yields:

$$i\hbar\frac{\partial}{\partial t}|\psi\rangle = \hat{H}|\psi\rangle$$

where the Hamiltonian emerges as:

$$\hat{H} = \hat{H}_0 + \hat{V}_{strain}$$

- $\hat{H}_0$: kinetic term from logical graph connectivity
- $\hat{V}_{strain}$: potential from strain landscape

**Key point:** The Schrödinger equation is not postulated—it's the equation of motion for minimum logical action trajectories.

## 6.2 The Born Rule Without Postulates

### 6.2.1 Probability from Logical Consistency

Consider measuring observable $\hat{Q}$ with eigenspaces $\{P_k\}$ on state $|\psi\rangle$.

The probability $p_k$ of outcome $k$ must satisfy:

**L1 (Normalization):** $\sum_k p_k = 1$

**L2 (Logical Additivity):** For orthogonal decompositions,
$$p(A \lor B) = p(A) + p(B) \text{ when } A \land B = \emptyset$$

**L3 (Coherence Invariance):** Probabilities depend only on logical content:
$$p_k = f(|\langle P_k|\psi\rangle|)$$

**L4 (Composition):** For independent systems,
$$p_{ij} = p_i \cdot p_j$$

### 6.2.2 The Unique Solution

**Theorem 6.1 (Born Rule Uniqueness).** The only function satisfying L1-L4 is:

$$p_k = |\langle P_k|\psi\rangle|^2 = |c_k|^2$$

*Proof sketch:*
- L3 implies $p_k = f(|c_k|)$ for some function $f$
- L2 forces $f$ to be homogeneous of degree $n$
- L4 requires $f(xy) = f(x)f(y)$, giving $f(x) = x^n$
- L1 with orthogonal states forces $n = 2$

Therefore: **The Born rule is the unique probability measure consistent with logical requirements.**

## 6.3 Measurement as Strain Resolution

### 6.3.1 The Coherence Capacity

**Definition 6.1 (Coherence Capacity).** The coherence capacity $\sigma_{critical}$ of a physical system is determined by its logical complexity:

$$\sigma_{critical} = N_{dof} \cdot \sigma_0$$

where:
- $N_{dof}$ = number of logical degrees of freedom (graph vertices)
- $\sigma_0$ = fundamental strain quantum (Planck-scale constant)

**Physical Interpretation:** Larger systems with more logical structure can sustain higher strain before requiring resolution. For a macroscopic apparatus with $N_{dof} \sim 10^{23}$, the coherence capacity is enormous, ensuring classical behavior.

### 6.3.2 Outcome Selection Mechanism

**Definition 6.2 (Strain Landscape).** For state $|\psi\rangle = \sum_k c_k |k\rangle$, the strain landscape is:

$$D(k|\psi) = D(|k\rangle) + w_N \ln\left(\frac{1}{|c_k|^2}\right)$$

This defines the "effort" required to resolve to outcome $k$.

**Outcome Selection Principle:** When $D_{total} > \sigma_{critical}$, the system evolves along the path of steepest strain descent:

$$\frac{d|\psi\rangle}{d\tau} = -\nabla D(\psi)$$

where $\tau$ is the resolution timescale. The outcome $k$ is selected where this gradient flow stabilizes, with probability determined by the basin of attraction volume, which yields $P(k) = |c_k|^2$.

### 6.3.3 What Makes a Measuring Apparatus

**Definition 6.3 (Measuring Apparatus).** A system $M$ constitutes a measuring apparatus for observable $\hat{Q}$ if:

1. **Pointer basis alignment:** $M$ has stable states $\{|m_k\rangle\}$ corresponding to eigenvalues of $\hat{Q}$
2. **Amplification:** $N_{dof}^{(M)} \gg N_{dof}^{(S)}$ (many more degrees of freedom than system)
3. **Irreversibility:** Environmental coupling ensures $D_{back} \gg \sigma_{critical}$ for reverse transitions

**Key insight:** A measuring apparatus is distinguished by having sufficient logical complexity to create an irreversible strain cascade when entangled with the measured system.

### 6.3.4 The Measurement Process

**Stage 1: Pre-measurement**  
System in superposition: $|\psi\rangle_S = \sum_k c_k |k\rangle_S$  
Apparatus in ready state: $|ready\rangle_M$  
Total strain: $D_{total} < \sigma_{critical}$

**Stage 2: Entanglement**  
Interaction creates: $|\Psi\rangle_{SM} = \sum_k c_k |k\rangle_S \otimes |m_k\rangle_M$  
Strain accumulates: $D_{total} = D_S + D_M + D_{SM}$

**Stage 3: Threshold Crossing**  
When $D_{total} > \sigma_{critical}^{(SM)}$:
- Gradient flow initiates: $d|\Psi\rangle/d\tau = -\nabla D$
- System follows steepest descent path
- Flow stabilizes at local minimum $|k_*\rangle_S \otimes |m_{k_*}\rangle_M$

**Stage 4: Outcome Stabilization**  
Final state: $|k_*\rangle_S \otimes |m_{k_*}\rangle_M$  
Strain reduced: $D_{final} < \sigma_{critical}$  
Reverse transition blocked: $D_{reverse} \gg \sigma_{critical}$

### 6.3.5 Resolution of the "Null Outcome"

From Section 1, configurations must satisfy:
$$\exp(-\beta D(\psi)) \geq \varepsilon$$

**Definition 6.4 (Realizability Threshold).** The threshold $\varepsilon$ represents the minimum logical coherence for physical manifestation:

$$\varepsilon = \exp\left(-\beta \sigma_{critical}\right)$$

**Null Outcome:** When $D(\psi) > \sigma_{critical}$, we have $\exp(-\beta D) < \varepsilon$. The configuration cannot maintain logical coherence and experiences:
- **Immediate decoherence** for slight excess ($D \gtrsim \sigma_{critical}$)
- **Logical dissolution** for severe excess ($D \gg \sigma_{critical}$)

The "null outcome" is not mysterious—it's the logical dissolution of configurations that exceed coherence capacity before establishing stable measurement correlations.

## 6.4 Why Measurement Appears Random

### 6.4.1 Deterministic but Unpredictable

The measurement outcome is determined by:
1. Initial strain landscape $D(k|\psi)$
2. Microscopic details of system-apparatus coupling
3. Environmental perturbations during threshold crossing

While deterministic in principle, the outcome is **computationally irreducible**—predicting it requires simulating the full logical evolution, which is practically impossible for macroscopic systems.

### 6.4.2 Emergence of Born Probabilities

The Born rule $P(k) = |c_k|^2$ emerges because:
- Basin volumes in strain landscape $\propto |c_k|^2$
- Gradient flow from random initial perturbations samples basins uniformly
- Ergodic averaging over many similar measurements yields Born statistics

The randomness is **epistemic**, arising from our inability to track $\sim 10^{23}$ logical degrees of freedom, not from fundamental indeterminacy.

## 6.5 Decoherence and the Classical Limit

### 6.5.1 Environmental Coupling

Interaction with environment adds external strain:
$$v_E = \sum_{k \in environment} J_k |\langle k|\psi\rangle|^2$$

This drives decoherence on timescale:
$$\tau_D = \frac{\hbar}{\langle v_E \rangle} \cdot \frac{\sigma_{critical}}{D_{total}}$$

Note the correction factor $\sigma_{critical}/D_{total}$ that accelerates decoherence near the threshold.

### 6.5.2 Emergence of Classical Behavior

Classical behavior emerges when:
1. **High complexity:** $N_{dof} \gg 1$ (macroscopic object)
2. **Environmental saturation:** $v_E \approx \sigma_{critical}/N_{dof}$
3. **Instant decoherence:** $\tau_D \to 0$

The classical world is the high-complexity, environmentally-coupled limit where superpositions instantly exceed coherence capacity.

## 6.6 Quantum Zeno Effect

Frequent measurements keep strain below threshold:
- Each measurement resets $D \to D_{post} < \sigma_{critical}$
- Insufficient time to accumulate strain: $\Delta t < \tau_{accumulation}$
- Evolution effectively frozen in eigenstate

**Zeno threshold:** Measurements must occur faster than:
$$\tau_{Zeno} = \frac{\sigma_{critical}}{|\langle\hat{H}\rangle|}$$

## 6.7 EPR and Non-locality

### 6.7.1 Entangled States

For entangled state $|\psi\rangle_{AB} = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$:

- Single global constraint: $D_{global} < D_A + D_B$ (subadditive)
- Measurement at A shifts global landscape
- B's outcome determined by new landscape minimum

### 6.7.2 No Spooky Action

The correlation mechanism:
1. Global strain landscape established at entanglement
2. Measurement at A selects consistent branch
3. B's measurement finds complementary minimum
4. No signal transmission—just shared logical structure

## 6.8 Predictions Beyond Standard QM

### 6.8.1 Strain-Modified Transition Rates

Transition probability with strain correction:
$$P_{i \to f} = P_{QM} \cdot \exp\left(-\beta \frac{\Delta D_{if}}{\sigma_{critical}}\right)$$

### 6.8.2 Measurement Back-action

Post-measurement strain increase:
$$\Delta D = w_N \ln\left(\frac{1}{|c_k|^2}\right)$$

Predicts: Highly unlikely outcomes ($|c_k|^2 \ll 1$) create more back-action strain.

### 6.8.3 Coherence Recovery Time

After measurement, coherence rebuilds as:
$$D(t) = D_{post} \cdot \exp\left(-\frac{t}{\tau_{recovery}}\right)$$

where $\tau_{recovery} = \hbar/E_{gap}$ depends on energy scales.

### 6.8.4 Critical Experiments

**Experiment 1: Coherence Capacity Scaling**
- Vary system size $N_{dof}$
- Measure decoherence time $\tau_D$
- Prediction: $\tau_D \propto N_{dof}$ (linear scaling)

**Experiment 2: Strain Accumulation**
- Prepare near-threshold state: $D \approx \sigma_{critical}$
- Apply weak perturbation
- Prediction: Sharp transition to classical behavior

**Experiment 3: Null Outcome Detection**
- Engineer high-strain state: $D \gg \sigma_{critical}$
- Attempt measurement
- Prediction: No stable outcome, rapid dissolution

## Key Results

- **Definition 6.1:** Coherence capacity scales with logical complexity
- **Definition 6.2:** Strain landscape governs outcome selection
- **Definition 6.3:** Measuring apparatus requires amplification + irreversibility
- **Definition 6.4:** Null outcomes occur when strain exceeds capacity
- **Theorem 6.1:** Born rule uniquely satisfies logical requirements

## Summary

This section established:
1. **Dynamics** emerge from logical action minimization
2. **Born rule** is the unique measure satisfying logical constraints
3. **Measurement** occurs via strain-driven gradient flow to stable minima
4. **Outcome selection** is deterministic but computationally irreducible
5. **Measuring apparatus** distinguished by complexity and irreversibility
6. **Null outcomes** represent logical dissolution above threshold
7. **Classical limit** emerges from high complexity + environmental coupling

All quantum phenomena—measurement, decoherence, entanglement—arise from logical structure and strain dynamics, not from additional postulates. The measurement problem is resolved: outcomes are selected by gradient flow in the strain landscape, with probabilities emerging from basin volumes.