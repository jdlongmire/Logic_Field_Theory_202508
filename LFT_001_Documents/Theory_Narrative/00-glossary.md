## Glossary

**3FLL (Three Fundamental Laws of Logic)**  
Identity: $A = A$.  
Non-Contradiction: $\neg(A \land \neg A)$.  
Excluded Middle: $A \lor \neg A$.

**$\mathcal{S}$**  
Formally describable information field (syntactic space) containing all definable information patterns.

**$\mathbb{L}$**  
Logic-enforcement operator applying the 3FLL to $\mathcal{S}$, producing only logically coherent configurations.

**$\mathcal{A} = \mathbb{L}(\mathcal{S})$**  
The admissible set: all logically permissible configurations after applying $\mathbb{L}$ to $\mathcal{S}$.  
(Formerly denoted $\Omega$ in earlier drafts; symbol changed to avoid probability-space collisions.)

**Logical Strain $D(\psi)$**  
Functional quantifying realization cost for an admissible configuration $\psi$:
$$
D(\psi) = w_I v_I + w_N v_N + w_E v_E
$$

- **$v_I$** – Internal contradiction strain (proximity of contradictory paths).  
- **$v_N$** – Non-classicality (entropic) strain.  
- **$v_E$** – External misfit strain.

**Principle of Least Logical Strain**  
Hypothesized dynamical principle: realized physical evolution minimizes $D(\psi)$ over admissible trajectories.

