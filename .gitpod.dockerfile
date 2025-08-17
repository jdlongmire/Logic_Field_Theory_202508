# .gitpod.dockerfile
FROM gitpod/workspace-base

# Install Lean 4
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.12.0
ENV PATH="/home/gitpod/.elan/bin:${PATH}"

# Pre-build mathlib cache
WORKDIR /workspace
RUN git clone https://github.com/leanprover-community/mathlib4.git /tmp/mathlib4 && \
    cd /tmp/mathlib4 && \
    lake exe cache get && \
    rm -rf /tmp/mathlib4

USER gitpod