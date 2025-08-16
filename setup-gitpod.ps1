# setup-gitpod.ps1
# PowerShell script to set up Gitpod integration for LFT

Write-Host "🚀 Setting up Gitpod integration for Logic Field Theory" -ForegroundColor Cyan
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Gray

# Create .gitpod.yml
Write-Host "📄 Creating .gitpod.yml..." -ForegroundColor Yellow
@'
# .gitpod.yml
# Gitpod configuration for Logic Field Theory Lean proofs

image:
  file: .gitpod.dockerfile

# Commands to run on workspace start
tasks:
  - name: 🔨 Build LFT Proofs
    init: |
      echo "📚 Setting up Logic Field Theory environment..."
      lake build
      echo "✅ Build complete!"
    command: |
      clear
      echo "╔════════════════════════════════════════════════════════╗"
      echo "║       LOGIC FIELD THEORY - LEAN 4 ENVIRONMENT         ║"
      echo "╠════════════════════════════════════════════════════════╣"
      echo "║  Deriving QM from the Three Fundamental Laws of Logic ║"
      echo "╚════════════════════════════════════════════════════════╝"
      echo ""
      echo "📊 Quick Commands:"
      echo "  lake build         - Build all proofs"
      echo "  lake test          - Run verification suite"
      echo "  ./scripts/verify   - Verify specific derivation"
      echo ""
      echo "📁 Key Files:"
      echo "  003-Lean_Supporting_Data/Core_Backup/D01_Admissibility.lean"
      echo "  003-Lean_Supporting_Data/Core_Backup/D02_ComplexNecessity.lean"
      echo "  003-Lean_Supporting_Data/Core_Backup/D03_UnitaryEvolution.lean"
      echo "  003-Lean_Supporting_Data/Core_Backup/D04_BornRule.lean"
      echo "  003-Lean_Supporting_Data/Core_Backup/D05_StrainWeights.lean"
      echo ""
      echo "🔬 Critical Test: τ_D ∝ ξ² (LFT) vs τ_D ∝ ξ⁻¹ (QM)"
      echo ""
      
  - name: 📝 Theory Documentation
    command: |
      echo "Opening theory narrative..."
      code 001-Papers/Theory_Narrative/01-introduction.md
      
  - name: 🧪 Experimental Predictions
    command: |
      echo "Key predictions for experimental validation:"
      cat 002-Derivations/D06-predictions.md | head -50

# VS Code extensions
vscode:
  extensions:
    - leanprover.lean4
    - ms-python.python
    - yzhang.markdown-all-in-one
    - james-yu.latex-workshop
    - streetsidesoftware.code-spell-checker

# Port configuration
ports:
  - port: 8080
    onOpen: ignore
    visibility: public
    description: "Lean documentation server"
  - port: 3000
    onOpen: ignore
    visibility: public
    description: "Interactive proof explorer"

# GitHub integration
github:
  prebuilds:
    master: true
    branches: true
    pullRequests: true
    pullRequestsFromForks: false
    addComment: true
    addBadge: true
    addLabel: prebuilt-in-gitpod
'@ | Out-File -FilePath ".gitpod.yml" -Encoding UTF8

Write-Host "✅ .gitpod.yml created" -ForegroundColor Green

# Create .gitpod.dockerfile
Write-Host "📄 Creating .gitpod.dockerfile..." -ForegroundColor Yellow
@'
# .gitpod.dockerfile
# Lean 4 environment for Logic Field Theory

FROM gitpod/workspace-full:latest

# Install Lean 4 dependencies
USER gitpod

# Install elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# Add elan to PATH
ENV PATH="/home/gitpod/.elan/bin:${PATH}"

# Pre-install the Lean version specified in lean-toolchain
COPY --chown=gitpod:gitpod lean-toolchain /tmp/lean-toolchain
RUN cd /tmp && elan toolchain install $(cat lean-toolchain) && rm lean-toolchain

# Install additional tools for visualization and analysis
RUN pip install --user matplotlib numpy scipy jupyter pandas

# Install Node packages for potential web interface
RUN npm install -g http-server

# Create helpful scripts directory
RUN mkdir -p /home/gitpod/scripts

# Add a welcome message
RUN echo 'echo "🚀 Logic Field Theory - Lean 4 Environment Ready!"' >> /home/gitpod/.bashrc
RUN echo 'echo "📖 Documentation: https://doi.org/10.5281/zenodo.16884443"' >> /home/gitpod/.bashrc

# Set up Git configuration for better collaboration
RUN git config --global pull.rebase false

USER root
'@ | Out-File -FilePath ".gitpod.dockerfile" -Encoding UTF8

Write-Host "✅ .gitpod.dockerfile created" -ForegroundColor Green

# Create scripts directory if it doesn't exist
if (!(Test-Path -Path "scripts")) {
    New-Item -ItemType Directory -Path "scripts" -Force | Out-Null
    Write-Host "📁 Created scripts directory" -ForegroundColor Green
}

# Create verify.sh script
Write-Host "📄 Creating scripts/verify.sh..." -ForegroundColor Yellow
@'
#!/bin/bash
# scripts/verify.sh
# Interactive verification script for LFT derivations

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# ASCII art header
print_header() {
    echo -e "${GREEN}"
    echo "╔══════════════════════════════════════════╗"
    echo "║     LFT PROOF VERIFICATION SYSTEM       ║"
    echo "╚══════════════════════════════════════════╝"
    echo -e "${NC}"
}

# Function to verify a specific derivation
verify_derivation() {
    local derivation=$1
    local file=""
    
    case $derivation in
        D01|d01)
            file="003-Lean_Supporting_Data/Core_Backup/D01_Admissibility.lean"
            echo -e "${BLUE}Verifying D01: Admissibility (𝒜 = ℒ(𝒮))...${NC}"
            ;;
        D02|d02)
            file="003-Lean_Supporting_Data/Core_Backup/D02_ComplexNecessity.lean"
            echo -e "${BLUE}Verifying D02: Complex Necessity (ℂ is unique)...${NC}"
            ;;
        D03|d03)
            file="003-Lean_Supporting_Data/Core_Backup/D03_UnitaryEvolution.lean"
            echo -e "${BLUE}Verifying D03: Gauge Structure (U(1)×SU(2)×SU(3))...${NC}"
            ;;
        D04|d04)
            file="003-Lean_Supporting_Data/Core_Backup/D04_BornRule.lean"
            echo -e "${BLUE}Verifying D04: Born Rule (P = |ψ|²)...${NC}"
            ;;
        D05|d05)
            file="003-Lean_Supporting_Data/Core_Backup/D05_StrainWeights.lean"
            echo -e "${BLUE}Verifying D05: Decoherence Scaling (τ_D ∝ ξ²)...${NC}"
            ;;
        *)
            echo -e "${RED}Unknown derivation: $derivation${NC}"
            echo "Valid options: D01, D02, D03, D04, D05"
            exit 1
            ;;
    esac
    
    if [ -f "$file" ]; then
        echo -e "${YELLOW}Running Lean verification...${NC}"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        
        # Run Lean on the file
        if lean "$file" 2>&1 | tee /tmp/lean_output.txt; then
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo -e "${GREEN}✅ Verification PASSED!${NC}"
            
            # Extract and display key theorems
            echo -e "\n${BLUE}Key Theorems Verified:${NC}"
            grep -E "^theorem|^lemma" "$file" | head -5 | while read -r line; do
                echo "  • $line"
            done
        else
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            echo -e "${RED}❌ Verification FAILED${NC}"
            echo "Check the output above for errors."
        fi
    else
        echo -e "${RED}File not found: $file${NC}"
        exit 1
    fi
}

# Function to run all verifications
verify_all() {
    echo -e "${BLUE}Running complete verification suite...${NC}\n"
    
    local all_passed=true
    
    for d in D01 D02 D03 D04 D05; do
        echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
        if verify_derivation $d > /tmp/${d}_output.txt 2>&1; then
            echo -e "${GREEN}✅ $d: PASSED${NC}"
        else
            echo -e "${RED}❌ $d: FAILED${NC}"
            all_passed=false
        fi
    done
    
    echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    
    if [ "$all_passed" = true ]; then
        echo -e "${GREEN}"
        echo "╔══════════════════════════════════════════╗"
        echo "║   ALL DERIVATIONS VERIFIED SUCCESSFULLY   ║"
        echo "╚══════════════════════════════════════════╝"
        echo -e "${NC}"
    else
        echo -e "${RED}Some verifications failed. Check individual outputs.${NC}"
    fi
}

# Main script logic
print_header

if [ $# -eq 0 ]; then
    echo "Usage: ./scripts/verify.sh [OPTION]"
    echo ""
    echo "Options:"
    echo "  D01-D05    Verify specific derivation"
    echo "  all        Verify all derivations"
    echo "  predict    Show experimental predictions"
    echo ""
    echo "Example: ./scripts/verify.sh D02"
    exit 0
fi

case $1 in
    all|ALL)
        verify_all
        ;;
    *)
        verify_derivation $1
        ;;
esac

echo ""
'@ | Out-File -FilePath "scripts/verify.sh" -Encoding UTF8 -NoNewline

Write-Host "✅ scripts/verify.sh created" -ForegroundColor Green

# Summary
Write-Host ""
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Gray
Write-Host "✅ Gitpod integration files created successfully!" -ForegroundColor Green
Write-Host ""
Write-Host "📝 Next steps:" -ForegroundColor Yellow
Write-Host "  1. Review the created files" -ForegroundColor White
Write-Host "  2. Commit to your repository:" -ForegroundColor White
Write-Host ""
Write-Host "     git add .gitpod.yml .gitpod.dockerfile scripts/verify.sh" -ForegroundColor Cyan
Write-Host "     git commit -m 'Add Gitpod integration for zero-install Lean verification'" -ForegroundColor Cyan
Write-Host "     git push" -ForegroundColor Cyan
Write-Host ""
Write-Host "  3. Add this badge to your README.md:" -ForegroundColor White
Write-Host ""
Write-Host "[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/jdlongmire/LFT)" -ForegroundColor Cyan
Write-Host ""
Write-Host "🚀 Your repository will then have one-click Lean verification!" -ForegroundColor Green