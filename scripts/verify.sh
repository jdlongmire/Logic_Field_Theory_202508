#!/bin/bash
# scripts/verify.sh
# Interactive verification script for LFT derivations

echo "========================================="
echo "  Logic Field Theory Verification Tool"
echo "========================================="
echo ""

cd LFT_003_Lean_Proofs

PS3="Select a derivation to verify (or 6 to verify all): "
options=("D01 - Admissibility" "D02 - Complex Necessity" "D03 - Unitary Evolution" "D04 - Born Rule" "D05 - Strain Weights" "Verify All" "Quit")

select opt in "${options[@]}"
do
    case $opt in
        "D01 - Admissibility")
            echo "Verifying D01 - Admissibility..."
            lake build Core.D01_Admissibility
            echo "✅ D01 verification complete!"
            ;;
        "D02 - Complex Necessity")
            echo "Verifying D02 - Complex Necessity..."
            lake build Core.D02_ComplexNecessity
            echo "✅ D02 verification complete!"
            ;;
        "D03 - Unitary Evolution")
            echo "Verifying D03 - Unitary Evolution..."
            lake build Core.D03_UnitaryEvolution
            echo "✅ D03 verification complete!"
            ;;
        "D04 - Born Rule")
            echo "Verifying D04 - Born Rule..."
            lake build Core.D04_BornRule
            echo "✅ D04 verification complete!"
            ;;
        "D05 - Strain Weights")
            echo "Verifying D05 - Strain Weights..."
            lake build Core.D05_StrainWeights
            echo "✅ D05 verification complete!"
            ;;
        "Verify All")
            echo "Verifying all derivations..."
            lake build
            echo "✅ All derivations verified successfully!"
            ;;
        "Quit")
            break
            ;;
        *) echo "Invalid option $REPLY";;
    esac
done