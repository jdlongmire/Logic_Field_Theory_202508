# Archive Cleanup Script
# Run AFTER the main reorganization to archive remaining old folders
# Run from: C:\Users\jdlon\Documents\LFT_GEN_19_LEAN

Write-Host "=== Archiving Old Structure ===" -ForegroundColor Cyan
Write-Host "Moving remaining old folders to 005-Supporting_Data/Archive/Old_Structure/" -ForegroundColor Yellow

# Create archive destination
$archivePath = "005-Supporting_Data/Archive/Old_Structure"
New-Item -ItemType Directory -Force -Path $archivePath | Out-Null
Write-Host "Created archive folder: $archivePath" -ForegroundColor Green

# List of old directories that might still exist
$oldFolders = @(
    "docs"
    "LFT_GEN_19_LEAN"
    "LFT"
    "planning"
    "src"
    "figures"
    "lean-map"
)

# Move each old folder to archive if it exists
foreach ($folder in $oldFolders) {
    if (Test-Path $folder) {
        # Check if it has content
        $items = Get-ChildItem -Path $folder -Recurse -Force -ErrorAction SilentlyContinue
        if ($items.Count -gt 0) {
            Write-Host "Archiving: $folder ($(($items | Where {$_.PSIsContainer -eq $false}).Count) files)" -ForegroundColor Yellow
            Move-Item -Path $folder -Destination "$archivePath/$folder" -Force
            Write-Host "  ✓ Moved to archive: $folder" -ForegroundColor Green
        } else {
            # Empty folder - just remove
            Remove-Item -Path $folder -Recurse -Force
            Write-Host "  ✓ Removed empty folder: $folder" -ForegroundColor Gray
        }
    }
}

# Also move any other old files in root that shouldn't be there
Write-Host "`nChecking for other files to archive..." -ForegroundColor Yellow

# Files that should stay in root
$keepInRoot = @(
    "README.md"
    "LICENSE"
    ".gitignore"
    "lakefile.toml"
    "lean-toolchain"
    "simple_reorg.ps1"
    "archive_cleanup.ps1"
    "test_reorg.ps1"
    "reorganize_lft.ps1"
    "reorganize_lft_fixed.ps1"
)

# Get all files in root
$rootFiles = Get-ChildItem -File -Path "." | Where-Object {
    $_.Name -notin $keepInRoot -and 
    -not $_.Name.StartsWith(".") -and  # Keep hidden files
    $_.Extension -ne ".zip"  # Keep backup zips
}

if ($rootFiles.Count -gt 0) {
    $miscArchive = "$archivePath/misc_root_files"
    New-Item -ItemType Directory -Force -Path $miscArchive | Out-Null
    
    foreach ($file in $rootFiles) {
        Write-Host "  Archiving root file: $($file.Name)" -ForegroundColor Yellow
        Move-Item -Path $file.FullName -Destination "$miscArchive/" -Force
    }
    Write-Host "  ✓ Moved $($rootFiles.Count) miscellaneous files to archive" -ForegroundColor Green
}

# Create archive README
$dateArchived = Get-Date -Format "yyyy-MM-dd HH:mm"
$archiveReadme = @"
# Archived Old Structure

This folder contains the original repository structure before reorganization.
Date archived: $dateArchived

## Contents

- docs/ - Original documentation structure
- LFT_GEN_19_LEAN/ - Original Lean structure  
- LFT/ - Original LFT folder
- planning/ - Original planning documents
- src/ - Original source files
- figures/ - Original figures
- lean-map/ - Original Lean mapping
- misc_root_files/ - Other files from root

## Note

These files are preserved for reference. The active content is now in the numbered folder structure (001-005).
"@

$archiveReadme | Out-File -FilePath "$archivePath/README.md" -Encoding UTF8

# Summary
Write-Host "`n=== Archive Summary ===" -ForegroundColor Green
$archivedItems = Get-ChildItem -Path $archivePath -Recurse -File
Write-Host "Total files archived: $($archivedItems.Count)" -ForegroundColor Cyan
Write-Host "Archive location: $archivePath" -ForegroundColor Cyan

# Show new clean root
Write-Host "`n=== Clean Repository Root ===" -ForegroundColor Green
Write-Host "Remaining in root:" -ForegroundColor Yellow
Get-ChildItem -Path "." | Where-Object { 
    $_.Name -notlike ".*" -and 
    $_.Name -ne ".git" -and
    $_.Name -ne ".lake"
} | ForEach-Object {
    if ($_.PSIsContainer) {
        Write-Host "  📁 $($_.Name)" -ForegroundColor Cyan
    } else {
        Write-Host "  📄 $($_.Name)" -ForegroundColor White
    }
}

Write-Host "`n✅ Archive cleanup complete!" -ForegroundColor Green
Write-Host "Old structure preserved in: 005-Supporting_Data/Archive/Old_Structure/" -ForegroundColor Yellow