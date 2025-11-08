#!/bin/bash
#SBATCH -p primary
#SBATCH --mem=32G
#SBATCH -n 1
#SBATCH --cpus-per-task=1
#SBATCH --time=12:00:00
#SBATCH --mail-type=all
#SBATCH --mail-user=pstanica@nps.edu
#SBATCH -J APN_Search
#SBATCH -o apn_search_%j.out
#SBATCH -e apn_search_%j.err

echo "Job started: $(date)"
echo "Job ID: $SLURM_JOB_ID"
echo "Node: $SLURMD_NODENAME"
echo "CPUs: $SLURM_CPUS_PER_TASK"
echo "Memory: 32GB"

# Check if sage is available first
if command -v sage &> /dev/null; then
    echo "Sage found in PATH - no module load needed"
else
    # Try to load module if sage not in PATH
    if command -v module &> /dev/null; then
        echo "Trying to load sage module..."
        module load sagemath 2>/dev/null || module load sage 2>/dev/null || echo "No sage module found"
    fi
    
    # Check again
    if ! command -v sage &> /dev/null; then
        echo "ERROR: sage command not found!"
        exit 1
    fi
fi

echo "Sage version:"
sage --version

# Check if script exists
if [ ! -f "apn_search_HPC.py" ]; then
    echo "ERROR: apn_search_HPC.py not found!"
    exit 1
fi

echo "Starting APN hexanomial search..."

# Run the search
time sage apn_search_HPC.py

EXIT_CODE=$?

echo "Job finished: $(date)"
echo "Exit code: $EXIT_CODE"

if [ $EXIT_CODE -eq 0 ]; then
    echo "SUCCESS - Output files:"
    ls -lh apn_*.txt
else
    echo "FAILED with exit code: $EXIT_CODE"
fi

exit $EXIT_CODE
