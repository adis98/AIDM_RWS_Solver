<#
Activate minizinc
$env:Path = "C:\Program Files\MiniZinc;" + $env:Path
#>
param($p1, $p2)

$filename = "D:\EARLY_YEARS\Master\TU Delft\Q3\Algorithms for Intelligent Decision Making\Assignment\AIDM_RWS_Solver\data\Example"

$newFilename = $filename + $p2 + ".dzn"

echo "===================================================="
echo Executing $newFilename
echo "===================================================="

minizinc --solver $p1 CSP_solution.mzn $newFilename -f -a --output-time --solver-time-limit 3600000



<#
.\run_mzn.ps1 Gecode 1
.\run_mzn.ps1 Gecode 2
.\run_mzn.ps1 Gecode 3
.\run_mzn.ps1 Gecode 4
.\run_mzn.ps1 Gecode 5
.\run_mzn.ps1 Gecode 6
.\run_mzn.ps1 Gecode 7
.\run_mzn.ps1 Gecode 8
.\run_mzn.ps1 Gecode 9
.\run_mzn.ps1 Gecode 10
.\run_mzn.ps1 Gecode 11
.\run_mzn.ps1 Gecode 12
.\run_mzn.ps1 Gecode 13
.\run_mzn.ps1 Gecode 14
.\run_mzn.ps1 Gecode 15
.\run_mzn.ps1 Gecode 16
.\run_mzn.ps1 Gecode 17
.\run_mzn.ps1 Gecode 18
.\run_mzn.ps1 Gecode 19
.\run_mzn.ps1 Gecode 20
#>