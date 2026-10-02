@echo off
REM Sync Lean sources from the (non-ASCII) workspace path to the ASCII build path,
REM then build each module individually (parallel `lake build` trips a Lean file-read bug here).
setlocal
set SRC=D:\ai\大一秋课程\分析1\hw1\lean\AnalysisHW1
set DST=D:\ahw1
set TC=C:\Users\12739\.elan\toolchains\leanprover--lean4---v4.34.0
set LAKE=%TC%\bin\lake.exe

robocopy "%SRC%\AnalysisHW1" "%DST%\AnalysisHW1" *.lean /NJH /NJS /NP /NFL /NDL >nul
robocopy "%SRC%" "%DST%" *.lean *.toml *.md /NJH /NJS /NP /NFL /NDL >nul

cd /d "%DST%"
if "%~1"=="" (
  for %%F in (AnalysisHW1\Problem*.lean) do (
    echo === %%F
    "%LAKE%" build "AnalysisHW1.%%~nF" 2>&1
  )
) else (
  for %%A in (%*) do (
    echo === %%A
    "%LAKE%" build "AnalysisHW1.%%A" 2>&1
  )
)
endlocal
