# Multi-connection ranged download (bypasses per-connection VPN throttling).
# Usage: ParallelDownload.ps1 -Url <url> -Out <file> [-Chunks 16] [-ChunkTimeoutSec 1800]
param(
  [Parameter(Mandatory=$true)][string]$Url,
  [Parameter(Mandatory=$true)][string]$Out,
  [int]$Chunks = 16,
  [int]$ChunkTimeoutSec = 1800
)
$ErrorActionPreference = 'Stop'

$head = (& curl.exe -sIL --ssl-no-revoke --max-time 60 $Url 2>$null) -join "`n"
$len = $null
foreach ($line in ($head -split "`n")) {
  if ($line -match '^\s*[Cc]ontent-[Ll]ength:\s*(\d+)') { $len = [int64]$Matches[1] }
}
if (-not $len -or $len -le 0) { throw "Cannot determine Content-Length for $Url" }
Write-Host ("total {0:N1} MB in {1} chunks" -f ($len/1MB), $Chunks)

$dir = Join-Path ([System.IO.Path]::GetDirectoryName($Out)) ("parts_" + [System.IO.Path]::GetFileName($Out))
Remove-Item $dir -Recurse -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory -Force -Path $dir | Out-Null

$per = [int64][math]::Ceiling($len / $Chunks)
$t0 = Get-Date
$jobs = @()
for ($i = 0; $i -lt $Chunks; $i++) {
  $from = $i * $per
  if ($from -ge $len) { continue }
  $to = [math]::Min($from + $per - 1, $len - 1)
  $jobs += Start-Job -ScriptBlock {
    param($url, $from, $to, $file, $to_s)
    & curl.exe -sL --ssl-no-revoke --retry 20 --retry-delay 3 --retry-all-errors --max-time $to_s -r "$from-$to" -o $file $url 2>$null
    exit $LASTEXITCODE
  } -ArgumentList $Url, $from, $to, (Join-Path $dir "p$i.bin"), $ChunkTimeoutSec
}
$jobs | Wait-Job | Out-Null
$jobs | Remove-Job

$files = Get-ChildItem $dir -Filter 'p*.bin' | Sort-Object { [int]($_.BaseName.Substring(1)) }
$got = ($files | Measure-Object Length -Sum).Sum
$dt = ((Get-Date) - $t0).TotalSeconds
Write-Host ("downloaded {0:N1} MB in {1:N1}s = {2:N2} MB/s" -f ($got/1MB), $dt, ($got/1MB/$dt))

if ($got -ne $len) {
  Write-Warning ("length mismatch: expected $len, got $got ({0} parts)" -f $files.Count)
}

$outStream = [System.IO.File]::Create($Out)
try {
  foreach ($f in $files) {
    $s = [System.IO.File]::OpenRead($f.FullName)
    try { $s.CopyTo($outStream) } finally { $s.Dispose() }
  }
} finally { $outStream.Dispose() }
Write-Host ("wrote {0} ({1:N1} MB)" -f $Out, ((Get-Item $Out).Length/1MB))
