param([string]$Engine = "pdflatex")
$ErrorActionPreference = "Stop"
Push-Location -LiteralPath $PSScriptRoot
try {
    New-Item -ItemType Directory -Force build | Out-Null
    & python checks/prepare_and_audit.py
    if ($LASTEXITCODE -ne 0) { throw "Manuscript transcription audit failed." }
    for ($pass=1; $pass -le 2; $pass++) {
        & $Engine -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=build main.tex |
            Out-File -FilePath "build/compile-pass-$pass.txt" -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw "LaTeX compilation failed; inspect build logs." }
    }
    $buildLog = Get-Content -Raw -LiteralPath build/main.log
    if ($buildLog -match "Overfull \\[hv]box|Missing character:|There were undefined references|Citation .+ undefined") {
        throw "Resolve the layout or reference warning before publishing."
    }
    Copy-Item -LiteralPath build/main.pdf -Destination domino-tilings-en.pdf -Force
    Write-Output "Built domino-tilings-en.pdf. M1-M6 scope documented; external semantic review pending."
}
finally { Pop-Location }
