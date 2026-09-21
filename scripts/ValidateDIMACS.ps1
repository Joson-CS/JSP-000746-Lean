param(
    [string]$Path = (Join-Path (Split-Path -Parent $PSScriptRoot) 'certificates\core.cnf')
)

$ErrorActionPreference = 'Stop'
$resolvedPath = (Resolve-Path -LiteralPath $Path).Path
$lines = @(Get-Content -LiteralPath $resolvedPath)

if ($lines.Count -lt 1) {
    throw 'DIMACS file is empty.'
}
if ($lines[0] -cne 'p cnf 153 888') {
    throw "Unexpected DIMACS header: '$($lines[0])'"
}

$headerMatch = [regex]::Match($lines[0], '^p cnf ([1-9][0-9]*) ([1-9][0-9]*)$')
if (-not $headerMatch.Success) {
    throw 'Malformed DIMACS header.'
}
$declaredVariables = [int]$headerMatch.Groups[1].Value
$declaredClauses = [int]$headerMatch.Groups[2].Value
$clauseLines = @($lines | Select-Object -Skip 1)
if ($clauseLines.Count -ne $declaredClauses) {
    throw "Clause count mismatch: parsed $($clauseLines.Count), declared $declaredClauses."
}

$seenVariables = [System.Collections.Generic.HashSet[int]]::new()
for ($clauseNumber = 1; $clauseNumber -le $clauseLines.Count; $clauseNumber++) {
    $tokens = @($clauseLines[$clauseNumber - 1].Split(
        [char[]]@(' ', "`t"), [System.StringSplitOptions]::RemoveEmptyEntries))
    if ($tokens.Count -lt 2) {
        throw "Clause $clauseNumber is empty or lacks its terminator."
    }

    $integers = @($tokens | ForEach-Object { [int]::Parse($_) })
    if ($integers[-1] -ne 0) {
        throw "Clause $clauseNumber does not end in 0."
    }
    $literals = @($integers | Select-Object -First ($integers.Count - 1))
    if ($literals.Count -eq 0) {
        throw "Clause $clauseNumber is an unexpected empty clause."
    }
    if ($literals.Count -ne 3) {
        throw "Clause $clauseNumber has $($literals.Count) literals instead of 3."
    }
    if ($clauseNumber -le 816 -and @($literals | Where-Object { $_ -ge 0 }).Count -ne 0) {
        throw "Triangle-free clause $clauseNumber contains a nonnegative literal."
    }
    if ($clauseNumber -gt 816 -and @($literals | Where-Object { $_ -le 0 }).Count -ne 0) {
        throw "Additive clause $clauseNumber contains a nonpositive literal."
    }

    $seenLiterals = [System.Collections.Generic.HashSet[int]]::new()
    foreach ($literal in $literals) {
        if ($literal -eq 0) {
            throw "Clause $clauseNumber contains variable 0 as a literal."
        }
        $variable = [Math]::Abs($literal)
        if ($variable -gt $declaredVariables) {
            throw "Clause $clauseNumber contains out-of-range variable $variable."
        }
        if (-not $seenLiterals.Add($literal)) {
            throw "Clause $clauseNumber contains duplicate literal $literal."
        }
        if ($seenLiterals.Contains(-$literal)) {
            throw "Clause $clauseNumber is tautological at variable $variable."
        }
        [void]$seenVariables.Add($variable)
    }
}

if ($seenVariables.Count -ne $declaredVariables) {
    throw "Only $($seenVariables.Count) of $declaredVariables variables occur."
}
foreach ($variable in 1..$declaredVariables) {
    if (-not $seenVariables.Contains($variable)) {
        throw "Declared variable $variable never occurs."
    }
}

$hash = (Get-FileHash -LiteralPath $resolvedPath -Algorithm SHA256).Hash.ToLowerInvariant()
[pscustomobject]@{
    Path = $resolvedPath
    Header = $lines[0]
    VariablesDeclared = $declaredVariables
    VariablesObserved = $seenVariables.Count
    ClausesDeclared = $declaredClauses
    ClausesParsed = $clauseLines.Count
    EveryClauseTerminated = $true
    NoVariableZero = $true
    VariablesInRange = $true
    NoEmptyClause = $true
    EveryClauseHasThreeLiterals = $true
    TriangleThenAdditiveSigns = $true
    NoDuplicateLiteral = $true
    NoTautologicalClause = $true
    SHA256 = $hash
}
