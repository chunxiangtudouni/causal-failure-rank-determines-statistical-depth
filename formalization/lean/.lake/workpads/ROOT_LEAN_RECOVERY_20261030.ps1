param(
    [Parameter(Mandatory=$true)][string]$Executable,
    [Parameter(Mandatory=$true)][string[]]$Arguments
)

# Crash recovery overlay. The original four-slot gate is preserved byte-for-byte.
# All recovering writers share two outer slots and a 4096 MiB admission floor.
# No running compiler is stopped, restarted, or evicted by this wrapper.
$ErrorActionPreference = 'Stop'
$recoverySlots = @()
$recoveryIndex = -1
$recoveryExit = 1
$recoveryAdmission = $null
$recoveryHeld = $false
try {
    for ($recoveryNumber = 0; $recoveryNumber -lt 2; $recoveryNumber++) {
        $recoverySlots += [System.Threading.Mutex]::new(
            $false, "Local\STOC_Lean_20261030_Recovery_Slot_$recoveryNumber")
    }
    $recoveryAdmission = [System.Threading.Mutex]::new(
        $false, 'Local\STOC_Lean_20261030_Recovery_Admission')
    Write-Output "ROOT_RECOVERY queued ownerPid=$PID"
    try {
        [void]$recoveryAdmission.WaitOne()
        $recoveryHeld = $true
    } catch [System.Threading.AbandonedMutexException] {
        $recoveryHeld = $true
    }
    try {
        try {
            $recoveryIndex = [System.Threading.WaitHandle]::WaitAny(
                [System.Threading.WaitHandle[]]$recoverySlots)
        } catch [System.Threading.AbandonedMutexException] {
            $recoveryIndex = $_.Exception.MutexIndex
        }
        do {
            $recoveryAvailable = (Get-Counter '\Memory\Available MBytes').CounterSamples[0].CookedValue
            if ($recoveryAvailable -lt 4096) {
                Write-Output "ROOT_RECOVERY awaitingMemoryMiB=$recoveryAvailable ownerPid=$PID"
                Start-Sleep -Seconds 5
            }
        } while ($recoveryAvailable -lt 4096)
    } finally {
        $recoveryAdmission.ReleaseMutex()
        $recoveryHeld = $false
    }
    Write-Output "ROOT_RECOVERY acquired=$recoveryIndex availableMiB=$recoveryAvailable ownerPid=$PID"
    & "$PSScriptRoot/ROOT_LEAN_SLOT.ps1" -Executable $Executable -Arguments $Arguments
    $recoveryExit = $LASTEXITCODE
    if ($null -eq $recoveryExit) { $recoveryExit = 0 }
} finally {
    if ($recoveryIndex -ge 0) {
        $recoverySlots[$recoveryIndex].ReleaseMutex()
        Write-Output "ROOT_RECOVERY released=$recoveryIndex ownerPid=$PID"
    }
    foreach ($recoverySlot in $recoverySlots) { $recoverySlot.Dispose() }
    if ($null -ne $recoveryAdmission) {
        if ($recoveryHeld) { $recoveryAdmission.ReleaseMutex() }
        $recoveryAdmission.Dispose()
    }
}
exit $recoveryExit
