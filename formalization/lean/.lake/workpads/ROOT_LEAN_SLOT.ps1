param(
    [Parameter(Mandatory=$true)][string]$Executable,
    [Parameter(Mandatory=$true)][string[]]$Arguments
)

# Shared compiler admission only. No source/cache/config mutation and no process termination.
# Named mutexes recover automatically when their owning process exits unexpectedly.
$ErrorActionPreference = 'Stop'
$rootSlotHandles = @()
$rootSlotIndex = -1
$rootSlotExit = 1
$rootAdmission = $null
$rootAdmissionHeld = $false
try {
    for ($rootSlotNumber = 0; $rootSlotNumber -lt 4; $rootSlotNumber++) {
        $rootSlotHandles += [System.Threading.Mutex]::new(
            $false, "Local\STOC_Lean_20261030_Slot_$rootSlotNumber")
    }
    $rootAdmission = [System.Threading.Mutex]::new(
        $false, 'Local\STOC_Lean_20261030_Admission')
    Write-Output "ROOT_LEAN_SLOT queued ownerPid=$PID"
    try {
        [void]$rootAdmission.WaitOne()
        $rootAdmissionHeld = $true
    } catch [System.Threading.AbandonedMutexException] {
        $rootAdmissionHeld = $true
    }
    # One admitted waiter owns the wait for a slot. New arrivals cannot steal
    # a just-released slot from it by repeatedly restarting a short timed wait.
    try {
        Write-Output "ROOT_LEAN_SLOT admission ownerPid=$PID"
        try {
            $rootSlotCandidate = [System.Threading.WaitHandle]::WaitAny(
                [System.Threading.WaitHandle[]]$rootSlotHandles)
            $rootSlotIndex = $rootSlotCandidate
        } catch [System.Threading.AbandonedMutexException] {
            $rootSlotIndex = $_.Exception.MutexIndex
        }
    } finally {
        if ($rootAdmissionHeld) {
            $rootAdmission.ReleaseMutex()
            $rootAdmissionHeld = $false
        }
    }
    Write-Output "ROOT_LEAN_SLOT acquired=$rootSlotIndex ownerPid=$PID"
    & $Executable @Arguments
    $rootSlotExit = $LASTEXITCODE
    if ($null -eq $rootSlotExit) { $rootSlotExit = 0 }
} finally {
    if ($rootSlotIndex -ge 0) {
        $rootSlotHandles[$rootSlotIndex].ReleaseMutex()
        Write-Output "ROOT_LEAN_SLOT released=$rootSlotIndex ownerPid=$PID"
    }
    foreach ($rootSlotHandle in $rootSlotHandles) { $rootSlotHandle.Dispose() }
    if ($null -ne $rootAdmission) {
        if ($rootAdmissionHeld) { $rootAdmission.ReleaseMutex() }
        $rootAdmission.Dispose()
    }
}
exit $rootSlotExit
