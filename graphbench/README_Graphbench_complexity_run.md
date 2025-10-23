.\\Graphbench\_complexity\_run.ps1 `

&nbsp; -Root "C:\\development\\art\_pv\_np" `

&nbsp; -OutDir "C:\\development\\art\_pv\_np\\bench\\sweep" `

&nbsp; -PythonExe "python" `

&nbsp; -D 128 -Kproj 32 `

&nbsp; -TimeoutSec 450






Get-ChildItem "$OutDir\\logs" |

&nbsp; Sort-Object LastWriteTime -Descending |

&nbsp; Select-Object -First 1 |

&nbsp; ForEach-Object { Write-Host "`n--- LOG: $($\_.Name) ---`n"; Get-Content -Raw $\_.FullName }



