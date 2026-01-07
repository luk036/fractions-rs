# Simple verification script for benchmarks
Write-Host "Checking if benchmarks compile..."
cargo check --bench fraction_benchmarks 2>&1 | Out-File -FilePath bench_check.log
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ Benchmarks compile successfully!"
    Write-Host "You can now run 'cargo bench' to execute the benchmarks."
} else {
    Write-Host "✗ Benchmarks have compilation errors. Check bench_check.log for details."
}