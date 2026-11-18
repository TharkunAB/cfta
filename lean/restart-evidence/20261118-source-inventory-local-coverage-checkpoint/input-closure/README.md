The checkpoint verifier checks the archived bytes without restored run directories.
The additional input-closure checker verifies the actual input recovery map.
Run that checker at the checked Source tree after restoring the original input paths.
Each archived-inputs.json record gives the original path, payload path and compression flag.
The checker rehashes all selected payloads that recover the five input maps.
It links 49 prior archives and gives no extra theorem credit.
