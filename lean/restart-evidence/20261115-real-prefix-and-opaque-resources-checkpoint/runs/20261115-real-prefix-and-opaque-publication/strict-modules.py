import os,subprocess
commands = [['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-R', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261115-real-prefix-and-opaque-publication/source', '-o', '/tmp/mcfta-real-prefix-publication-6wh1fyie/Owner.olean', '/home/tritlo/Code/mcfta/lean/restart-evidence/20261115-real-prefix-and-opaque-publication/source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'], ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', '/tmp/mcfta-real-prefix-publication-6wh1fyie/Real.olean', '/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationObservedRealPrefixResources.lean']]
for command in commands:
    subprocess.run(command,check=True)
