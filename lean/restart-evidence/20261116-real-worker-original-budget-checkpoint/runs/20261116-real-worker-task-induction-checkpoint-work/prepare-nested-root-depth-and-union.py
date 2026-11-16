from pathlib import Path
import subprocess

work=Path(__file__).parent
source=(work/'prepare-scalar-root-depth-and-union-core.py').read_text()
for old,new in {
 '20261116-current-real-worker-scan-scalar-root-projection-repair':'20261116-current-real-worker-scan-nested-root-simp-repair',
 'f178ebea61122b099704652b164d0acf843a27ab579fd06a6fdc77f429c609a6':'462333f58c802b15535b62ec1ff3ba9e0f39b760b20c422b717dea9c31650cab',
 '20261116-native-whole-real-scalar-root-and-union-normal-check':'20261116-native-whole-real-nested-root-and-union-normal-check',
 'prepare-scalar-root-depth-core.py':'prepare-nested-root-depth-core.py',
 'SCALAR-ROOT-NORMALIZED-FULL-APPEND':'NESTED-ROOT-NORMALIZED-FULL-APPEND',
 'WholeScalarRoot136Probes':'WholeNestedRoot136Probes',
}.items():
    assert old in source
    source=source.replace(old,new)
helper=work/'prepare-nested-root-depth-and-union-core.py'
helper.write_text(source)
subprocess.run(['python3',str(helper)],check=True)
