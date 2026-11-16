from pathlib import Path
import subprocess

work=Path(__file__).parent
source=(work/'prepare-scalar-depth-and-union.py').read_text()
for old,new in {
 '20261116-current-real-worker-scan-target-scalar-opacity-repair':'20261116-current-real-worker-scan-scalar-root-projection-repair',
 'd9707d0ff7dcf8a6218e82bd865509daa7e61380ca57320db1eb287720398856':'f178ebea61122b099704652b164d0acf843a27ab579fd06a6fdc77f429c609a6',
 '20261116-native-whole-real-scalar-and-union-normal-check':'20261116-native-whole-real-scalar-root-and-union-normal-check',
 'prepare-scalar-depth-core.py':'prepare-scalar-root-depth-core.py',
 'SCALAR-NORMALIZED-FULL-APPEND':'SCALAR-ROOT-NORMALIZED-FULL-APPEND',
 'WholeScalar136Probes':'WholeScalarRoot136Probes',
}.items():
    assert old in source
    source=source.replace(old,new)
helper=work/'prepare-scalar-root-depth-and-union-core.py'
helper.write_text(source)
subprocess.run(['python3',str(helper)],check=True)
