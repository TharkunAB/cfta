from pathlib import Path
import subprocess

work=Path(__file__).parent
source=(work/'prepare-union-normal-incoming.py').read_text()
for old,new in {
    '20261116-current-shared-incoming-union-normal-endpoint-draft':'20261116-current-shared-incoming-union-normal-skipped-gate-repair',
    '20261116-native-shared-incoming-union-normal-check':'20261116-native-shared-incoming-union-normal-repaired-check',
    '2514b77818f8596aa5df6fe86d040ea7fd4f2105e2ff128249a72a671b956291':'646671cf186b2607543e1b28126b5ed612af9337d1584ce542c5e6b29d02aa6c',
}.items():
    assert old in source
    source=source.replace(old,new)
marker="(run/'check.py').write_text(driver)"
assert source.count(marker)==1
source=source.replace(marker,"driver=driver.replace(\"+\"+repr(\"\\\\n\"), \"+\"+repr(\"\\n\"))\n"+marker)
helper=work/'prepare-union-normal-repaired-core.py'
helper.write_text(source)
subprocess.run(['python3',str(helper)],check=True)
