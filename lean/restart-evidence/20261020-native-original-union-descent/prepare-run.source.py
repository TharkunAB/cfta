import runpy,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
runpy.run_path(str(HERE/'prepare-metadata.py'))
runpy.run_path(str(HERE/'write-current-documents.py'))
