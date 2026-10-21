import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent

def check(base,entry):
    p=base/entry['path'];data=p.read_bytes()
    assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],str(p)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text())
    assert manifest['lean_jobs']==0 and manifest['proof_pairs']==0
    for entry in manifest['files']:check(HERE,entry)
    assert json.loads((HERE/'source-pins.json').read_text())['files']==manifest['sources']
    for entry in manifest['sources']:
        check(HERE/'inputs/root',entry)
        if args.live:check(args.root,entry)
    print(json.dumps({'status':'PASS','local_pins':len(manifest['files']),'root_pins':len(manifest['sources']),'lean_jobs':0,'proof_pairs':0,'live':args.live}))
if __name__=='__main__':main()
