import json
import os
import subprocess

def run(command, timeout=25):
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        print(json.dumps(dict(command=command, exit_code=result.returncode,
            stdout=result.stdout, stderr=result.stderr)))
    except subprocess.TimeoutExpired as error:
        print(json.dumps(dict(command=command, status='TIMED_OUT',
            stdout=(error.stdout or b'').decode() if isinstance(error.stdout, bytes) else error.stdout,
            stderr=(error.stderr or b'').decode() if isinstance(error.stderr, bytes) else error.stderr)))

config = subprocess.check_output(['ssh', '-G', 'git@github.com'], text=True)
keys = {'hostname', 'port', 'user', 'batchmode', 'controlmaster', 'controlpath',
        'proxycommand', 'proxyjump', 'identitiesonly', 'identityagent'}
print(json.dumps(dict(ssh_config=[line for line in config.splitlines() if line.split()[0] in keys],
    ssh_agent_socket_set=bool(os.environ.get('SSH_AUTH_SOCK')))))
run(['/snap/bin/gh', 'auth', 'status'])
run(['ssh', '-vT', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=10',
    '-o', 'ConnectionAttempts=1', 'git@github.com'])
