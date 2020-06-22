import sarge, subprocess
from sarge import Command, Capture
import sys
SERVER_NAME = 'isabelle_gym'

# A class that communicates with the Isabelle server.
class IsablleServer:
    def __init__(self, timeout, debug=False):
        self.debug = debug
        self.timeout = timeout
        # TODO: remember clients so that they get closed when server is closed.
        try:
            self.process = sarge.run('isabelle server -n ' + SERVER_NAME, async_=True, stdout=Capture(buffer_size=1),stderr=Capture(buffer_size=1))
            out = self.process.stdout.expect(r'server .+ \(password .+\)\n')
            if debug:
                print(out, self.process.stderr.read())
        except FileNotFoundError: 
            print('Please make sure the "isabelle" program is in the PATH.')
            raise

    def create_client(self):
        return IsabelleClient(self.timeout,self.debug)

    def close(self):
        sarge.run("isabelle server -x -n " + SERVER_NAME)
        self.process.close()
            
class IsabelleClient:
    def __init__(self, timeout, debug):
        self.debug = debug
        self.timeout = timeout
        self.process = sarge.Command('isabelle client -n ' + SERVER_NAME, stdout=Capture(buffer_size=1),stderr=Capture(buffer_size=1))
        self.process.run(input=subprocess.PIPE, async_=True)
        outs = self.process.stdout.expect(r"OK (.+)\n")
        # outs is a re.Match object
        if outs:
            return outs[0]
        else:
            return self.process.stderr.read()

    def close(self): 
        # TODO: find a way to stop the client
        pass
    # returns result.
    def send(self, message):
        self.process.stdin.write(message)
        self.process.stdin.flush()
        outs = self.process.stdout.expect(r"OK (.+)\n")
        # outs is an re.Match object
        if outs:
            return outs[0]
        else:
            return self.process.stderr.read()

class IsabelleSession:
    def __init__(self, timeout, debug):
        self.debug = debug
        self.timeout = timeout

if __name__ == "__main__":
    test_server = IsablleServer(1000,debug=True)
    test_client = test_server.create_client()

    print(test_client.send(b"echo 42\n"))
    test_server.close()

# reference : CoqGym/serapi.py
