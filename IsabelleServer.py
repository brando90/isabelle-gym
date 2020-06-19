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

    def close(self): 
        #TODO: find a way to stop the client
        pass
    # returns result.
    def send(self, message):
        self.process.stdin.write(message)
        self.process.stdin.flush()
        return self.process.stdout.read(), self.process.stderr.read()

class IsabelleSession:
    def __init__(self, timeout, debug):
        self.debug = debug
        self.timeout = timeout

# reference : CoqGym/serapi.py
