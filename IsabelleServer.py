import sarge
# A class that communicates with the Isabelle server.
class IsablleServer:
    def __init__(self, timeout, debug=False):
        self.debug = debug
        self.timeout = timeout
        

# reference : CoqGym/serapi.py
