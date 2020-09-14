import subprocess
from subprocess import PIPE

import sarge
from sarge import Command, Capture, Feeder, run

import threading
import sys

class IsabelleConsole:
    def __init__(self, debug = False):
        self.debug = debug
        self.lines = []
        self.goals = []
        self.sexps = []

        try:
            self.process = Command('isabelle console -o quick_and_dirty', stdout=Capture(buffer_size=1), stderr=Capture(buffer_size=1))
            self.process.run(input = PIPE, async_=True)
            out = self.process.stdout.expect("Poly/ML> ", timeout = 10)
            if out:
                print("ok")
            else:
                print("not ok")
        except FileNotFoundError:
            print('Please make sure the "isabelle" program is in the PATH.')
            raise

    #<- Basic Operations ->#
    def send(self, message):
        self.process.stdin.write(str.encode(message) + b'\n')
        self.process.stdin.flush()

    def read(self, update_goals = True, update_sexps = True):
        self.lines.clear()
        s = self.process.stdout.readline().decode('utf-8')
        while s != "Poly/ML> ":
            if s:
                if s == "val it = (): unit":
                    break
                self.lines.append(s.strip())
            s = self.process.stdout.readline().decode('utf-8')
        
        if update_goals:
            self.goals = self.extract_goals(self.lines)
        
        if update_sexps:
            self.sexps = self.extract_sexps(self.lines)

    def close(self):
        self.process.kill()

    #<- Proxy Commands ->#
    def use_thy(self, theory): # use thory name as input (aka without suffix)
        self.send('use_thy \"' + theory + '\";')
        self.read(update_goals=True)

    def use(self, ml_file): # use thory name as input (aka without suffix)
        self.send('use \"' + ml_file + '\";')
        self.read(update_goals=False)

    #<- Helper Functions->#
    def extract_goals(self, console_output):
        goals = []
        is_reading_goal = False

        for each in self.lines:
            if len(each) >= 3 and each[0:3] == '###':
                is_reading_goal = False
            if len(each) >= 3 and each[0:3] == '***':
                is_reading_goal = False
            if is_reading_goal:
                goals.append(each)
            if len(each) >= 4 and each[0:4] == 'goal':
                is_reading_goal = True
        return goals
    
    def extract_sexps(self, console_output):
        sexps = []
        sexps_str = ""
        reading_sexps = False

        for each in self.lines:
            if each and reading_sexps:
                if each != 'string list':
                    sexps_str += each
                else:
                    reading_sexps = False
                    break
            if each == 'val it =':
                reading_sexps = True
    
        sexps = eval(sexps_str[:-1])
        return sexps


    # Query isar ast of the given isar command.
    def get_isar_ast(self, line):
        return line # for now. TODO: Actually query the ast.