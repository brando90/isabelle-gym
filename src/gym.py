import document
from document import Document

import console
from console import IsabelleConsole

class Gym:
    def __init__(self, debug = False):
        self.console = IsabelleConsole()   # console
        self.document = Document(filename = 'thy')    # .thy proof document
        self.goals = []

        # add default theory _ and import Main statements
        self.add_line('theory ' + self.document.prefix + self.document.filename)
        self.add_line('imports Main')
        self.add_line('begin')
    
    # simply add a new line to .thy document
    def add_line(self, line): 
        self.document.add_line(line)

    # get all lines in .thy document
    def get_lines(self): 
        return self.document.get_lines()

    # remove a line in .thy document
    def backtrack(self): 
        self.document.remove_last_line()
        
    # add a new line to .thy document, compile it through console, option to print raw output or goals
    def process_line(self, line, print_console = False, print_goals = False): 
        self.add_line(line)
        self.result = self.process_document(print_console, print_goals)
    
    # compile the current .thy document as is through console, option to print raw output or goals
    def process_document(self, print_console = False, print_goals = False):
        self.add_line("print_state") 
        self.add_line("done") 
        self.add_line("end") 

        self.console.use_thy(self.document.get_name())
        self.goals = self.console.goals

        self.document.remove_last_line()
        self.document.remove_last_line()
        self.document.remove_last_line()

        if print_console: print(self.console.lines)
        if print_goals: print(self.console.goals)