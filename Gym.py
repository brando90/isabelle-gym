class Gym:
    def __init__():
        # Somehow initialize it

# use json-RPC to communicate with isabelle server
class IsabelleCommuniation():
    def update_document(self, document):
        # magically update document and get feedback
    def update_caret(self, document,pos):
        # magically update caret and get proofstate

class FileEditor():
    working_file = None # the file the document is managing.
    def addline(self, pos, text):
        self.add(pos, text+"\n")
    def add(pos, text):
        # magically add something to the file at position
    def delete(pos1, pos2):
        # magically delete something from the file at position

class Document:
    theorems = [] # list of theorems
    theorem_dict = {} # maps theorems to position in the document.
    thy_file = None # FileEditor of the document

    def addline_and_proofstate(line):
        thy_file.addline(pos,line)
        return update_document()

    def get_proofstate(theorem):
        return update_caret(theorem_dict[theorem])

    def add_theorem(theorem):
        lines += theorem.lines() # something like that.
        return update_document


class IsabelleDocument:
    # initialize a document for proving
    def __init__(document,timeout)
    # Get a lemma in the document to prove
    def get_lemma(id)
    def new_lemma(id)

class IsabelleLemma:
    # initialize a lemma inside a document to prove, isar is a boolean indicating the proof style
    # returns first node in the proof tree
    def __init__(environment,theorem,timeout,isar)

    ## for apply tactic style:
    proof_tree # Tree of proof
    # apply a tactic to a node in the proof tree (replacing old one)
    # returns new node id
    def apply(tactic, node_id)
    # get proof state of selected node
    def get_state(node_id)
    # use atp (e.g. sledgehammer) on selected node
    def atp(atp_type, node_id)

    ## for isar style: (I'm not sure about how Isar works)
    sentences # list of sentences in the proof
    # add a sentence in the proof 
    def add(sentence)
    # remove a sentence in the proof
    def remove(sentence_id)
    # get proof state at a sentence
    def get_isar_state(sentence_id) 

background_document = IsabelleDocument("something something")

class Goal:
    hypothesis = []
    conclusion = "" # or some AST
    document = IsabelleDocument()
    def __init__(self, hypothesis, conclusion):
        self.hypothesis = hypothesis
        self.conclusion = conclusion
        self.lemma = background_document.new_lemma()
    # apply the tactic to the goal
    def apply(self, tactic): 
        return self.lemma.apply(tactic)


