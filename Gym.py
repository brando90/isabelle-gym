class Gym:
    def __init__():
        # Somehow initialize it
    def 
class Document:
    environment # List of definitions and theorems in the environment
    def_lem # List of definitions and lemmas in the document.



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
    
    
