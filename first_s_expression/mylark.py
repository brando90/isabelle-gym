from lark import Lark
import lark

grammar = """
start: term

term: apply
    | const
    | free
    | var
    | bound
    | abs
apply: "(apply " term " " term ")"
const: "(const " MYSTR  ")"
free: "(free " MYSTR ")"
var: "(var " MYSTR ")"
bound: "(bound " MYSTR ")"
abs: "(abs " MYSTR " " term ")"
MYSTR: LETTER (LETTER | "." | "_" | DIGIT)*

%import common.WORD
%import common.DIGIT
%import common.LETTER
%ignore " "
"""
parser = Lark(grammar)
tree1 = parser.parse("(apply (const HOL.Trueprop) (apply (apply (const HOL.implies) (apply (apply (const HOL.conj) (free A)) (free B))) (apply (apply (const HOL.conj) (free B)) (free A))))")
print(parser.parse("(apply (const HOL.Trueprop) (apply (apply (const HOL.implies) (apply (apply (const HOL.conj) (free A)) (free B))) (apply (apply (const HOL.conj) (free B)) (free A))))"))
print(tree1.pretty())

class IncreaseAllNumbers(lark.Transformer):
    def _call_userfunc(self, tree, children):
        #print(tree.data)
        return

    def _call_userfunc_token(self, c):
        print(c)

IncreaseAllNumbers(visit_tokens=True).transform(tree1)
