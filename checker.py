import pattern as P
import state as S

# pattern + action
# names of arguments to action should match names of capture groups in pattern
class Rule:
    def __init__(self, pattern, action):
        self.pattern = pattern
        self.f = action
    def apply(self, checker, ast):
        matches = P.matches(self.pattern, ast)
        if matches is None:
            raise ValueError('Pattern match failed:\n{}\n=?=\n{}'.format(
                P.pretty(P.explode(self.pattern)),
                P.pretty(P.explode(ast))))
        return self.f(checker, **matches)

class Checker:
    def __init__(self, rules):
        self.state = State()
        self.rules = rules

    def push(self):
        self.state.push()

    def pop(self):
        self.state.pop()

    def undo(self):
        self.state.undo()

    def check(self, ast):
        for rule in self.rules:
            try:
                self.push()
                result = rule.apply(ast, self)
                self.pop()
                return result
            except ValueError:
                self.undo()
