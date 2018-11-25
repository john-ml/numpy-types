import ast

# -------------------- pretty printer for AST objects --------------------

# convert ast object into tree of dicts and lists
def explode(a):
    if type(a) is list:
        return list(map(explode, a))

    if not hasattr(a, '_fields'):
        return a
    
    fields = {}
    for k in a._fields:
        fields[k] = explode(a.__getattribute__(k))

    return type(a), fields

# exploded tree -> string
def pretty(exploded, indent='  ', lines=False):
    def pretty_(exploded):
        if type(exploded) is list:
            t = [b for a in exploded for b in pretty_(a)]
            if len(t) <= 1:
                return ['[' + ''.join(t) + ']']
            return ['['] + [indent + a for a in t] + [']']

        if type(exploded) is not tuple:
            return [str(exploded)]

        node, children = exploded
        subs = []
        for k, v in children.items():
            t = pretty_(v)
            h, t = t[0], t[1:]
            name = '.' + k + ' = '
            subs.append(name + h)
            subs.extend(' ' * len(name) + a for a in t)

        if len(subs) == 1:
            return [node.__name__ + subs[0]]

        return [node.__name__] + [indent + a for a in subs]

    return '\n'.join(pretty_(exploded)) if not lines else pretty_(exploded)

# visualize a parse tree
def pretty_parse(s):
    return pretty(explode(ast.parse(s)))

# -------------------- pattern-matching against ast --------------------

# check if ast matches pattern (which is also an ast)
# variables (capture groups) are prefixed by underscores
# variables that capture statement lists of prefixed by double underscores
# return Optional[Dict[var, ast]]
def matches(pattern, query):

    # put captured entries in b into a, or throw if encounter duplicate capture group name
    def merge(a, b):
        for k, v in b.items():
            if k in a:
                raise ValueError('Duplicate capture group name: {}'.format(k))
            a[k] = v

    if type(pattern) is ast.Name and pattern.id.startswith('_'):
        return { pattern.id[1:]: query }

    if type(pattern) is ast.Name and '__' in pattern.id and \
       type(query).__name__ == pattern.id[pattern.id.index('__')+2:]:
        return { pattern.id[:pattern.id.index('__')]: query }

    if type(pattern) is not type(query):
        return None

    # ignore .context (don't care whether is Load or Store)
    if type(pattern) is ast.Name:
        return {} if pattern.id == query.id else None
   
    # capture multiple subscripts in 1 variable
    if type(pattern) is type(query) is ast.Index and \
       type(pattern.value) is ast.Name and \
       pattern.value.id.startswith('__'):
        return { pattern.value.id[2:]: query.value }

    if type(pattern) is list:
        if len(pattern) == 1 \
           and type(pattern[0]) is ast.Expr \
           and type(pattern[0].value) is ast.Name \
           and pattern[0].value.id.startswith('__'):
            return { pattern[0].value.id[2:]: query } 
        if len(pattern) == 1 \
           and type(pattern[0]) is ast.arg \
           and pattern[0].arg.startswith('__'):
            return { pattern[0].arg[2:]: query } 
        if len(pattern) != len(query):
            return None
        captures = {}
        for a, b in zip(pattern, query):
            c = matches(a, b)
            if c is None:
                return None
            merge(captures, c)
        return captures

    if not hasattr(pattern, '_fields'):
        return {} if not hasattr(query, '_fields') and pattern == query else None

    if pattern._fields != query._fields:
        return None

    captures = {}
    for k in pattern._fields:
        v = pattern.__getattribute__(k)
        v1 = query.__getattribute__(k)
        # capture function definition name or argument name
        if type(pattern) is ast.FunctionDef and k == 'name' and pattern.name.startswith('_') or \
           type(pattern) is ast.arg and k == 'arg' and pattern.arg.startswith('_'):
            v = ast.parse(v).body[0].value
        c = matches(v, v1)
        if c is None:
            return None
        merge(captures, c)

    return captures

# extract from code snippet the part of the ast necessary to make a pattern
# i.e. remove Module node + the Expr node if the pattern is an expression and not a statement
# and treat a : t as argument annotation, not as an assignment statement
def make_pattern(s):
    tree = ast.parse(s).body[0]
    if type(tree) is ast.Expr:
        return tree.value
    if type(tree) is ast.AnnAssign:
        return matches(
            raw_pattern('def f(__a):\n pass'),
            ast.parse('def f({}):\n pass'.format(s)))['a'][0]
    return tree

# treat code snippet as raw pattern (i.e. don't remove unnecessary Module/Expr nodes)
def raw_pattern(s):
    return ast.parse(s)
 
# pretty-print matches
def pretty_matches(matches):
    if matches is None:
        return str(None)
    captures = (k + ' ->\n' + '\n'.join('    ' + a for a in pretty(explode(v), lines=True)) \
        for k, v in matches.items())
    return '{ ' + '\n, '.join(captures) + '\n}'

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    print(pretty_parse('def f(a : int) -> bool:\n    return a == 0'))
    print(pretty_parse('a * b'))
    print(pretty_parse('a = b'))
    print(ast.dump(ast.parse('_a * _b')) == ast.dump(ast.parse('_a *    _b')))
    print(pretty_matches(matches(ast.parse('_a = _b'), ast.parse('n = n + 1'))))
    n_plus_one = matches(ast.parse('_a = _b'), ast.parse('n = n + 1'))['b']
    print(pretty_matches(matches(ast.parse('_a + _b').body[0].value, n_plus_one)))
    print(make_pattern('_a = _b'))
    print(make_pattern('_a * _b'))
    print(pretty_matches(matches(make_pattern('return _a'), ast.parse('return 3.0').body[0])))
    print(pretty_parse('a : b = 3'))
    print(pretty_parse('if a:\n    pass\nelif b:\n    pass\nelse:\n    pass'))
    d = {}
    d[n_plus_one] = 0
    print(n_plus_one, hash(n_plus_one), d[n_plus_one])

    n = matches(ast.parse('_a'), ast.parse('n'))
    print(pretty(explode(n['a'])))
    print(n)

    print(pretty_matches(matches(
        ast.parse('def f(a : int) -> bool:\n    __a'),
        ast.parse('def f(a : int) -> bool:\n    a = a + 1\n    return a'))))

    print(pretty_parse('def f(a : int, b : bool) -> bool:\n    pass'))
    print(pretty_parse('def f(__a) -> bool:\n    pass'))
    print(pretty_matches(matches(
        raw_pattern('__everything'),
        ast.parse('def f(a : int, b : bool) -> bool:\n    pass'))))
    print(pretty_parse('# hello'))
    print(pretty_matches(matches(
        ast.parse('a__Num'),
        ast.parse('3'))))
    print(pretty_parse('a[1,2,3]'))
    print(pretty_parse('a[__b]'))
    print(pretty_matches(matches(
        ast.parse('_a[__b]'),
        ast.parse('arr[1, 2, 3, 4, n + 1]'))))
    print(pretty_matches(matches(
        make_pattern('def _f(__args) -> _return_type:\n    __body'),
        ast.parse('def f(a : int, b : array[a]) -> array[a + 1]:\n    return test').body[0])))
    print(make_pattern('_a : _t'))
    print(type(make_pattern('_a : _t')) is ast.arg)
